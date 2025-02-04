open Ast
open Ppx_yojson_conv_lib.Yojson_conv.Primitives

type estado = int [@@deriving yojson]

type simbolo = char option [@@deriving yojson]

type transicao = (estado * simbolo) * estado [@@deriving yojson]

type transicao_gnfa = (estado * re) * estado 

type gnfa =
  estado list * char list * transicao_gnfa list * estado list * estado list

(* o nosso nfa *)
type nfa =
  estado list * char list * transicao list * estado list * estado list
[@@deriving yojson]

let rec read_multiplelines () =
  try
    let line = read_line () in
    line ^ " " ^ read_multiplelines ()
  with End_of_file -> ""

let nfa_of_string s = s |> Yojson.Safe.from_string |> nfa_of_yojson


(* deve efetuar as definições das funções ou submódulos aqui ... *)
let rec show_re = function
| Vazio -> "_"
| Caracter c -> String.make 1 c
| Concatenacao (Vazio, Concatenacao(Escolha(a,b),Vazio)) -> show_re a ^ "|" ^ show_re b  
| Concatenacao (Escolha (a,b), Escolha(c,d)) ->  "(" ^ show_re a ^ "|" ^ show_re b ^ ")(" ^ show_re c ^ "|" ^ show_re d ^")"
| Concatenacao (Escolha (a,b), c) -> "(" ^ show_re a ^ "|" ^ show_re b ^ ")" ^ show_re c
| Concatenacao (a, Escolha (b,c)) ->  show_re a ^ "" ^ "(" ^ show_re b ^ "|" ^ show_re c ^ ")"
| Concatenacao (a, b) -> show_re a ^ "" ^ show_re b
| Escolha (a, b) -> show_re a ^ "|" ^ show_re b 
| Estrela (Concatenacao (Escolha(a,b),c)) -> "((" ^ show_re a ^ "|" ^ show_re b ^ ")" ^show_re c^")*"
| Estrela (Concatenacao (c,Escolha(a,b))) -> "(" ^show_re c^"(" ^ show_re a ^ "|" ^ show_re b ^ "))*"
| Estrela (Concatenacao (a,b)) -> "(" ^ show_re a ^ "" ^ show_re b ^ ")*"
| Estrela (Escolha (a,b)) -> "(" ^ show_re a ^ "|" ^ show_re b ^ ")*"
| Estrela a -> show_re a ^ "*"



let rec create_start_trans si is =
  match si with
  | x::y -> [(is,None),x] @ create_start_trans y is
  | _ -> []

let rec create_final_trans sl fs =
  match sl with
  | x::y -> [(x,None),fs] @ create_final_trans y fs
  | _ -> []
  

let add_state_nfa nfa =
  let (s, c1, t, i, f) = nfa in
  ([0]@s@[((List.length s)+1)],c1,(create_start_trans i 0) @ t @ (create_final_trans f ((List.length s)+1) ),[0],[((List.length s)+1)])

let rec same_trans tl tlaux =
  match tl with
  | ((si,r),sf)::y -> if ((List.length (List.filter (fun ((ssi,rr),ssf) -> si == ssi && sf == ssf && r != rr) (y@tlaux))) != 0) then [((si,r),sf)] @ (same_trans y (((si,r),sf)::tlaux)) else same_trans y tlaux
  | _ -> []

let rec regex_list_to_escola rl =
  match rl with
  | [x] -> x
  | x::y -> Escolha(x,regex_list_to_escola y)
  | _ -> Vazio

let rec create_regex tl = 
  match tl with
  | ((si,r),sf)::y -> 
    let exist = List.filter (fun ((ssi,_),ssf) -> si == ssi && sf == ssf) y in
    let exist_regex = regex_list_to_escola (List.map (fun ((_,rr),_) -> rr) exist) in
    if (List.length exist <> 0) then ([((si,(Escolha (r,exist_regex))),sf)] @ create_regex y) else create_regex y
  | _ -> []

let rec remove_same_states tl =
  match tl with
  | x::y -> if (List.mem x y) then remove_same_states y else [x] @ remove_same_states y
  | _ -> []

let create_gnfa (s,c,t,i,f) : gnfa = 
  let tra_gnfa = List.map (fun ((s1,element),s2) -> 
    let regex = match element with
    | Some c -> Caracter c
    | None -> Vazio in
    ((s1,regex),s2)) t in
  let tra_gnfa = remove_same_states tra_gnfa in
  let trans_remove = same_trans tra_gnfa [] in

  let tra_gnfa = List.filter (fun ((si,_),sf) -> List.length (List.filter (fun ((ssi,_),ssf) -> si == ssi && sf == ssf) trans_remove) == 0) tra_gnfa in
  let tra_gnfa = tra_gnfa @ (create_regex trans_remove) in
  (s,c,tra_gnfa,i,f)

let rec current_state sl i f =
  match (List.rev (List.sort compare sl)) with
  | x::y -> if (List.mem x i || List.mem x f) then current_state y i f else x
  | _ -> -1
  
  let rec trans_to_state tl s=
  match tl with
  | x::y ->
    let (s1,_),s2 = x in
    let l1,l2,l3 = trans_to_state y s in
    if s2 == s && s1 == s then (l1,[x] @ l2,l3)
    else if s1 == s then ([x] @ l1,l2,l3)
    else if s2 == s then (l1,l2,[x] @ l3)
    else  (l1,l2,l3)
  | _ -> ([],[],[])

let rec state_to_state_to_regex trans =
  match trans with
  | [((_,r),_)] -> Estrela r
  | ((_,r),_)::y -> Concatenacao(Estrela r,state_to_state_to_regex y)
  | _ -> Vazio

let rec ghfhf l e =
  let ((ssi,_),ssf) = e in
  match l with
  | ((si,_),sf)::y -> if (si == ssi && sf == ssf) then true else ghfhf y e
  | _ -> false

let rec resolve_gnfa gnfa : gnfa =
  let (s,c1,t,i,f)= gnfa in
  let actual_state = current_state s i f in 
  if actual_state = -1 then gnfa else
    let new_state_list = List.filter (fun y -> y <> actual_state) s in
    let state_to,state_to_state,to_state = trans_to_state t actual_state in
    let to_state = if(state_to_state = []) then to_state else List.map (fun ((si,r),sf) -> ((si,Concatenacao(r,(state_to_state_to_regex state_to_state))),sf)) to_state in
    let trans_by_state = List.concat (List.map (fun ((si,r),_) -> 
        List.map (fun ((_,rr),ssf) -> ((si, Concatenacao(r,rr)),ssf)) state_to
    ) to_state) in
    let trans_without_state = List.filter (fun ((si,_),sf) -> si <> actual_state && sf <> actual_state) t in
    let nova_lista = List.concat (List.map (fun ((si,r),sf) ->
        let rec func tl =
          match tl with
          | ((ssi,rr),ssf)::y -> if si == ssi && sf == ssf then [((si,Escolha (rr,r)),sf)] else func y
          | _ -> [((si,r),sf)] in
        func trans_without_state
      ) trans_by_state) in
    let nova_lista = (List.filter (fun x -> not (ghfhf nova_lista x)) trans_without_state) @ nova_lista in
    let gnfa2 = (new_state_list,c1,nova_lista,i,f) in
    resolve_gnfa gnfa2



(* função Main *)
let () =
  let s = read_multiplelines () in

  (* deve editar as chamadas aqui ... *)

  (* converte para o formato interno *)
  let gnfa = create_gnfa(add_state_nfa (nfa_of_string s)) in

 
  let (_,_,t,_,_) = resolve_gnfa gnfa in
  let ((_,t1),_) = List.nth t 0 in
  print_string(show_re t1);

  
  print_newline();