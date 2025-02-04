open Ppx_yojson_conv_lib.Yojson_conv.Primitives

(* o nosso autómato (PDA) *)
type estado = int [@@deriving yojson]

type simbolo = char option [@@deriving yojson]

type transicao = (estado * simbolo * simbolo) * (estado * simbolo)
[@@deriving yojson]

type pda =
  estado list
  * char list
  * char list
  * transicao list
  * estado list
  * estado list
[@@deriving yojson]

(* fita para colocar a palavra em aceitação *)
type fita = char option list [@@deriving yojson]

(* o nosso autómato (PDA) com uma palavra para aceitação *)
type pdaw = pda * fita [@@deriving yojson]

(* a nossa gramática livre de contexto (CFG) *)
type producao = char * string list [@@deriving yojson]

type cfg = producao list [@@deriving yojson]

(* a nossa gramática livre de contexto (CFG) com uma palavra na fita para
   aceitação *)
type cfgw = cfg * fita [@@deriving yojson]

let rec read_multiplelines () =
  try
    let line = read_line () in
    line ^ " " ^ read_multiplelines ()
  with End_of_file -> ""

let pda_of_string s = s |> Yojson.Safe.from_string |> pda_of_yojson

let string_of_pda a = a |> yojson_of_pda |> Yojson.Safe.to_string

let cfg_of_string s = s |> Yojson.Safe.from_string |> cfg_of_yojson

let string_of_cfg c = c |> yojson_of_cfg |> Yojson.Safe.to_string

let palavra_of_string s = s |> Yojson.Safe.from_string |> fita_of_yojson

let palavra_of_string_legivel s : fita =
  let lst_of_string s =
    String.to_seq s |> List.of_seq
    |> List.map (function '_' -> None | c -> Some c)
  in
  s |> lst_of_string

let string_of_palavra p = p |> yojson_of_fita |> Yojson.Safe.to_string

let string_of_palavra_legivel p =
  p
  |> List.map (function None -> "_" | Some c -> String.make 1 c)
  |> String.concat ""

(* deve efetuar as definições das funções ou submódulos aqui ... *)

let checkmatch s =
  match s with 
  |'_'->None
  |_->Some s

let rec createTrans c l t s alf=
  match l with 
    |x::y -> 
      if((String.length x) == 1 ) then 
        (
          let xxx = String.get x 0 in
          if ((xxx >= 'a' && xxx <= 'z') || (xxx >= '0' && xxx <= '9')) then 
            createTrans c y (t @ [((2,None,checkmatch c),(2,checkmatch xxx))]) s ([xxx]@alf) 
          else 
            createTrans c y (t @ [((2,None,checkmatch c),(2,checkmatch xxx))]) s alf
        )
      else 
        (
          let lista =List.rev( (List.of_seq (String.to_seq x)) )in
          match lista with
          |a::b -> 
            let rec addresto list t s1 alf2 =    
              match list with
              |c::[] -> if ((c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')) then  ((t @ [(((List.nth s1(List.length s1 - 1)),None,None),(2,checkmatch c))]), s1,([c]@alf2)) else ((t @ [(((List.nth s1(List.length s1 - 1)),None,None),(2,checkmatch c))]), s1,alf2)
              |c::d -> if ((c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')) then  addresto d (t @ [(((List.nth s1(List.length s1 - 1)),None,None),((List.nth s1(List.length s1 - 1))+1,checkmatch c))]) (s1@[(List.nth s1(List.length s1 - 1))+1]) ([c]@alf2) else addresto d (t @ [(((List.nth s1(List.length s1 - 1)),None,None),((List.nth s1(List.length s1 - 1))+1,checkmatch c))]) (s1@[(List.nth s1(List.length s1 - 1))+1]) alf2
              |_-> (t,s1,alf2) in
            let t2,s2,alfp = if ((a >= 'a' && a <= 'z') || (a >= '0' && a <= '9')) then addresto b (t @ [((2,None, checkmatch c),((List.nth s(List.length s - 1))+1,checkmatch a))]) (s@[(List.nth s(List.length s - 1))+1]) ([a]@alf) else addresto b (t @ [((2,None, checkmatch c),((List.nth s(List.length s - 1))+1,checkmatch a))]) (s@[(List.nth s(List.length s - 1))+1]) alf in
            createTrans c y t2 s2 alfp
          |_ -> createTrans c y t s alf
        )
    | _ -> (t,s,alf)

let rec gera_alfabeto palavra : char list= 
  match palavra with
  |x::y -> if (List.mem x y) then gera_alfabeto y else x :: gera_alfabeto y
  |_ -> []

let rec mais_trans list =
  match list with 
  |_::[]->[]
  |x::y ->[((2,Some x,Some x),(2,None))] @ mais_trans y
  |_ ->[]


let rec create_pda cfg pda = 
  match cfg with 
  |x::y -> 
    if (pda == ([],[],[],[],[],[])) then 
      let c,_ = x in
      create_pda cfg ([0;1;2],[],['$'],[((0,None,None),(1,Some '$'));((1,None,None),(2,Some c))],[0],[])
    else
      let s,ai,ap,t,si,sf = pda in
      let c,lista = x in
      let trans,estados, pilha_alf = createTrans c lista t s ap in
      create_pda y (estados,ai,pilha_alf,trans,si,sf)
  |_ -> 
    (
      let s,ai,af,t,si,_ = pda in
      let alf_pilha = gera_alfabeto af in
      let trans = t @ mais_trans alf_pilha @[((2,None,Some '$'),((List.nth s(List.length s - 1))+1,None))] in 
      let estados  = s @ [(List.nth s(List.length s - 1))+1] in 
      (estados,ai,alf_pilha,trans,si, [(List.nth s(List.length s - 1))+1])
    )
      
    

  let matchf si =
    match si with
  | Some c -> c
  | None -> '_'



  let rec working_pda3 tl input stack estado_atual f =
    
    if(List.length stack>30) then ["Rejeita"]else(
    

      if (stack == []&&input == []&&(List.mem estado_atual f)) then ["Aceita"] else(

        let rec restolista2 listr = 
        
          match listr with
          | ((estado,s1,s2),(nstate,nstack))::y ->(if (estado == estado_atual && (s1 == None || (input <>[] && matchf s1 == matchf(List.hd input))) &&(s2 == None || (stack <>[] && matchf s2 == matchf(List.hd stack))) )then working_pda3 tl (if(s1 == None)then input else List.tl input )  (if nstack == None then (if(s2 == None)then stack else List.tl stack ) else (if(s2 == None)then  [nstack]@stack else [nstack]@(List.tl stack) ) ) nstate f @ restolista2 y else restolista2 y  )   
          | _ -> ["Rejeita"] in
        restolista2 tl
        
      )
        
    )

(* type memoria = estado list * simbolo list * fita *)

(* exception FIM of memoria *)

(* quando for submeter pode desativar todos os prints extra utilizando
   verbose = false *)
let verbose = false

let enable f = if verbose then f else ignore

(* função principal *)
let () =
  let s = read_multiplelines () in
  enable print_endline s ;
  (* converter e imprimir palavra *)
  {|["a", "b", null, "c"]|} |> palavra_of_string |> string_of_palavra
  |> enable print_endline ;
  "ab_c" |> palavra_of_string_legivel |> string_of_palavra_legivel
  |> enable print_endline ;
  (* deve editar as chamadas aqui ... *)

  (* deve considerar também os seguintes blocos *)

  (* Exemplo: estados 1,2; alfabeto '0','1'; alfabeto da pilha; função
     transição: ((de,simbolo,simbolo), (para, simbolo)); estado inicial;
     estados finais *)
  ([1; 2], ['0'; '1'], ['a'; 'b'], [((1, None, None), (2, None))], [1], [2])
  |> string_of_pda |> enable print_endline ;
  (* converte para o formato interno *)
  let pda =
    pda_of_string
      {|[[1,2],["0","1"],["a","b"],[[[1,null,null],[2,null]]],[1],[2]]|}
  in
  (* imprime o json no formato interno *)
  pda |> string_of_pda |> enable print_endline ;
  (* converte uma string numa expressão regular *)
  let c =
    cfg_of_string
      {|[["S", ["ABC"]], ["A", ["aC", "D"]], ["B", ["bB", "A", "_"]], ["C", ["Ac","Cc", "_"]]]|}
  in
  (* imprime uma gramática livre de contexto *)
  c |> string_of_cfg |> enable print_endline;
  
  let s = Str.global_replace (Str.regexp{| |}) "" s in


  let re_cfgw = Str.regexp {|\[\[\["[A-Z].*|} in
  let re_pdaw = Str.regexp {|\[\[\[[0-9].*|} in

  let json =  s |> Yojson.Safe.from_string in


  if Str.string_match re_cfgw s 0
  then (


    let cfg, palavra = json |> cfgw_of_yojson in
    let _,_,_,t,si,f = create_pda cfg ([],[],[],[],[],[]) in
   (* let pda : pda = ([0;1;2],[],[],[((0,None,None),(1,Some '$'));((1,None,None),(2,Some 'S'))],[0],[]) in *)
    let teste = working_pda3 t palavra [] (List.nth si 0) f in 
    print_string(if (List.mem "Aceita" teste) then "Aceita\n" else "Rejeita\n");

  );

  if Str.string_match re_pdaw s 0
  then (
    let pda, palavra = json |> pdaw_of_yojson in
    let _,_,_,tl,i,f = pda in
    let teste = working_pda3 tl palavra [] (List.nth i 0) f in
    print_string(if (List.mem "Aceita" teste) then "Aceita\n" else "Rejeita\n");

  );