open Ast

(* id é dado por um número inteiro de 0..n *)
type estado = int 
(* Some(c): c é uma letra do alfabeto de a..z e None: o símbolo _ *)
type simbolo = char option
(* ((p,l),q): transição do estado p para o estado q utilizando o símbolo l *)
type transicao = ((estado * simbolo) * estado)
(* lista de estados iniciais, lista de estados finais e lista de transições *)
type automato = (estado list * estado list * transicao list) 


let print_simbolo simbolo =
  match simbolo with
  | Some c -> print_char c
  | None -> print_char '_'

let print_trans trans = 
  let ((state1,value),state2) = trans in
  print_int state1;
  print_string " ";
  print_simbolo value;
  print_string " ";
  print_int state2


let rec count_node auto = 
  match auto with
  | Vazio -> 1
  | Caracter _ -> 2
  | Concatenacao (x,y) -> count_node x + count_node y
  | Escolha  (x,y) -> 1 + count_node x + count_node y
  | Estrela x -> 1 + count_node x

let rec trans_estrela final_states first_state =
  match final_states with
  | x::y -> [((x, Some '_' ),first_state)] @ trans_estrela y first_state
  | _ -> []

let rec f2 re s : automato =
  match re with
  | Vazio -> [s], [s], []
  | Caracter c -> [s], [s+1], [((s,Some c) ,s+1)]
  | Concatenacao(a, b) ->
    let states_b = count_node b in
    let (ib,fb,tb) = f2 b s in
    let (ia,fa,ta) = f2 a (states_b + s) in
    let first_state_b = List.nth ib 0 in
    ia, fb, (trans_estrela (List.rev fa) first_state_b)@ ta @ tb
  | Escolha(a,b) ->
    let (ib,fb,tb) = f2 b s in
    let (ia,fa,ta) = f2 a (count_node b + s) in
    let first_state = (count_node a + count_node b) + s in
    let first_ia = List.nth ia 0 in
    let first_ib = List.nth ib 0 in
    [first_state], fa @ fb, [((first_state, Some '_'),first_ia)] @ [((first_state, Some '_'),first_ib)] @ ta @ tb
  | Estrela a ->
    let (ia,fa,ta) = f2 a s in
    let first_ia = List.nth ia 0 in
    let first_state = (count_node a)  + s in
    [first_state],  [first_state] @ fa , [((first_state, Some '_'), first_ia)] @ (trans_estrela (List.rev fa) first_ia)  @ ta  
    
  


let rec show_trans t =
  match t with
  | x::[] -> print_trans x
  | x::y -> print_trans x; print_newline(); show_trans y
  | _ -> print_string ""

let rec show_final f =
  match f with
  | x::[] -> print_int x; print_newline()
  | x::y -> print_int x; print_string(" "); show_final y
  | _ -> print_newline()

(* função Main *)
let () =
  let s = read_line () in
  let r = Parser.main Lexer.token (Lexing.from_string s) in
  (*print_endline (imprimir_re r)*)
  print_int (count_node r);
  print_newline();
  let (i,f,trans) = f2 r 1 in
  print_int (List.length i);
  print_newline();
  print_int (List.nth i 0);
  print_newline();
  print_int (List.length f);
  print_newline();
  show_final f;
  print_int(List.length trans);
  print_newline();
  if (List.length trans == 0) then print_string ""
  else
  (show_trans trans;
  print_newline())

  (* deve editar as chamadas aqui ... *)