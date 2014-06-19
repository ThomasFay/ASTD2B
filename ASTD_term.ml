open Functions

type t =   Var of ASTD_variable.t 
         | Const of ASTD_constant.t
         | Addition of t*t
         | Multiplication of t*t
         | Substraction of t*t

type params = t list

exception ASTD_not_a_constant of t

(* Iterators over params *)
let foldl f b p = List.fold_left (f:'a -> t -> 'a) b (p:params)
and foldr f p b = List.fold_right (f:t -> 'a -> 'a) (p:params) b
and map = List.map 
and find = List.find
(* --- *)

(* params scanning *)
let exists = List.exists 
and for_all = List.for_all
and for_all2 = List.for_all2

let rec compare_syntax = (=)

let compare_term_with_const t c =
    match t with
    | Const c0 -> c = c0
    | _ -> false

let compare_syntax_of_params p1 p2 =
    try for_all2 compare_syntax p1 p2
    with Invalid_argument _ 
         -> print_endline "ASTD_term.compare_params" ; false 

let compare_params_with_consts p list_of_constants =
    try for_all2 compare_term_with_const p list_of_constants
    with Invalid_argument _ 
         -> print_endline "ASTD_term.compare_params_with_consts" ; false

let parameters_of_variables vars = 
    List.map (fun v -> Var v) vars

let parameters_of_constants constants = 
    List.map (fun v -> Const v) constants

let extract_constant_from_term =
    function
    | (Const c) -> c
    | _ as t    -> raise (ASTD_not_a_constant t) 

let extract_constants_from_params =
    map extract_constant_from_term

let check_constants_from = 
    let check_one = function
        | (Const c) -> true
        | _         -> false
    in for_all check_one  

let rec string_of = function 
    | Var v   -> v
    | Const c -> ASTD_constant.string_of c
    | Addition(t1,t2) -> string_of_binary_complex_term " + " t1 t2
    | Multiplication(t1,t2) -> string_of_binary_complex_term " * " t1 t2 
    | Substraction(t1,t2) -> string_of_binary_complex_term " - " t1 t2 
and string_of_binary_complex_term operator_string t1 t2 = 
    "(" ^ (string_of t1) ^ operator_string ^ (string_of t2) ^ ")"

let string_of_params = create_string_of_list string_of

let print t = print_string (string_of t)

let print_params = create_print_list print



