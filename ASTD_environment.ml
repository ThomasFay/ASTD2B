open Functions

type binding = ASTD_variable.t * ASTD_term.t

type t = binding list 

exception ASTD_type_mismatch 

let map = List.map 
let fold_right = List.fold_right 
let fold_left = List.fold_left 
let fold = fold_right 
let find = List.find
let iter = List.iter (* not included in mli *)
let find_value_of environment variable = List.assoc variable environment

let rec reduce e term = match term with 
    | ASTD_term.Var v -> ( try find_value_of e v
                          with Not_found -> term )
    | ASTD_term.Const c -> term
    | ASTD_term.Addition (t1,t2) -> add_terms (reduce e t1) (reduce e t2) 
    | ASTD_term.Multiplication (t1,t2) -> multiply_terms (reduce e t1) (reduce e t2) 
    | ASTD_term.Substraction (t1,t2) -> substract_terms (reduce e t1) (reduce e t2) 
(* not included in mli *)
and apply_binary_operator_between_integer op t1 t2 = 
    let c1 = ASTD_term.extract_constant_from_term t1
    and c2 = ASTD_term.extract_constant_from_term t2
    in match (c1,c2) with
       | (ASTD_constant.Integer i1, ASTD_constant.Integer i2) 
         -> ASTD_term.Const (ASTD_constant.of_int (op i1 i2))
       | _ -> raise ASTD_type_mismatch 
(* not included in mli *)
and add_terms t1 t2 = try apply_binary_operator_between_integer ( + ) t1 t2 
                      with _ -> ASTD_term.Addition (t1,t2)
(* not included in mli *)
and multiply_terms t1 t2 = try apply_binary_operator_between_integer ( * ) t1 t2
                           with _ -> ASTD_term.Multiplication (t1,t2)
(* not included in mli *)
and substract_terms t1 t2 = try apply_binary_operator_between_integer ( - ) t1 t2
                            with _ -> ASTD_term.Substraction (t1,t2)

let rec evaluate e term = ASTD_term.extract_constant_from_term (reduce e term)

let bind v t = (v,t) 
and bind_var v v0 = (v, ASTD_term.Var v0) 
and bind_const v c = (v, ASTD_term.Const c) 

let get_var = fst
and get_value = snd

let empty = []

let add_binding b e = let v = get_var b
                      and t = get_value b
                      in let bind_temp=(bind v (reduce e t)) 
			in begin bind_temp::(List.remove_assoc v e)end

let of_binding b = add_binding b empty

let of_list_of_binding a_list = List.fold_right add_binding a_list empty

let put_on = fold add_binding

let (+>) = add_binding 

let (|>) = put_on 

let associate_vars_with_params = 
    let associate e v t = add_binding (bind v t) e
    in try List.fold_left2 associate empty 
       with Invalid_argument s -> print_endline "ASTD_environment.associate_vars_with_params" ; 
                                  raise (Invalid_argument ("ASTD_term" ^ s))


let rec increase_call env fct_list = match fct_list with
   |(a,b)::q -> let binding=bind a b in increase_call (add_binding binding env) q
   |[] -> env



let is_empty e = (e = empty)

let is_not_empty e = not (is_empty e)

let get_first = function 
                | b::e -> b
                | _ -> failwith "Empty environment."

let get_tail = function
               | b::e -> e
               | _ -> failwith "Empty environment."

let symbol_of_binding = ":=" 

let print_binding b = ASTD_variable.print (get_var b) ; 
                      print_string symbol_of_binding ; 
                      ASTD_term.print (get_value b)

let print = 
    create_print_container iter print_binding "([" "])" ";"

let string_of_binding b = 
    let string_of_var = ASTD_variable.string_of (get_var b)
    and string_of_value = ASTD_term.string_of (get_value b)
    in string_of_var ^ symbol_of_binding ^ string_of_value

let string_of = 
    create_string_of_container fold string_of_binding "([" "])" ";"

let compare_term_with_const_in env term constant = 
    begin 
       ASTD_term.compare_term_with_const (reduce env term) constant
    end

let compare_params_with_consts_in env t_list c_list =
    try ASTD_term.for_all2 (compare_term_with_const_in env) t_list c_list
    with Invalid_argument _ -> false



let compare_term_with_const_in2 env term constant = 
        if constant=ASTD_constant.FreeConst 
        then true 
        else begin match term with
    |ASTD_term.Var(a) -> ASTD_term.compare_term_with_const (reduce env term) constant
    |ASTD_term.Const(a)-> if a=ASTD_constant.Symbol("ANY VALUE")
                                   then begin true end
                                   else ASTD_term.compare_term_with_const term constant
    |_->failwith "addition, multiplication, .... not implemented"
             end

let compare_params_with_consts_in2 env t_list c_list =
    try ASTD_term.for_all2 (compare_term_with_const_in2 env) t_list c_list
    with Invalid_argument _ -> false



