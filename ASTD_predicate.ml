type name = string 

type t = name * ASTD_term.params

exception ASTD_free_variable of ASTD_term.t * t

let _ASTD_predicate_definition_table_ = Hashtbl.create 5 

let predicate name params = (name,params)

let get_name = fst
let get_params = snd

let register = Hashtbl.add _ASTD_predicate_definition_table_ 
let get = Hashtbl.find _ASTD_predicate_definition_table_ 

let evaluate p env =
    let name = get_name p
    and params = get_params p 
    in try  
        let pred = get name 
        and evaluate = ASTD_environment.reduce 
        in let evaluated_params = List.map (evaluate env) params
        in begin 
           let d=pred (ASTD_term.extract_constants_from_params evaluated_params)
           in d
           end
    with ASTD_term.ASTD_not_a_constant term
         -> raise (ASTD_free_variable (term,(name,params)))

let estimate p env =
    let name = get_name p
    and params = get_params p 
    in try  
        let pred = get name 
        and evaluate = ASTD_environment.reduce 
        in let evaluated_params = List.map (evaluate env) params
        in begin 
           let e = (ASTD_term.extract_constants_from_params evaluated_params)
           in if (ASTD_constant.contain_free e) then true
                                                else pred e
           end
    with ASTD_term.ASTD_not_a_constant term
         -> raise (ASTD_free_variable (term,(name,params)))


let print_name n = print_string n
let print p = let name = get_name p
              and params = get_params p
              in print_name name ;
                 ASTD_term.print_params params

let string_of_name n = n
let string_of p = let name = get_name p
                  and params = get_params p
                  in (string_of_name name)^(ASTD_term.string_of_params params)

