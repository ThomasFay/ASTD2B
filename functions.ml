
let compose f g = function x -> f (g x)

let switch_args f = (fun x -> fun y -> f y x)

let gen_int_list n = 
    let rec aux n l = if (n = 0)
                      then l
                      else aux (n-1) (n::l)
    in aux n []

let print_space n = print_newline () ; for j=1 to n do print_string " " done

let rec filter_not liste predicat = 
    let not_pred x = not (predicat x)
    in List.filter not_pred liste 

let create_print_container container_iter print_element left right sep = 
    function container ->
        let first = ref true
        in let print_each e = if (!first) 
                              then first := false
                              else print_string sep ;
                              print_element e
        in begin
           print_string left;
           container_iter print_each container ;
           print_string right 
           end

let create_print_set iter print_element = 
    create_print_container iter print_element "{" "}" ","

let create_print_list print_element = 
    create_print_container List.iter print_element "(" ")" ","

let create_string_of_container container_fold string_of_element left right sep = 
    function container ->
        let first = ref true in 
        let add_after_first sep  = if !first then (first := false ; "") else sep in
        let string_of_one_element e = (add_after_first sep) ^ (string_of_element e) in 
        let add_one_elt_after e s = s ^ (string_of_one_element e) in
        let all_elements = container_fold add_one_elt_after container ""
        in left ^ all_elements ^ right

let create_string_of_set fold string_of_element = 
    create_string_of_container fold string_of_element "{" "}" ","

let create_string_of_list string_of_element = 
    let list_fold f l b = List.fold_left (fun x -> fun y -> f y x) b l
    in
        create_string_of_container list_fold string_of_element "(" ")" ","

