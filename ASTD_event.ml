
type t = Event of ASTD_label.t * ASTD_constant.t list 

(* Event *)

let event label consts = Event (label,consts)



let compare_action_with_event env a e  = 
    match (a,e) with 
    | (ASTD_transition.Transition(alabel, aparams), Event (elabel, econsts))  
      -> (begin (alabel = elabel) end) && 
              begin (ASTD_environment.compare_params_with_consts_in env aparams econsts) end
           
;;

let compare_action_with_event2 env a e  = 
    match (a,e) with 
    | (ASTD_transition.Transition(alabel, aparams), Event (elabel, econsts))  
      -> (begin (alabel = elabel) end) && 
              begin (let c=ASTD_environment.compare_params_with_consts_in2 env aparams econsts
                     in begin  c end)
              end
           
;;

let string_of_event event = 
    match event with
    | Event (label,consts) 
      -> let label_s = ASTD_label.string_of label
         and consts_s = ASTD_constant.string_of_list consts 
         in label_s ^ consts_s


let get_const ev = match ev with
 | Event (label,consts) -> consts
 
let get_data ev = match ev with
 |Event (label,consts) -> (label,consts)

let get_label ev = match ev with
 |Event (label,consts) -> label

let print_event e = print_string (string_of_event e)

let print_event_ln e = print_endline (string_of_event e)

