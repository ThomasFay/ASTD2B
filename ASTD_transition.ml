
type t = Transition of ASTD_label.t * ASTD_term.params 



let transition label consts = Transition (label,consts)
;;

let get_label a = let Transition(label,_)=a in label
;;


let get_params a = let Transition(_,consts)=a in consts
;;

let rec is_included label trans_list = match trans_list with
    |a::q -> if (label = get_label a)
                then true
                else is_included label q
    |[] -> false
;;

