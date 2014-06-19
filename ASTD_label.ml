open Functions

type t = string

module Set_of = Set.Make( struct type t = string (***label=t***)
                                    let compare = compare
                             end )

type lazy_set = Set_of.t lazy_t

let of_string s = s

let empty_set = lazy Set_of.empty
let add elt s = lazy (Set_of.add elt (Lazy.force s))
let singleton elt = lazy (Set_of.singleton elt)
let union s1 s2 = lazy (Set_of.union (Lazy.force s1)(Lazy.force s2))
let inter s1 s2 = lazy ( Set_of.inter (Lazy.force s1) (Lazy.force s2))
let member elt s = Set_of.mem elt (Lazy.force s) 
let iteration_over_labels f s = Set_of.iter f (Lazy.force s) 
let fold_set f s b = Set_of.fold f (Lazy.force s) b

let label_set_from_list ~label_list = 
    let add_s s elt = add elt s
    in List.fold_left add_s empty_set label_list

(* Currently, a label is a string *)
let string_of l = l 
let print l = print_string l

let string_of_set = create_string_of_set fold_set string_of
let print_set = create_print_set iteration_over_labels print

