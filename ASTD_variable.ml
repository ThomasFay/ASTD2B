open Functions

type t = string

type typed = t * ASTD_constant.set_name

let of_string s = s

let print v = print_string v

let print_list = create_print_list print

let string_of v = v 

let string_of_list = create_string_of_list string_of 

