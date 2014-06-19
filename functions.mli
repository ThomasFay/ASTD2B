(** General functions module *)

val compose : ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c

val switch_args : ('a -> 'b -> 'c) -> ('b -> 'a -> 'c)

val gen_int_list : int -> int list

val filter_not : 'a list -> ('a -> bool) -> 'a list

val print_space : int -> unit

(** {2 Print container} *)

val create_print_container : 
  (('a -> 'b) -> 'c -> 'd) -> 
  ('a -> 'b) -> string -> string -> string -> 'c -> unit

val create_print_set : (('a -> 'b) -> 'c -> 'd) -> ('a -> 'b) -> 'c -> unit

val create_print_list : ('a -> unit) -> 'a list -> unit

(** {2 String of container} *)

val create_string_of_container :
  (('a -> string -> string) -> 'b -> string -> string) -> 
  ('a -> string) -> string -> string -> string -> 'b -> string

val create_string_of_set :
  (('a -> string -> string) -> 'b -> string -> string) ->
  ('a -> string) -> 'b -> string

val create_string_of_list : ('a -> string) -> 'a list -> string

