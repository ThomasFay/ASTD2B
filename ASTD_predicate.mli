(** ASTD predicate module *)

type name = string
type t = name * ASTD_term.params

exception ASTD_free_variable of ASTD_term.t * t

(*val _ASTD_predicate_definition_table_ :
      (name, ASTD_constant.t list -> bool) Hashtbl.t*)

(** {3 Constructor} *)

val predicate : name -> ASTD_term.params -> t

(** {3 Accessors} *)

val get_name : t -> name
val get_params : t -> ASTD_term.params

(** {3 Evaluation of a predicate} *)

val evaluate : t -> ASTD_environment.t -> bool         
val estimate : t -> ASTD_environment.t -> bool  


(** {3 Print and conversion in string} *)

val print_name : name -> unit
val print : t -> unit
val string_of_name : name -> string
val string_of : t -> string

(** {2 Registration of predicate} *)

val register : name -> (ASTD_constant.t list -> bool) -> unit

val get : name -> ASTD_constant.t list -> bool
