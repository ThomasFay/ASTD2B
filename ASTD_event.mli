(** ASTD event module *)

(**The {!ASTD_event.t} type represents the action introduced by the user of the application. It means he should introduce a label, the name of the function, and a list of constants which are the values of the parameters*)
type t = Event of ASTD_label.t * ASTD_constant.t list 


(** {3 Constructors} *)

val event : ASTD_label.t -> ASTD_constant.t list -> t


(** {3 Accessors}*)

val get_const : t -> ASTD_constant.t list
val get_data : t -> (ASTD_label.t * ASTD_constant.t list)
val get_label : t -> ASTD_label.t


(** {3 Comparison with an action} *)

val compare_action_with_event : ASTD_environment.t -> ASTD_transition.t -> t -> bool

val compare_action_with_event2 : ASTD_environment.t -> ASTD_transition.t -> t -> bool

(** {3 Printers} *)

val print_event : t -> unit

val print_event_ln : t -> unit

(** {3 Conversion in string} *)

val string_of_event : t -> string


