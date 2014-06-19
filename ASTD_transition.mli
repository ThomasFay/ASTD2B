(** ASTD event module *)

(**The {!ASTD_transition.t} type refers to the function indicated on each arrow. It contains a label and a list of parameters that can be constants ,variables or a joker*)
type t = Transition of ASTD_label.t * ASTD_term.params 




(** {3 Constructors} *)

val transition : ASTD_label.t -> ASTD_term.params -> t


(** {3 Accessors} *)
val get_label : t -> ASTD_label.t

val get_params : t -> ASTD_term.params

val is_included : ASTD_label.t -> t list -> bool


