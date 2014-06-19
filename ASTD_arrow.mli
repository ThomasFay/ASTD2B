(** ASTD arrow module *)

type from_state = string
type to_state = string
type through_state = string
type from_final_state = bool


(** The type {!ASTD_arrow.t} represents the arrows of the automata structure. *)
type t = Local of from_state * to_state * ASTD_transition.t * ASTD_predicate.t list * from_final_state 
(**Local arrows*)

|From_sub of from_state * to_state * through_state * ASTD_transition.t * ASTD_predicate.t list * from_final_state 
(**Arrows from superior astd, with through_state representing the name of the superior astd of the current one.*)

|To_sub of from_state * to_state * through_state * ASTD_transition.t * ASTD_predicate.t list * from_final_state
(**Arrows to an inferior astd, with through_state representing the name of the astd on the same level as the current state.*)



(** {3 Constructor} *)

val local_arrow :from_state -> to_state-> ASTD_transition.t -> ASTD_predicate.t list -> from_final_state -> t
val fsub_arrow :from_state -> to_state -> through_state -> ASTD_transition.t -> ASTD_predicate.t list -> from_final_state ->  t
val tsub_arrow :from_state -> to_state -> through_state -> ASTD_transition.t -> ASTD_predicate.t list -> from_final_state ->  t



(** {3 Accessors} *)

val get_from : t -> from_state
val get_to : t -> to_state
val get_through : t -> through_state
val get_transition : t -> ASTD_transition.t
val get_predicates : t-> ASTD_predicate.t list
val get_from_final_state : t-> from_final_state
val get_label_transition : t -> ASTD_label.t

val is_from_sub : t-> bool
val is_to_sub : t-> bool
val is_local : t-> bool

(** {3 Registration of transitions} *)




(** _ASTD_transition_table_ stores the parameters of possible transitions from structure for quantified astd, using the name of the quantified astd and the label of those transitions.*)

val register_transition : string->ASTD_transition.t -> unit
val register_transitions_from_list : string->ASTD_transition.t list -> unit
val get_transition_params : string->ASTD_label.t -> ASTD_term.params list



(** {3 Main Functions} *)

(** Evaluate the guard precisely using the {!ASTD_environment.t}. *)
val evaluate_guard : ASTD_environment.t -> ASTD_predicate.t list -> bool

(** Evaluate the guard. If the value used for a variable is ASTD_constant.FreeConst, the predicate is estimated at true. *)
val estimate_guard : ASTD_environment.t -> ASTD_predicate.t list -> bool

(** Evaluate the predicates on the arrow and compare the event with the transition. *)
val valid_arrow : ASTD_event.t -> ASTD_environment.t -> t -> bool


