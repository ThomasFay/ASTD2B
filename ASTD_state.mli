(** ASTD state module *)


type position = string
type step = Fst| Snd
type side = Undef | Left | Right
type qchoice = Val of ASTD_term.t |ChoiceNotMade
type astd_name = string
type called_path =astd_name list

val debug_on : unit -> unit

(** The type {!ASTD_state.t} represents the current state of an ASTD. *)
type t = Automata_s of position * ((astd_name * t) list) * t
(**The automata state contains the name of the current sub astd, the history of the states, and the current sub state *)

        |Sequence_s of step * t
(**The sequence state contains an indication of which side of the sequence is currently studied, and the current sub state*)

        |Choice_s of side * t
(**The choice state contains an indication of which one of the two sub astd is currently studied, and the current sub state. If the choice hasn't been made yet, the choice indication is Undef and the state is NotDefined*)

        |Kleene_s of bool * t
(**The kleene closure state precise if the execution of the sub astd has started, and contains the current sub state *)

        |Synchronisation_s of t * t
(**The synchronisation state contains the two sub states*)

        |QChoice_s of qchoice *(ASTD_constant.domain)* (ASTD_constant.domain) * t
(**The quantified choice state contains the chosen value and the sub state. If the choice hasn't been made yet, the value is ChoiceNotMade and the sub state is NotDefined. The two domains are used while the choice hasn't been made : the first is the list of values for which the state is unknown and the second is the list of values for which we don't know if the state is final or not*)

        |QSynchronisation_s  of (ASTD_constant.domain)*(ASTD_constant.domain)*(ASTD_constant.domain) * t
(**The quantified synchronisation state contains the domain of values that we are sure are not finals, the domain of values we don't know if they are final, the values corresponding to not initial states of the sub astd and the initial sub astd.*)

        |Guard_s of bool * t
(**The guard state precise if the execution has been accepted once, and contains the sub state*)

        |Call_s of bool * t
(**The call state precise if the call has been made. If not, the sub state is NotDefined*)

        |NotDefined
(**Not defined state*)

        |Elem
(**Elementary state*)




(** {3 Constructors} *)

val automata_s_of : position -> ((astd_name * t) list) -> t -> t
val sequence_s_of : step -> t -> t
val choice_s_of : side -> t -> t
val kleene_s_of : bool -> t -> t
val synchronisation_s_of : t -> t -> t
val qchoice_s_of : qchoice ->(ASTD_constant.domain)->(ASTD_constant.domain)-> t -> t
val qsynchronisation_s_of :(ASTD_constant.domain)->(ASTD_constant.domain)->(ASTD_constant.domain) -> t->t
val guard_s_of : bool -> t -> t
val call_s_of : bool -> t -> t
val not_defined_state :  unit -> t

val undef_choice_of : unit -> side
val right_choice_of : unit -> side
val left_choice_of : unit -> side

val first_sequence_of : unit -> step
val second_sequence_of : unit -> step

val qchoice_notmade_of : unit -> qchoice



(** {3 Accessors} *)

val get_pos : t -> astd_name
val get_data_from_qsynchro : t -> ((ASTD_constant.domain) *(ASTD_constant.domain)*(ASTD_constant.domain) * t)
val get_val : qchoice -> ASTD_term.t
val get_data_automata_s : t-> (position * ((astd_name * t) list) * t)







(** {3 Manipulation Functions} *)

val is_automata : t -> bool
val is_qsynchro : t -> bool
val val_of : ASTD_term.t -> qchoice











(** {3 Conversion in string} *)

val string_of_qchoice : qchoice -> string
val string_of_seq : step -> string
val string_of_choice : side -> string 
val string_of_bool : bool -> string





(** {3 Registration of states from a quantified synchronisation} *)

(** _ASTD_synch_table_ stores states, using the name of the quantified synchronisation, the environment, the list of calls it have been through and the chosen value. *)


val remove_all : string -> ASTD_constant.t option ->ASTD_astd.t -> unit
val register_synch : string -> ASTD_constant.t option-> t ->ASTD_astd.t -> unit
val get_synch : string->ASTD_constant.t option->ASTD_astd.t -> t
val get_synch_state : ASTD_constant.domain -> t -> string -> ASTD_constant.t option->ASTD_astd.t ->t

val save_data : ((string*ASTD_constant.t option)*ASTD_astd.t*t*bool) list->unit





