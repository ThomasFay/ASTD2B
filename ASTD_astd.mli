(** ASTD astd module*)      
type astd_name = string;;

type path = astd_name list

val debug_on : unit -> unit



(** The type {!ASTD_astd.t} represents the structure of an ASTD. *)
type t = Automata of astd_name * t list * ASTD_arrow.t list * astd_name list* astd_name list  * astd_name
(**The automata structure, represented by the name of the astd, a list of sub-astd, a list of arrows, the list of the names of shallow final astds,the list of the names of deep final astd  and the name of the initial one*)

    | Sequence of  astd_name * t * t
(**The sequence structure, represented by the name of the astd, the left sub astd and the right one*)

    | Choice of astd_name * t * t 
(**The choice structure, represented by the name of the astd, the first sub astd and the second one*)

    | Kleene of astd_name * t
(**The kleene closure structure, represented by the name of the astd and the sub astd*)

    | Synchronisation of astd_name * ASTD_label.t list * t * t
(**The synchronisation structure, represented by the name of the astd, the list of synchronized transitions and the two sub astd of the structure*)
    | Fork of astd_name * ASTD_label.t list * ASTD_predicate.t list * t * t
    | QChoice of astd_name * ASTD_variable.t * string * t 
(**The quantified choice structure, represented by the name of the astd, the quantified variable, its domain of value and the sub astd*)

    | QSynchronisation of astd_name * ASTD_variable.t * string * ASTD_label.t list * t     
(**The quantified synchronisation structure, represented by the name of the astd, the quantified variable, her domain of value, the list of synchronized transitions, and the sub astd*)
    | QFork of astd_name * ASTD_variable.t * string * ASTD_predicate.t list * ASTD_label.t list * t

    | Guard of astd_name * ASTD_predicate.t list * t
(**The guard structure, represented by the name of the astd, a list of predicates and the sub astd *)

    | Call of astd_name * astd_name *  ((ASTD_variable.t *ASTD_term.t) list )
(**The call structure, with the name of the astd, the name of the called astd and a vector containing variables and their assigned value*)

    | Elem of astd_name
(**The base elem ASTD*)




(** {3 Constructor} *)


val give_name : unit -> astd_name
val automata_of : astd_name -> t list -> ASTD_arrow.t list -> astd_name list-> astd_name list-> astd_name -> t
val sequence_of : astd_name -> t -> t -> t
val choice_of : astd_name -> t -> t -> t
val kleene_of : astd_name -> t -> t
val synchronisation_of : astd_name -> ASTD_label.t list -> t -> t -> t
val qchoice_of : astd_name -> ASTD_variable.t -> string -> 'a -> t -> t
val qsynchronisation_of : astd_name -> ASTD_variable.t -> string -> ASTD_label.t list -> ASTD_optimisation.optimisation list-> t -> t
val qfork_of : astd_name -> ASTD_variable.t -> string -> ASTD_predicate.t list -> ASTD_label.t list -> t -> t
val fork_of : astd_name -> ASTD_label.t list -> ASTD_predicate.t list -> t -> t -> t
val guard_of : astd_name -> ASTD_predicate.t list -> t -> t
val call_of : astd_name -> astd_name -> ((ASTD_variable.t *ASTD_term.t) list )-> t
val elem_of : astd_name -> t
  


(** {3 Accessors} *)


val get_name: t -> astd_name
val get_sub : t -> t list
val get_arrows : t -> ASTD_arrow.t list
val get_deep_final : t -> astd_name list
val get_shallow_final : t -> astd_name list
val get_init : t -> astd_name
val get_seq_l : t -> t
val get_seq_r : t -> t
val get_choice1 : t -> t
val get_choice2 : t -> t
val get_astd_kleene : t -> t
val get_trans_synchronised : t -> ASTD_label.t list
val get_synchro_astd1 : t -> t
val get_synchro_astd2 : t -> t
val get_qvar : t -> ASTD_variable.t
val get_qvalues_c : t -> string
val get_qvalues_s : t -> string
val get_qastd : t -> t
val get_guard_pred : t -> ASTD_predicate.t list
val get_guard_astd : t -> t
val get_called_name : t -> astd_name
val get_called_values : t ->((ASTD_variable.t *ASTD_term.t) list )




val get_data_automata :t -> (astd_name * t list * ASTD_arrow.t list * astd_name list* astd_name list * astd_name)
val get_data_sequence :t -> (astd_name * t * t )
val get_data_choice :t -> (astd_name * t * t )
val get_data_kleene :t -> (astd_name * t )
val get_data_synchronisation :t -> (astd_name * ASTD_label.t list * t *t)
val get_data_guard :t -> (astd_name * ASTD_predicate.t list * t)
(* val get_data_qchoice :t -> (astd_name * ASTD_variable.t * ASTD_constant.domain * ASTD_optimisation.dependency list *t) *)
(* val get_data_qsynchronisation : *)
(*                t -> (astd_name * ASTD_variable.t * ASTD_constant.domain * ASTD_label.t list * ASTD_optimisation.optimisation list * t ) *)
val get_data_call : t -> (astd_name * astd_name * ((ASTD_variable.t *ASTD_term.t) list ))


(**Finds all transitions accessible from the sub_astd *)
val get_sub_transitions : astd_name list ->t -> ASTD_transition.t list
val get_sub_arrows : astd_name list -> t -> ASTD_arrow.t list
val get_sub_names : astd_name list -> t -> astd_name list


(** {3 Manipulation Functions} *)

val rename_astd: t -> astd_name -> t
val is_elem : t-> bool
val is_synchro : t ->bool
val is_qchoice : t ->bool
val is_qsynchro : t ->bool
val is_automata : t ->bool



(** {3 Main Functions} *)

(**Finds the right sub astd from a list using his name *)
val find_subastd : astd_name -> t list -> t 

(**Check if if the initial state of the astd is sure to be final or if we don't know for sure without checking the environment*)
val is_init_final : t -> astd_name list -> string



val replace_sub_astd: t-> astd_name -> t list-> t list


(** {3 Registration of astd} *)

(** _ASTD_astd_table_ stores astd, using their name. *)

val get_astd : astd_name -> t  

val get_call_astd : astd_name -> (t*((ASTD_variable.t * ASTD_constant.domain ) list))  

(*val call_astd : astd_name -> ASTD_environment.t -> t *)

val global_save_astd : t->(ASTD_variable.t * ASTD_constant.domain ) list->unit



(** {3 Printer} *)

val print : t->string-> unit


