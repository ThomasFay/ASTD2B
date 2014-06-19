(** ASTD environment module *)
(** only the increase_call function added in comparison with EBS*)

type binding = ASTD_variable.t * ASTD_term.t
type t = binding list


(** {2 Bindings} *)

val symbol_of_binding : string

(** {3 Constructor} *)

val bind : ASTD_variable.t -> ASTD_term.t -> binding
val bind_var : ASTD_variable.t -> ASTD_variable.t -> binding
val bind_const : ASTD_variable.t -> ASTD_constant.t -> binding

(** {3 Accessors} *)

val get_var : binding -> ASTD_variable.t
val get_value : binding -> ASTD_term.t

(** {3 Printers} *)

val print_binding : binding -> unit

(** {3 Conversion in string} *)

val string_of_binding : binding -> string

(** {2 Environments} *)

(** {3 Constructors} *)

val empty : t
val add_binding : binding -> t -> t
val of_binding : binding -> t
val of_list_of_binding : binding list -> t
val put_on : t -> t -> t
val ( +> ) : binding -> t -> t
val ( |> ) : t -> t -> t
val associate_vars_with_params : ASTD_variable.t list -> ASTD_term.params -> t
val increase_call : t -> (ASTD_variable.t * ASTD_term.t) list -> t  

(** {3 Accessors} *) 

val get_first : t -> binding
val get_tail : t -> t

(** {3 Iterator over environment} *)

(** {!ASTD_environment}[.find_value_of env var] find the {!ASTD_term}
    of the variable [var] in the environment [env].
    Raise {!Not_found} if there is no value associated with [var]
    in the environment [env].
    *)
val find_value_of : t -> ASTD_variable.t -> ASTD_term.t

(** {!ASTD_environment}[.map f env] applies function [f] 
    to all bindings in [env], and builds the environment 
    of all [[f b]] for all binding [b] in [e]. 
    Not tail-recursive. *)
val map : (binding -> 'a) -> t -> 'a list

(** {!ASTD_environment}[.fold_right f env n] is equivalent to
    [(f b1 (f b2 ... (f bn n) ...))] where [b1 ... bn]
    are the binding of [env]. Not tail-recursive. *) 
val fold_right : (binding -> 'a -> 'a) -> t -> 'a -> 'a

(** {!ASTD_environment}[.fold_left f n env] is equivalent to
    [(f ... (f (f n b1) b2)... bn)] where [b1 ... bn]
    are the binding of [env].*)
val fold_left : ('a -> binding -> 'a) -> 'a -> t -> 'a 

(** {!ASTD_environment}[.fold f env n] is equivalent to
    [(f bn ... (f b2 (f b1 n))...)] where [b1 ... bn]
    are the binding of [env].*)
val fold : (binding -> 'a -> 'a) -> t -> 'a -> 'a 

(** [find] for environment: 
    {!find} [p env] returns the first binding of the environment [env]
    that satisfies the predicate [p]. Raise [Not_found] if there
    no binding that satisfies [p] in [env].
    *)
val find : (binding -> bool) -> t -> binding

(** {3 Predicates} *)

val is_empty : t -> bool
val is_not_empty : t -> bool

(** {3 Printers} *)

val print : t -> unit

(** {3 Conversion in string} *)

val string_of : t -> string

(** {2 Interaction with terms and parameters} *)

(** {3 Evaluation of a term in an environment} *)

val reduce : t -> ASTD_term.t -> ASTD_term.t
val evaluate : t -> ASTD_term.t -> ASTD_constant.t

(** {3 Comparison of terms and parameters in an environment} *)

val compare_term_with_const_in : 
    t -> ASTD_term.t -> ASTD_constant.t -> bool

val compare_params_with_consts_in : 
    t -> ASTD_term.params -> ASTD_constant.t list -> bool


val compare_term_with_const_in2 : 
    t -> ASTD_term.t -> ASTD_constant.t -> bool

val compare_params_with_consts_in2 : 
    t -> ASTD_term.params -> ASTD_constant.t list -> bool


