(** ASTD term module *)

type t =   Var of ASTD_variable.t 
         | Const of ASTD_constant.t
         | Addition of t*t
         | Multiplication of t*t
         | Substraction of t*t

type params = t list

exception ASTD_not_a_constant of t

(** {2 Term} *)

(** {3 Comparison} *)

val compare_syntax : t -> t -> bool 
val compare_term_with_const : t -> ASTD_constant.t -> bool 

(** {3 Printers} *)

val print : t -> unit

(** {3 Conversion in string} *)

val string_of : t -> string

(** {2 Parameters} *)

(** {3 Constructors} *)

val parameters_of_variables : ASTD_variable.t list -> params
val parameters_of_constants : ASTD_constant.t list -> params

(** {3 Comparison} *)

val compare_syntax_of_params : params -> params -> bool
val compare_params_with_consts : params -> ASTD_constant.t list -> bool

(** {3 Utilities} *)

val extract_constant_from_term : t -> ASTD_constant.t
val extract_constants_from_params : params -> ASTD_constant.t list
val check_constants_from : params -> bool


(** {3 Iterator over parameters} *)

(** {!map} [f params] applies function [f] 
    to all terms in [params], and builds the parameters 
    of all [[f t]] for all term [t] in [params]. 
    Not tail-recursive. *)
val map : (t -> 'a) -> params -> 'a list

(** {!foldl} [f a [b1; ...; bn]] is [f ... (f (f a b1) b2) bn].*)
val foldl : ('a -> t -> 'a) -> 'a -> params -> 'a

(** {!foldr} [f [b1; ...; bn] a] is [f b1 (f b2 (... (f bn-1 (f bn a))))].*)
val foldr : (t -> 'a -> 'a) -> params -> 'a -> 'a

(** {!find} [p params] returns the first term of the parameters [params]
    that satisfies the predicate [p]. Raise [Not_found] if there
    no term that satisfies [p] in [params].
    *)
val find : (t -> bool) -> params -> t

(** {3 Parameters scanning} *)

val exists : (t -> bool) -> params -> bool

val for_all : (t -> bool) -> params -> bool

val for_all2 : (t -> 'a -> bool) -> params -> 'a list -> bool

(** {3 Printers} *)

val print_params : params -> unit

(** {3 Conversion in string} *)

val string_of_params : params -> string


