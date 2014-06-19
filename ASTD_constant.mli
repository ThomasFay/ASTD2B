(* type domain = string *)

(* type t = Integer of int | Symbol of string | FreeConst *)

(* type set_name = string *)

(* val string_of : t -> string *)

(* val of_int : int -> t *)

(* val contain_free : t list -> bool *)

(* val string_of_list : t list -> string *)

(* val is_included : t -> domain -> bool *)

(** ASTD constant module *)

(**The {!ASTD_constant.t} type allows us to use both integers and strings as constants, and FreeConst is a special constant allowing us to use any value *)
type t = Integer of int | Symbol of string | FreeConst (* HIDDEN *)
type set_name = string


module Set_of : Set.S with type elt = t
type set = Set_of.t

(**The {!ASTD_constant.value} type is a way to represent domains of values*)
type value = | Range of (int * int)
             | Val of t
             | FreeVal



(** A set needs a total ordering so this is the one I use : val(a)<val(b) if a<b \
                                                            Range(a,b)<Range(c,d)  if a<c or if a=c and b<d \
                                                            Val(a)<Range(b,c) if a<=b*)
module Domain : Set.S with type elt = value

(**The {!ASTD_constant.value} type is a Set, containing {!ASTD_constant.value}, that is to say a set representing all the possible domains of value *)
(*type domain=Domain.t*)

type domain= Domain.t



(** {2 Constant} *)
(** {3 Constructor of constant} *)

val of_int : int -> t

(** {3 Accessors}*)

val kind_of_val : t -> bool

(** {3 Printers} *)

val print : t -> unit
val print_list : t list -> unit

(** {3 Conversion in string} *)

val string_of : t -> string
val string_of_list : t list -> string
val int_of : t -> int







(** {2 Set of constant} *)

(** {3 Constructors of constant set} *)

val empty_set : set
val constant_set_from_list : t list -> set
val constant_set_from_range : min:int -> max:int -> set
 

(** {3 Iterator over set of constant} *)

val fold_set : (t -> 'a -> 'a) -> set -> 'a -> 'a
val iteration_over_set : (t -> unit) -> set -> unit
val for_all_constants : (t -> bool) -> set -> bool
val exists_a_constant : (t -> bool) -> set -> bool

(** {3 Other functions} *)

val add_in : t -> set -> set
val remove_from : t -> set -> set
val choose_in : set -> t 
val member : t -> set -> bool
val union : set -> set -> set
val is_empty : set -> bool

val contain_free : t list -> bool


(** {3 Printers} *)

val print_set_name : set_name -> unit
val print_set : set -> unit

(** {3 Conversion in string} *)

val string_of_set_name : set_name -> set_name
val string_of_set : set -> string







(** {2 Value } *)
(** {3 Constructors} *)

val range_of : int -> int -> value 
val value_of : t -> value

(** {3 Accessors} *)

val int_of_val : value ->int
val string_of_val : value ->string
val val_to_const : value ->t






(** {2 Domain = Set of values} *)
(** {3 Constructors} *)

val empty_dom : domain
val create_dom_from_val : value -> domain 

(** {3 Accessors} *)

val head_tail : domain -> (t*domain)
val is_included : t -> domain -> bool
val is_empty_dom : domain->bool
val map_dom : (value -> 'a) -> domain -> 'a list


(** {3 Domain manipulation}*)

val remove_domain_from : domain -> domain -> domain

val fusion : domain -> domain -> domain

val insert : value -> domain -> domain

val remove : value -> domain -> domain


(** {3 Conversion in string} *)

val print_dom : domain -> string










