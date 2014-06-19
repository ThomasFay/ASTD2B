(** ASTD label module *)

type t = string (* HIDDEN *)

(** Module of label set *)
module Set_of : Set.S with type elt = t

(** Lazy set of label type *)
type lazy_set = Set_of.t lazy_t

(** {2 Constructor} *)

val of_string : string -> t

(** {2 Primitive function of lazy_set} *)

val empty_set : lazy_set
val add : t -> lazy_set -> lazy_set
val singleton : t -> lazy_set
val union : lazy_set -> lazy_set -> lazy_set
val inter : lazy_set -> lazy_set -> lazy_set
val member : t -> lazy_set -> bool

(** {3 Iterators} *)

val iteration_over_labels : (t -> unit) -> lazy_set -> unit
val fold_set : (t -> 'a -> 'a) -> lazy_set -> 'a -> 'a
val label_set_from_list : label_list:t list -> lazy_set 

(** {2 Print and conversion in string} *)

(** {3 Printers} *)

val print : t -> unit
val print_set : lazy_set -> unit

(** {3 Conversion in string} *)

val string_of : t -> string
val string_of_set : lazy_set -> string
