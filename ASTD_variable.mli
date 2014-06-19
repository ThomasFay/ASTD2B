(** EBS variable module *)

type t = string (* HIDDEN *)
type typed = t * ASTD_constant.set_name

(** {2 Constructor} *)

val of_string : string -> t

(** {2 Print and conversion in string} *)

(** {3 Printers} *)

val print : t -> unit
val print_list : t list -> unit

(** {3 Conversion in string} *)

val string_of : t -> string 
val string_of_list : t list -> string
