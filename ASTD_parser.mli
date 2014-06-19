(** ASTD parser tools module *)

exception ASTD_parsing_exception of string

type 'a parser_rule = (Lexing.lexbuf -> ASTD_parser_rules.token) -> Lexing.lexbuf -> 'a

val get_from : in_channel -> 'a parser_rule -> 'a

val get_from_stdin : 'a parser_rule -> 'a

val get_from_file : string -> 'a parser_rule -> 'a

(** {2 Structure} *)

(** get and parse a structure:
    - {!get_structure_from} ["stdin"] gets it from the [stdin] channel
    - {!get_structure_from} [filename] gets it from the file named [filename].*)
val get_structure_from : string -> unit

(** get and parse a structure from the [stdin] channel. *)
val get_structure_from_stdin : unit -> unit

(** {3 Event_list} *)

(** get and parse a structure:
    - {!get_event_list_from} ["stdin"] gets it from the [stdin] channel
    - {!get_event_list_from} [filename] gets it from the file named [filename].*)
val get_event_list_from : string -> ASTD_event.t list

(** get and parse a structure from the [stdin] channel. *)
val get_event_list_from_stdin : unit -> ASTD_event.t list

