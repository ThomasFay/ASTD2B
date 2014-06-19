open ASTD_astd

exception ASTD_parsing_exception of string

type 'a parser_rule = (Lexing.lexbuf -> ASTD_parser_rules.token) -> Lexing.lexbuf -> 'a

let get_from from parser_entry_rules =
    let raw = let s = ref ""
              in try while true do s := (!s ^ (input_line from) ^ "\n") done ; ""
                 with End_of_file -> !s
    in let raw_spec = Lexing.from_string raw 
    in parser_entry_rules ASTD_lexer_rules.token raw_spec

let get_from_stdin rule = get_from stdin rule

let get_from_file file_name rule = let ic = open_in file_name
                                   in let result = get_from ic rule
                                      in begin
                                         close_in ic ;
                                         result
                                         end

let get_structure_from iname =
    let getter = if (iname = "stdin")
                 then get_from_stdin
                 else (get_from_file iname)
    in getter ASTD_parser_rules.structure


let get_structure_from_stdin = fun () -> (get_structure_from "stdin")




let get_event_list_from iname =
    let getter = if (iname = "stdin")
                 then get_from_stdin
                 else (get_from_file iname)
    in getter ASTD_parser_rules.apply_event


let get_event_list_from_stdin = fun () -> (get_event_list_from "stdin")




