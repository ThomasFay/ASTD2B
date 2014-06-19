{
    open ASTD_parser_rules ;;
 
    let ebs_lexer_debug = false ;;
    let ebs_lexer_msg m = if (ebs_lexer_debug) 
                           then print_endline m 
                           else ignore m;;
}

let ws = ['\r''\n''\t'' '' ']
let lowerletters = ['a'-'z']
let upperletters = ['A'-'Z']
let letters = lowerletters | upperletters
let digits = ['0'-'9']
let id = "Id"
let underscore='_'
let quote='"'


rule token = parse
 | ws    { token lexbuf }
 | '%'   { LAMBDA }
 | "aut"   { AUTOMATA }
 | '.'   { SEQUENCE }
 | '*'   { KLEENE }
 | '+'   { PLUS }
 | '?'   { QMARK }
 | "|["  { LSYNCHRO }
 | "]|"  { RSYNCHRO }
 | "|||" { INTERLEAVE }
 | "||"  { PARALLEL }
 | '|'   { CHOICE }
 | "=>"  { GUARD }
 | "->"  { ebs_lexer_msg "new LINT" ;LINK }
 | "(["  { LENV }
 | "])"  { RENV }
 | "call" { CALL }
 | "elem" { ELEM }
 | "True" { TRUE }
 | "False" { FALSE }
 | '-'   { REMOVE }
 | "local"  {LOCAL}
 | "to_sub" {TO_SUB}
 | "from_sub" {FROM_SUB}
 | letters+ (letters+ | digits+ | underscore)*                    { ebs_lexer_msg "identifiant_name" ; IDENTITY_NAME    (Lexing.lexeme lexbuf) }
 | quote letters+ (letters+ | digits+ | underscore)* quote        { ebs_lexer_msg "string_name" ; STRING_VALUE    (Lexing.lexeme lexbuf) }
 | digits+ as number                                              { ebs_lexer_msg "new int value" ; INT_VALUE   (int_of_string number) } 


 | underscore                 {ebs_lexer_msg "new underscore" ; UNDERSCORE}
 | '<'   { BEGIN_ASTD }
 | '>'   { END_ASTD } 
 | '['   { ebs_lexer_msg "new LINT" ; LINT }
 | ']'   { ebs_lexer_msg "new RINT" ; RINT }
 | '{'   { ebs_lexer_msg "new LSET" ; LSET }
 | '}'   { ebs_lexer_msg "new RSET" ; RSET }
 | '('   { ebs_lexer_msg "new LPAR" ; LPAR }
 | ')'   { ebs_lexer_msg "new RPAR" ; RPAR }
 | ':'   { ebs_lexer_msg "new COLON" ; COLON }
 | ';'   { ebs_lexer_msg "new SCOLON" ; SCOLON }
 | ','   { ebs_lexer_msg "new COMMA" ; COMMA }
 | ":="  { IS }
 | '='   { EQUALS }
 | eof   { EOF }
