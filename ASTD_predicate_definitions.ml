
let _ASTD_check_table_ = Hashtbl.create 5 



(*** PREDICATES ***)

let isGreater = function 
    | n::m::[] -> n > m
    | _ -> failwith "isGreater : bad arity"

let isZero = function 
    | n::[] -> n = ASTD_constant.of_int 0
    | _ -> failwith "isGreater : bad arity"

let isGreaterThanZero = function
    | n::[] -> n > ASTD_constant.of_int 0
    | _ -> failwith "isGreater : bad arity"



let clearAll = function
    |check_id::[]->begin
                    begin 
                    while begin Hashtbl.mem _ASTD_check_table_ check_id end 
                      do Hashtbl.remove _ASTD_check_table_ check_id  
                      done
                    end;
                    true
                   end
    |_-> failwith "clear bad arity"



let isGreaterThanOne = function
    | n::[] -> begin 
               (n > (ASTD_constant.of_int 1))
               end
    | _ -> failwith "isGreater : bad arity"
;;

let rEgistre = function
    |(check_id)::(value)::[] -> begin 
                            begin print_endline "REGISTER VALUE FOR CHECK";Hashtbl.add _ASTD_check_table_ check_id value 
                            end; 
                              true 
                                end
    |_ -> failwith "register, bad arity"
;;

let isSmall = function
    | check_id::[] -> begin
                       let a = Hashtbl.find _ASTD_check_table_ check_id in (a<=(ASTD_constant.of_int 10000))
                      end
    | _ -> failwith "isSmall : bad arity"




let isCheck = function
    | check_id::[] -> let a=Hashtbl.mem _ASTD_check_table_ check_id in a
    |_ ->failwith "isCheck : bad arity"

let none = function
    | [] -> true
    | _-> failwith "none as no parameters"
;;

(*** REGISTRATION ***)





ASTD_predicate.register "isGreater" isGreater ;;
ASTD_predicate.register "isZero" isZero ;;
ASTD_predicate.register "isGreaterThanZero" isGreaterThanZero ;;
ASTD_predicate.register "isGreaterThanOne" isGreaterThanOne ;;
ASTD_predicate.register "isSmall" isSmall;;
ASTD_predicate.register "isCheck" isCheck;;
ASTD_predicate.register "clearAll" clearAll;;
ASTD_predicate.register "rEgistre" rEgistre;;
ASTD_predicate.register "none" none;;


