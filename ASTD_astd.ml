type astd_name = string;;

type path = astd_name list


(*
General ASTD Type. Constructed by induction. The different induction types are :
- Automata : constructed with
  - astd_name : The name of the ASTD (a string)
  - t list : A list of ASTD representing the states of the ASTD
  - ASTD_arrow.t list : A list representing the ASTD transition
  - astd_name list : A list representing the ASTD shallow final states
  - astd_name list : A list representing the ASTD deep final states
  - astd_name : an ASTD name standing for the initial state of the ASTD
- Sequence : constructed with
  - astd_name : the name of the astd
  - t : an ASTD representing the first ASTD of the sequence
  - t : an ASTD representing the second ASTD of the sequence
- Choice : contructed with
  - astd_name : The name of the ASTD
  - t : The first ASTD of the choice operator
  - t : The second ASTD of the choice operator
- Kleene : constructed with
  - astd_name : the name of the ASTD
  - t : the ASTD that is closed
- Synchronisation : constructed with
  - astd_name : The name of the ASTD
  - ASTD_label.t list : the list of synchronised operations (DELTA)
  - t : The first ASTD of the synchronisation
  - t : The second ASTD of the synchronisation
- QChoice : constructed with
  - astd_name : The name of the ASTD
  - ASTD_variable.t : Variable 
  - string : name of the domain of the variable
  - t : sub ASTD that will be chosen
- QSynchronisation
  - astd_name
  - ASTD_variable.t
  - ASTD_constant.domain
  - ASTD_label.t list
  - ASTD_optimisation.optimisation list
  - t 
- Guard
  - astd_name
  - ASTD_predicate.t list
  - t
- Call
  - astd_name
  - astd_name
  - (ASTD_variable.t *ASTD_term.t)
  - list 
  - Elem of astd_name

*)

type t = Automata of astd_name * t list * ASTD_arrow.t list * astd_name list * astd_name list * astd_name
    | Sequence of  astd_name * t * t
    | Choice of astd_name * t * t 
    | Kleene of astd_name * t
    | Synchronisation of astd_name * ASTD_label.t list * t * t
    | Fork of astd_name * ASTD_label.t list * ASTD_predicate.t list * t * t
    | QChoice of astd_name * ASTD_variable.t * string * t
    | QSynchronisation of astd_name * ASTD_variable.t * string * ASTD_label.t list * t 
    | QFork of astd_name * ASTD_variable.t * string * ASTD_predicate.t list * ASTD_label.t list * t
    | Guard of astd_name * ASTD_predicate.t list * t
    | Call of astd_name * astd_name * (ASTD_variable.t *ASTD_term.t) list 
    | Elem of astd_name
;; 


    let val_debug = ref false;;
    let debug m = if (!val_debug) 
                            then (print_endline m )
                            else begin end;;
    let debug_on () = (val_debug := true);;




let give_name=
  let n= ref 0 
      in function () -> 
                n:=!n+1;
                "gen_astd_"^(string_of_int !n)
;;




let automata_of name astd_l arrow_l shallow_final_states deep_final_states init  = Automata (name,astd_l,arrow_l,shallow_final_states,deep_final_states,init);;

let sequence_of name astd_l astd_r = Sequence (name,astd_l,astd_r);;

let choice_of name astd1 astd2 = Choice (name,astd1,astd2);;

let kleene_of name a = Kleene (name,a);;

let synchronisation_of name transition_list a1 a2 = Synchronisation (name,transition_list,a1,a2);;

let qchoice_of name var val_list dep a  = QChoice (name,var,val_list,a);;

let qsynchronisation_of name var val_list transition_list opt a   = 
                                          QSynchronisation (name,var,val_list,transition_list,a);;

let qfork_of name var val_list predicate_list transition_list a =
  QFork (name,var,val_list,predicate_list,transition_list,a)

let fork_of name transition_list predicate_list a1 a2 =
  Fork (name,transition_list,predicate_list,a1,a2)

let guard_of name predicate_list a = Guard(name,predicate_list,a);;

let call_of name called_name fct_vect = Call(name,called_name,fct_vect);;

let elem_of name = Elem (name) ;;





let get_name a = match a with
  | Automata (name,_,_,_,_,_) -> name 
  | Sequence (name,_,_) -> name
  | Choice (name,_,_) -> name
  | Kleene (name,_) -> name
  | Synchronisation (name,_,_,_) -> name
  | QChoice (name,_,_,_) -> name
  | QSynchronisation (name,_,_,_,_) -> name  
  | Guard (name,_,_) -> name
  | Call  (name,_,_) -> name
  | Elem (name) -> name
  | QFork (name,_,_,_,_,_) -> name
  | Fork (name,_,_,_,_) -> name
;;


let get_sub a = match a with
  |Automata (_,l,_,_,_,_) -> l
  | _ -> failwith "unappropriate request aut sub"
;;


let get_arrows a = match a with
  |Automata (_,_,arrows,_,_,_) -> arrows 
  | _ -> failwith "unappropriate request get_arrows"
;;

let get_deep_final a = match a with
  |Automata (_,_,_,_,final,_) -> final
  | _ -> failwith "unappropriate request get_final"
;;

let get_shallow_final a = match a with
  |Automata (_,_,_,final,_,_) -> final
  | _ -> failwith "unappropriate request get_final"
;;

let get_init a = match a with
  |Automata (_,_,_,_,_,init) -> init
  | _ -> failwith "unappropriate request get_init"
;;



let get_seq_l a = match a with
  |Sequence (_,l,_) -> l
  | _ -> failwith "unappropriate request seq_l"
;;

let get_seq_r a = match a with
  |Sequence (_,_,r) -> r
  | _ -> failwith "unappropriate request seq_r"
;;

let get_choice1 a = match a with
  |Choice (_,un,_) -> un
  | _ -> failwith "unappropriate request choice1"
;;

let get_choice2 a = match a with
  |Choice (_,_,deux) -> deux
  | _ -> failwith "unappropriate request choice2"
;;


let get_astd_kleene a = match a with
  |Kleene (_,astd) -> astd
  | _ -> failwith "unappropriate request astd_kleene"
;;


let get_trans_synchronised a = match a with
  |Synchronisation (_,trans_list,_,_) -> trans_list
  |QSynchronisation (_,_,_,trans_list,_) -> trans_list
  | _ -> failwith "unappropriate request trans_synchronised"
;;


let get_synchro_astd1 a = match a with
  |Synchronisation (_,_,astd1,_) -> astd1
  | _ -> failwith "unappropriate request synchro_astd1"
;;


let get_synchro_astd2 a = match a with
  |Synchronisation (_,_,_,astd2) -> astd2
  | _ -> failwith "unappropriate request synchro_astd2"
;;


let get_qvar a = match a with
  |QChoice (_,v,_,_) -> v
  |QSynchronisation (_,v,_,_,_) -> v
  | _ -> failwith "unappropriate request get_qvar"
;;

let get_qvalues_c a = match a with
  |QChoice (_,_,val_list,_) -> val_list
  | _ -> failwith "unappropriate request get_qvalues_c"
;;

let get_qvalues_s a = match a with
  |QSynchronisation (_,_,val_list,_,_) -> val_list
  | _ -> failwith "unappropriate request get_qvalues_s"
;;



let get_qastd a = begin debug (" get sub qastd "^(get_name a));
 match a with
  |QChoice (_,_,_,astd) -> astd
  |QSynchronisation (_,_,_,_,astd) -> astd
  | _ -> failwith "unappropriate request get_qastd" end

;;

let get_guard_pred a =match a with
  |Guard (_,pred,_) -> pred
  | _ -> failwith "unappropriate request get_guard_pred"
;;
  

let get_guard_astd a =match a with
  |Guard (_,_,astd) -> astd
  | _ -> failwith "unappropriate request get_guard_astd"
;;

let get_called_name a = match a with
  |Call (_,called,_) -> called
  | _ -> failwith "unappropriate request get_called_name"
;;

let get_called_values a = match a with 
  |Call (_,_,var_val_list) -> var_val_list 
  | _ -> failwith "unappropriate request get_called_values"
;;



let rename_astd astd_to_rename namebis = match astd_to_rename with
   |Automata (a,b,c,d,e,f) -> Automata (namebis,b,c,d,e,f)
   |Sequence (a,b,c) -> Sequence (namebis,b,c)
   |Choice (a,b,c) -> Choice (namebis,b,c)
   |Kleene (a,b) -> Kleene (namebis,b)
   |Synchronisation (a,b,c,d) -> Synchronisation (namebis,b,c,d)
   |QChoice (a,b,c,d) -> QChoice (namebis,b,c,d)
   |QSynchronisation (a,b,c,d,f) -> QSynchronisation (namebis,b,c,d,f)
   |QFork (a,b,c,d,e,f) -> QFork (namebis,b,c,d,e,f)
   |Fork(a,b,c,d,e) -> Fork (namebis,b,c,d,e)
   |Guard (a,b,c) -> Guard (namebis,b,c)
   |Call (a,b,c) -> Call (namebis,b,c)
   |Elem(_) -> Elem(namebis)
;;




let is_elem a = match a with
  | Elem(_) -> true
  | _ -> false
;;

let is_synchro a = match a with
  | Synchronisation(_) -> true
  | _ -> false
;;
let is_qsynchro a = match a with
  | QSynchronisation(_) ->true
  | _ -> false
;;
let is_qchoice a = match a with
  | QChoice(_) ->true
  | _ -> false
;;
let is_automata a = match a with
  | Automata(_) ->true
  | _ -> false
;;

let rec find_subastd name astd_list = match astd_list with
  |(a::tail) ->begin debug ("find in sub astd "^name^" compare with "^(get_name a));
            if (get_name a)=name
                    then a
                    else begin (find_subastd name tail )  end  
            end
   |[]->failwith ("sub-astd : not found "^name) 
;;



(*let rec test_var_dom env var_dom_list = match var_dom_list with
	|(var,dom)::tail-> if (ASTD_constant.is_included (ASTD_term.extract_constant_from_term(ASTD_environment.find_value_of env var)) dom)
				then test_var_dom env tail
				else false
	|[]->true
*)

let _ASTD_astd_table_ = Hashtbl.create 5 
;;


let _ASTD_astd_call_table_ = Hashtbl.create 5 
;;


let _ASTD_astd_dom_table_ = Hashtbl.create 5 
;;

let register a = Hashtbl.add _ASTD_astd_table_ (get_name a) a  
;;

let register_call_astd a b= Hashtbl.add _ASTD_astd_call_table_ (get_name a) (a,b)  
;;



let get_astd name = Hashtbl.find _ASTD_astd_table_ name 
;;

let get_call_astd name = Hashtbl.find _ASTD_astd_call_table_ name 

(*let call_astd name env= let (astd,var_dom_list)= get_call_astd name
			in if (test_var_dom env var_dom_list )
				then astd
				else failwith "call impossible"
;;
*)

let save_transitions name l = begin ASTD_arrow.register_transitions_from_list name l; l end 


let rec replace_sub_astd sub_astd name astd_list = match astd_list with 
	|astd::tail->if (get_name astd)=name
			then sub_astd::tail
			else astd::(replace_sub_astd sub_astd name tail)
	|[]->failwith "replace impossible: doesn't exist"

let get_data_automata astd = match astd with
  |Automata(a,b,c,d,e,f) -> (a,b,c,d,e,f)
  |_-> failwith "not appropriate data automata"


let get_data_sequence astd = match astd with
  |Sequence(a,b,c) -> (a,b,c)
  |_-> failwith "not appropriate data seq "

let get_data_choice astd = match astd with
  |Choice(a,b,c) -> (a,b,c)
  |_-> failwith "not appropriate data choice"

let get_data_kleene astd = debug ("get_data_kleene : "^get_name astd) ; match astd with
  |Kleene(a,b) -> (a,b)
  |_-> failwith "not appropriate data kleene"

let get_data_synchronisation astd = match astd with
  |Synchronisation(a,b,c,d) -> (a,b,c,d)
  |_-> failwith "not appropriate data synch"

let get_data_guard astd = match astd with
  |Guard(a,b,c) -> (a,b,c)
  |_-> failwith "not appropriate data guard"

let get_data_qchoice astd = match astd with
  |QChoice(a,b,c,d) -> (a,b,c,d)
  |_-> failwith "not appropriate data qchoice"

let get_data_qsynchronisation astd = match astd with
  |QSynchronisation(a,b,c,d,f) -> (a,b,c,d,f)
  |_-> failwith "not appropriate data qsynch"

let get_data_call astd = match astd with
  |Call(a,b,c) -> (a,b,c)
  |_-> failwith "not appropriate data call"




let string_of name = name 
;;


let global_save_astd a b = (register a);(register_call_astd a b)
;;


let rec string_of_sons sons_list = match sons_list with
 |h::t -> let name = string_of(get_name h) in name^" "^(string_of_sons t) 
 |[] ->""
;;




