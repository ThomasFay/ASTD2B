type position = string
type step = Fst | Snd
type side = Undef | Left | Right
type qchoice = Val of ASTD_term.t | ChoiceNotMade
type astd_name = string
type called_path =astd_name list

type t = Automata_s of position * ((astd_name * t) list) * t
        |Sequence_s of step * t
        |Choice_s of side * t
        |Kleene_s of bool * t
        |Synchronisation_s of t * t
        |QChoice_s of qchoice *(ASTD_constant.domain)* (ASTD_constant.domain) * t
        |QSynchronisation_s  of (ASTD_constant.domain)* (ASTD_constant.domain) * (ASTD_constant.domain) * t
        |Guard_s of bool * t
        |Call_s of bool * t
        |NotDefined
        |Elem
;;



    let val_debug = ref false;;
    let debug m = if (!val_debug) 
                            then (print_endline m )
                            else begin end;;
    let debug_on () = (val_debug := true);;
    
    let val_debug_hash = false ;;
    let debug_hash m = if (val_debug_hash) 
                            then (print_endline m )
                            else begin end;;



let automata_s_of pos hist current = Automata_s (pos,hist,current);;
let sequence_s_of step current = Sequence_s (step,current);;
let choice_s_of side current = Choice_s (side,current);;
let kleene_s_of started current = Kleene_s (started,current);;
let synchronisation_s_of first second = Synchronisation_s (first,second);;
let qchoice_s_of choice final_dom unknown_dom current = QChoice_s (choice,final_dom,unknown_dom,current);;
let qsynchronisation_s_of not_fin_dom unknown_dom init_dom init =  QSynchronisation_s (not_fin_dom,unknown_dom,init_dom,init);;
let guard_s_of condition current = Guard_s (condition,current);;
let call_s_of called current = Call_s (called,current);;
let not_defined_state () = NotDefined;;
let elem_state () =Elem;;


let undef_choice_of () = Undef;;
let left_choice_of () = Left;;
let right_choice_of () = Right;;

let first_sequence_of () =Fst;;
let second_sequence_of () =Snd;;

let qchoice_notmade_of () = ChoiceNotMade


let get_pos state = match state with
 |Automata_s (a,b,c) -> a
 |_ -> failwith "not an automata"
;;


let is_automata state = match state with
 |Automata_s(_,_,_) -> true
 |_-> false


let is_qsynchro state = match state with
 |QSynchronisation_s(_) -> true
 |_-> false


let get_data_from_qsynchro state = match state with
  |QSynchronisation_s(p,q,r,s) -> (p,q,r,s)
  |_-> failwith "not appropriate use of get_data_from_qsynchro" 

let get_data_automata_s state = match state with
  |Automata_s(a,b,c) -> (a,b,c)
  |_-> failwith "not an automata in get_data_automata_s" 



let get_val choice = match choice with
 |Val(a) -> a 
 |ChoiceNotMade -> failwith "not a value"
;;


let val_of a = Val (a);;


let rec study_comparison arg params = match (arg,params) with
 |((ASTD_term.Const a)::b,c::d)->if c = a then study_comparison b d
                                          else false
 |(a::b,c::d)-> study_comparison b d
 |([],[])-> true
 |_->failwith "parameters and arguments should have the same number" 


let correspond trans event = if ((ASTD_transition.get_label trans)=(ASTD_event.get_label event))
                                then (study_comparison (ASTD_transition.get_params trans) (ASTD_event.get_const event))
                                else false
                             
 

let rec get_val_arrow a_list event = match a_list with
  | (trans,v_list)::t -> if (correspond (trans) (event)) 
                                                     then ASTD_constant.fusion v_list (get_val_arrow t event) 
                                                     else  (get_val_arrow t event) 
  | [] -> ASTD_constant.empty_dom
;;



let rec get_labels arrows = match arrows with
  |(h1,h2)::t-> h1::(get_labels t)
  |[]->[]





let _ASTD_synch_table_ = Hashtbl.create 5 



(*let register_synch name value env call_path state = Hashtbl.add _ASTD_synch_table_ (name,value,env,call_path) state*) (**opt: remove state*)

let rec remove_all key opt_const astd= 
		if Hashtbl.mem _ASTD_synch_table_ (key,opt_const)
			then begin debug_hash ("remove all at"^key);
				Hashtbl.remove _ASTD_synch_table_ (key,opt_const);
				remove_all key opt_const astd
				end
			else begin end

let register_synch key opt_const state astd= 
                                debug_hash ("HASH register at "^key);
                                remove_all key opt_const astd;
                                Hashtbl.add _ASTD_synch_table_ (key,opt_const) state


let get_synch key opt_const astd= begin 
                                        debug_hash ("HASH extract at "^key);
                                        Hashtbl.find _ASTD_synch_table_ (key, opt_const) 
                                        end
                        
let get_synch_state not_init_dom init key opt_const astd=debug_hash ("extract at "^key^" or init");
                                                        let value = begin match opt_const with |Some c -> c | None -> failwith "No value in get_synch" end
							in if (ASTD_constant.is_included value not_init_dom)
                                                        	then Hashtbl.find _ASTD_synch_table_ (key,opt_const)
                                                         	else init


let rec save_data to_save = match to_save with
        |((key,opt_const),astd,state,add)::t-> 
			if add
			then begin
                                register_synch key opt_const state astd; 
                                save_data t
                                end
			else begin debug "remove all";
                                remove_all key opt_const astd;
                                save_data t
                                end
        |[]->begin end




let string_of_bool a = if a then "true" else "false"
;;



let string_of_seq a = match a with
  |Fst -> "First"
  |Snd -> "Second"

let string_of_choice a = match a with
  |Left -> "First"
  |Right -> "Second"
  |Undef -> "Choice not made yet"

let string_of_qchoice a=match a with
 |Val(v) -> ASTD_term.string_of v
 |ChoiceNotMade -> "Choice not made yet"
;;







  
