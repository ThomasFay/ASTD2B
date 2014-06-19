type from_state = string
type to_state = string
type through_state = string
type from_final_state = bool


type t = Local of from_state * to_state * ASTD_transition.t * ASTD_predicate.t list * from_final_state
|From_sub of from_state * to_state * through_state * ASTD_transition.t * ASTD_predicate.t list * from_final_state
|To_sub of from_state * to_state * through_state * ASTD_transition.t * ASTD_predicate.t list * from_final_state





exception ASTD_free_variable of ASTD_term.t * t






let _ASTD_arrow_table_ = Hashtbl.create 5 

let _ASTD_transition_table_ = Hashtbl.create 5 




let local_arrow from_state to_state transition predicates from_final_state =           
                                    Local(from_state,to_state,transition,predicates,from_final_state)
let fsub_arrow from_state to_state through_state transition predicates from_final_state =           
                                    From_sub(from_state,to_state,through_state,transition,predicates,from_final_state)
let tsub_arrow from_state to_state through_state transition predicates from_final_state =           
                                    To_sub(from_state,to_state,through_state,transition,predicates,from_final_state)


let is_from_sub a = match a with
  | From_sub(_) ->true
  | _ -> false
let is_to_sub a = match a with
  | To_sub(_) ->true
  | _ -> false
let is_local a = match a with
  | Local(_) ->true
  | _ -> false




let get_from arrow = match arrow with
     | Local ( from,_,_,_,_ ) -> from
     | From_sub ( from,_,_,_,_,_ ) -> from
     | To_sub ( from,_,_,_,_,_ ) -> from
let get_to arrow = match arrow with
     | Local ( _,dest,_,_,_ ) -> dest
     | From_sub ( _,dest,_,_,_,_ ) -> dest
     | To_sub ( _,dest,_,_,_,_ ) -> dest
let get_through arrow = match arrow with
     | From_sub ( _,_,through,_,_,_ ) -> through
     | To_sub ( _,_,through,_,_,_ ) -> through
     | _ -> failwith "no throught for local transitions"
let get_transition arrow = match arrow with
     | Local ( _,_,transitions,_,_ ) -> transitions
     | From_sub ( _,_,_,transitions,_,_ ) -> transitions
     | To_sub ( _,_,_,transitions,_,_ ) -> transitions
let get_predicates arrow = match arrow with
     | Local ( _,_,_,predicates,_ ) -> predicates
     | From_sub ( _,_,_,_,predicates,_ ) -> predicates
     | To_sub ( _,_,_,_,predicates,_ ) -> predicates
let get_from_final_state arrow = match arrow with
     | Local ( _,_,_,_,should_be_final ) -> should_be_final
     | From_sub ( _,_,_,_,_,should_be_final ) -> should_be_final
     | To_sub ( _,_,_,_,_,should_be_final ) -> should_be_final
let get_label_transition arrow =   ASTD_transition.get_label(get_transition arrow)






let register_transition name transition = match transition with
     |ASTD_transition.Transition(label,params) ->  Hashtbl.add _ASTD_transition_table_ (name,label) params

let rec register_transitions_from_list name transition_list = match transition_list with
     |(ASTD_transition.Transition(label,params))::t ->begin
                                                      Hashtbl.add _ASTD_transition_table_ (name,label) params;
                                                      register_transitions_from_list name t
                                                      end
     |[]->()

let get_transition_params name label =  Hashtbl.find_all _ASTD_transition_table_ (name,label)





let register = Hashtbl.add _ASTD_arrow_table_ 

(*let register_arrow arrow name= match arrow with
     | Local ( from,to_state,transition,pred,final ) ->
                                               register (from,name,ASTD_transition.get_label transition,final) arrow
     | From_sub ( from,to_state,through,transition,pred,final ) ->
                                               register (through,name,ASTD_transition.get_label transition,final) arrow
     | To_sub ( from,to_state,through,transition,pred,final ) -> 
                                               register (through,name,ASTD_transition.get_label transition,final) arrow

let get from event from_final name= Hashtbl.find_all _ASTD_arrow_table_ (from,name,(ASTD_event.get_label event),from_final)
*)





let rec evaluate_guard env predicate_list = 
begin 
    match predicate_list with
    |predicate::tail -> begin 
                 ((evaluate_guard env tail) && (ASTD_predicate.evaluate predicate env)) 
                end
    |[] -> true
end


let rec estimate_guard env predicate_list = 
begin 
    match predicate_list with
    |predicate::tail -> begin 
                 ((estimate_guard env tail) && (ASTD_predicate.estimate predicate env)) 
                end
    |[] -> true
end



let valid_arrow event env arrow = let is_valid =
                                     (
                                      (begin let c= (ASTD_event.compare_action_with_event2 env (get_transition arrow) event)
                                             in begin 
                                                      c
                                                end 
                                       end)
                                      && 
                                      (begin let b= evaluate_guard env (get_predicates arrow)
                                             in begin
                                                      b
                                                end 
                                       end)
                                     )
                                  in is_valid
;;





