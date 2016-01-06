open ASTD_B;;
open ASTD_astd;;
open ASTD_arrow;;

(* A set structure for ASTD with lexicographic order *)
module ASTDSet = Set.Make(struct
                            type t = ASTD_astd.t
                            let compare a b = compare (get_name a) (get_name b)
                          end);;

(* Remove duplicates in a list *)
let rec removeDuplicates l =
  match l with
    | [] -> []
    | a::l -> if List.mem a l then removeDuplicates l else a::(removeDuplicates l)
    | _ -> failwith "removeDuplicates expects a list as argument"

(* Concat all ASTD names of a list of ASTD *)
let rec fromListToString l =
  match l with
    | [] -> ""
    | a::l -> (get_name a)^(fromListToString l)
    | _ -> failwith "fromListToString expects a list of ASTD as argument"

(* Return an equivalent automata where init state has only exit transitions
and no entry one. Init state must be an Elem ASTD *)
let rec isolateInitState automata =
  match automata with
    | Automata (astd_name, sub_astds, arrows, shallow_final_names, deep_final_names, init_name) ->
      match (find_subastd init_name (get_sub automata)) with
        | Elem (_) ->
          (* We change local and to_sub arrows targeting init state *)
          let isToTransform = 
            function arrow ->
              ((get_to arrow) = init_name) || ((is_to_sub arrow) && ((get_through arrow) = init_name))
          in
          let arrows_to_transform = List.filter isToTransform arrows in
          
          match arrows_to_transform with
            | [] -> automata (* Job completed *)
          	
            | a::l ->
              (* A new state is added for init state *)
              let init_bis_name = init_name^"Bis" in
              
              (* Rerouting the a arrow to the new state *)
              let rerouted_arrows = 
                let from_state = get_from a in
                let to_state = init_bis_name in
                ((local_arrow from_state to_state (get_transition a) (get_predicates a) (get_from_final_state a))
                  :: (List.filter (function arrow -> not(arrow = a)) (get_arrows automata)))
              in
              
              (* Adding to the new state the same successors as init state *)
              let new_arrows = 
                List.map (function arrow -> local_arrow init_bis_name (get_to arrow) (get_transition arrow) (get_predicates arrow) false)
                  (List.filter (function arrow -> (get_from arrow) = (get_to a)) (get_arrows automata))
              in
              
              let shallow_final = if List.mem (get_init automata) (get_shallow_final automata)
                                  then (removeDuplicates (init_bis_name::(get_shallow_final automata)))
                                  else (get_shallow_final automata)
              in
              
              (* Since a new state and new arrows are added each time there is an arrow
              to be transformed, we must remove duplicates in sub-ASTDs and arrows lists *)
              isolateInitState (automata_of   (get_name automata)
                                              (removeDuplicates ((elem_of init_bis_name)::(get_sub automata)))
                                              (removeDuplicates (rerouted_arrows@new_arrows))
                                              (shallow_final)
                                              (get_deep_final automata)
                                              (get_init automata))
        | _ -> failwith "isolateInitState called for a complex init state"
    | _ -> failwith "isolateInitState expects an automata ASTD as argument"

let rec kleeneClosure name automata =
  (* Simplifying init state to perform merging *)
  let automata = isolateInitState automata in
  
  (* Adding transitions from finals to init succesors *)
  let new_arrows = List.map (function final ->
                            List.map  (function arrow ->
                                        local_arrow final (get_to arrow) (get_transition arrow) (get_predicates arrow) false)
                                      (List.filter  (function arrow -> (get_from arrow) = (get_init automata))
                                                    (get_arrows automata)
                                      )
                            )
                            (get_shallow_final automata)
  in
  let arrows = removeDuplicates ((List.concat new_arrows)@(get_arrows automata)) in
  
  automata_of name (get_sub automata) arrows ((get_init automata)::(get_shallow_final automata)) [] (get_init automata)



(* Check if an automata and a sub automata can be merged.

True if automata and sub_automata are automata,
sub_automata hasn't from_sub or to_sub arrows,
and there are only final transitions, from_sub and to_sub arrows
between automata and sub_automata. *)
let canBeMerged automata sub_automata =
  if((is_automata automata) && (is_automata sub_automata)) then
    not(List.exists (function arrow -> (is_from_sub arrow) || (is_to_sub arrow)) (get_arrows sub_automata))
    && not(List.exists (function arrow -> 
                        (* there are only final transitions between automata and sub_automata *)
                        not(get_from_final_state arrow) && ((get_from arrow) = (get_name sub_automata)))
                       (get_arrows automata))
  else
    false

(* Merge relevant automata and sub automatas *)
let rec mergeSubAutomatas automata =
  let sub_astds = get_sub automata in
  let mergeable_subs = List.filter (function astd -> canBeMerged automata astd) sub_astds in
  
  match mergeable_subs with
    | [] -> automata
    | a::l ->
      (* All sub automata states are added to automata *)
      let new_elems = get_sub a in
      
      (* Defining a function that reroute concerning arrows when merging sub automatas *)
      let rerouteArrow arrow =
        if (get_from arrow) = (get_name a) || (get_to arrow) = (get_name a) || ((is_to_sub arrow || (is_from_sub arrow)) && (get_through arrow) = (get_name a)) then
          match arrow with
            | Local (from_name, to_name, transition, predicates, is_final) ->
              if (get_from arrow) = (get_name a) then
                (* It is a final transition from sub automata, we create new arrows from all final states of sub automata *)
                List.map (function state -> local_arrow (get_name state) to_name transition predicates true)
                  (List.filter (function state -> List.mem (get_name state) ((get_shallow_final a)@(get_deep_final a))) (get_sub a))
              else (* i.e. the arrow is targeting the automata a *)
                (* We route the arrow to the init state of sub automata *)
                [local_arrow from_name (get_init a) transition predicates is_final]
                
            | From_sub (from_name, to_name, through_name, transition, predicates, is_final) ->
              if through_name = (get_name a) then
                [local_arrow from_name to_name transition predicates is_final]
              else
                [local_arrow from_name (get_init a) transition predicates is_final]
                
            | To_sub (from_name, to_name, through_name, transition, predicates, is_final) ->
              if through_name = (get_name a) then
                [local_arrow from_name to_name transition predicates is_final]
              else (* final transition from automata a to a sub *)
                List.map (function state -> local_arrow (get_name state) to_name transition predicates true)
                  (List.filter (function state -> List.mem (get_name state) ((get_shallow_final a)@(get_deep_final a))) (get_sub a))
        else
          [arrow]
      in
      
      let elems = new_elems@(List.filter (function astd -> not(astd = a)) sub_astds) in
      let arrows = (get_arrows a)@(List.concat (List.map rerouteArrow (get_arrows automata))) in
      
      (* Changing init if it was a complex state which has been flattened *)
      let init_name = if (get_init automata) = (get_name a) then get_init a else get_init automata in
      
      let shallow_final =
        (* If a was a shallow final state, all its elements are now shallow final states *)
        if List.mem (get_name a) (get_shallow_final automata) then
          (List.map get_name (get_sub a))
          @ (List.filter (function elem -> not((get_name a) = elem)) (get_shallow_final automata))
        (* If it was a deep final state, its final elements are now shallow final states *)
        else if List.mem (get_name a) (get_deep_final automata) then
          (get_deep_final a) @ (get_shallow_final a) @ (get_shallow_final automata)
        else
          (get_shallow_final automata)
      in
      
      let deep_final = List.filter (function elem -> not((get_name a) = elem)) (get_deep_final automata) in
      
      (* Recursive call to merge other sub automatas *)
      mergeSubAutomatas (automata_of  (get_name automata)
                                      elems
                                      arrows
                                      (get_shallow_final automata)
                                      (get_deep_final automata)
                                      init_name)

(* Loop of the determinization algorithm *)
let rec determinize_step nfa dfa stack =
  (* stack is the next states to transform *)
  match stack with
    | [] -> dfa
    | a::l ->
      let arrows = List.filter (function arrow -> List.mem (get_from arrow) (List.map get_name (ASTDSet.elements a))) (get_arrows nfa) in
      let arrow_types = List.map (function arrow -> ((get_transition arrow), (get_predicates arrow))) arrows in
      let arrow_types = removeDuplicates arrow_types in
      let list_of_new_elems = 
        List.map (  function arrow_type ->
                      (* Storing all successors of a in a list *)
                      let destinations_list = (
                        List.map (function arrow -> find_subastd (get_to arrow) (get_sub nfa))
                          (List.filter (function arrow -> 
                            if (get_transition arrow) = (fst arrow_type) && (get_predicates arrow) = (snd arrow_type) then
                              true
                            else
                              false
                            )
                            arrows
                          )
                        )
                      in
                      (* Creating a set out of the list *)
                      List.fold_right ASTDSet.add destinations_list ASTDSet.empty
                  ) arrow_types
        in
      let new_stack_elems = List.filter (function elem_set -> not(List.mem (fromListToString (ASTDSet.elements elem_set)) (List.map get_name (get_sub dfa)))) (removeDuplicates list_of_new_elems) in
      let new_arrows = 
        List.map (  function arrow_type ->
                      let destinations_list = (
                        List.map (function arrow -> find_subastd (get_to arrow) (get_sub nfa))
                          (List.filter (function arrow -> 
                            if (get_transition arrow) = (fst arrow_type) && (get_predicates arrow) = (snd arrow_type) then
                              true
                            else
                              false
                            )
                            arrows
                          )
                        )
                      in
                      let destinations_set = ASTDSet.elements (List.fold_right ASTDSet.add destinations_list ASTDSet.empty) in
                      local_arrow (fromListToString (ASTDSet.elements a)) (fromListToString destinations_set) (fst arrow_type) (snd arrow_type) false
                  ) arrow_types
      in
      let new_shallow_final = List.filter (function elem -> List.exists (function e -> List.mem (get_name e) (get_shallow_final nfa)) (ASTDSet.elements elem)) new_stack_elems in
      let new_deep_final = List.filter (function elem -> List.exists (function e -> List.mem (get_name e) (get_deep_final nfa)) (ASTDSet.elements elem)) new_stack_elems in
      let dfa = automata_of (get_name dfa)
                            ((get_sub dfa)@(List.map (function elem -> elem_of (fromListToString (ASTDSet.elements elem))) new_stack_elems))
                            ((get_arrows dfa)@new_arrows)
                            ((get_shallow_final dfa)@(List.map (function elem -> fromListToString (ASTDSet.elements elem)) new_shallow_final))
                            ((get_deep_final dfa)@(List.map (function elem -> fromListToString (ASTDSet.elements elem)) new_deep_final))
                            (get_init dfa)
      in
      determinize_step nfa dfa (l@new_stack_elems)


let determinize nfa =
  (* Initialization of the recursive algorithm *)
  let shallow_final = if List.mem (get_init nfa) (get_shallow_final nfa) then [get_init nfa] else [] in
  let deep_final = if List.mem (get_init nfa) (get_deep_final nfa) then [get_init nfa] else [] in
  let dfa = automata_of (get_name nfa)
                        [elem_of (get_init nfa)]
                        []
                        shallow_final
                        deep_final
                        (get_init nfa)
  in
  determinize_step nfa dfa [ASTDSet.singleton (find_subastd (get_init nfa) (get_sub nfa))]


let choiceTransform name left_astd right_astd =
  (* Creating a unique init state *)
  let new_init_name = (get_init left_astd)^(get_init right_astd) in
  let new_init = elem_of new_init_name in
  
  (* Adding this state and removing former init states *)
  let elems = new_init :: (List.filter  (function state -> 
                                        (get_name state) != (get_init left_astd) && (get_name state) != (get_init right_astd)
                                        )
                                        ((get_sub left_astd)@(get_sub right_astd)))
  in
  
  (* Rerouting arrows from former init states *)
  let new_arrows = List.map (function a -> local_arrow new_init_name (get_to a) (get_transition a) (get_predicates a) false)
                            (List.filter (function a -> ((get_from a) = (get_init left_astd) || (get_from a) = (get_init right_astd)))
                                          ((get_arrows left_astd)@(get_arrows right_astd)))
  in
  (* Modifying arrows targetting former init states *)
  let modified_arrows = List.map (function a -> local_arrow (get_from a) new_init_name (get_transition a) (get_predicates a) false)
                                 (List.filter (function a -> ((get_to a) = (get_init left_astd)) || ((get_to a) = (get_init right_astd)))
                                              ((get_arrows left_astd)@(get_arrows right_astd)))
  in
  let unchanged_arrows = (List.filter (function a -> not((get_from a) = (get_init left_astd) || (get_from a) = (get_init right_astd) || (get_to a) = (get_init left_astd) || (get_to a) = (get_init right_astd)))
                      ((get_arrows left_astd)@(get_arrows right_astd)))
  in
  let arrows = new_arrows @ modified_arrows @ unchanged_arrows in
  automata_of name elems arrows ((get_shallow_final left_astd)@(get_shallow_final right_astd)) [] new_init_name

let rec minimize astd = 
	match astd with
    | Elem (astd_name) -> elem_of astd_name
    
    | Automata (astd_name, sub_astds, arrows, shallow_final_names, deep_final_names, init_name) ->
      let min_sub_astds = List.map minimize sub_astds in (* Now all sub ASTDs are Elem or Automata with Elem sub ASTDs *)
      let nfa = mergeSubAutomatas (automata_of astd_name min_sub_astds arrows shallow_final_names deep_final_names init_name) in
      nfa
      
    | Sequence (astd_name, left_sub_astd, right_sub_astd) -> sequence_of astd_name (minimize left_sub_astd) (minimize right_sub_astd)

    | Choice (astd_name, left_sub_astd, right_sub_astd) -> 
      let min_left = minimize left_sub_astd in
      let min_right = minimize right_sub_astd in
      if (is_automata min_left) && (is_automata min_right) then
        determinize (choiceTransform astd_name min_left min_right)
      else
        choice_of astd_name min_left min_right

    | Kleene (astd_name, sub_astd) ->
      let min_sub_astd = minimize sub_astd in
      (* Performing kleene transform only if sub astd is an automata... *) 
      if is_automata min_sub_astd then
        let init_state = find_subastd (get_init min_sub_astd) (get_sub min_sub_astd) in
        (* ... and its init state is an Elem ASTD *)
        if is_elem init_state then
          kleeneClosure (get_name min_sub_astd) min_sub_astd
        else
          kleene_of astd_name min_sub_astd
      else
        kleene_of astd_name min_sub_astd

    | Synchronisation (astd_name, transition_labels, left_sub_astd, right_sub_astd) ->
      synchronisation_of astd_name transition_labels (minimize left_sub_astd) (minimize right_sub_astd)
    
    | Fork (astd_name, transition_labels, predicates, left_sub_astd, right_sub_astd) ->
      fork_of astd_name transition_labels predicates (minimize left_sub_astd) (minimize right_sub_astd)
    
    | QChoice (astd_name, variable, domain, sub_astd) ->
      QChoice (astd_name, variable, domain, minimize sub_astd)

    | QSynchronisation (astd_name, variable, domain, transition_labels, sub_astd) ->
      QSynchronisation (astd_name, variable, domain, transition_labels, minimize sub_astd)

    | QFork  (astd_name, variable, domain, predicates, transition_labels, sub_astd) ->
      QFork  (astd_name, variable, domain, predicates, transition_labels, minimize sub_astd)

    | Guard (astd_name, predicates, sub_astd) -> astd

    | Call (astd_name, called_astd_name, var_values_vector) -> astd
    
    | _ -> failwith "minimize argument must be an ASTD"

	
