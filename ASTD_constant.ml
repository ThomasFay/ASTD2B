open Functions

(* type domain = string *)

(* type set_name = string  *)

(* type t = | Integer of int *)
(*          | Symbol of string *)
(*          | FreeConst *)

(* let string_of n = match n with *)
(*   |Symbol a -> a *)
(*   |_-> failwith "should be used with a constant symbol" *)
(* ;; *)

(* let of_int n = Integer n;; *)

(* let rec contain_free l =match l with *)
(* |FreeConst::t->true *)
(* |a::t->contain_free t *)
(* |[]->false *)



(* let string_of_list = create_string_of_list string_of *)




type t = | Integer of int
         | Symbol of string
         | FreeConst



let compare_constant c1 c2 = match (c1,c2) with
    | (Integer n1, Integer n2) -> compare n1 n2
    | (Symbol s1, Symbol s2) -> compare s1 s2
    | _ -> -1

type a_constant = t
module Set_of = Set.Make( struct type t = a_constant (*** constant = t *)
                                 let compare = compare_constant
                          end) 

type set_name = string 
type set = Set_of.t








let of_int n = Integer n

let int_of n = match n with
  |Integer a -> a
  |_-> failwith "should be used with a constant integer"
;;

let string_of n = match n with
  |Symbol a -> a
  |_-> failwith "should be used with a constant symbol"
;;

let empty_set = Set_of.empty

let constant_set_from_list  = 
    let add_to_s s elt = Set_of.add elt s
    in List.fold_left add_to_s empty_set 

let constant_set_from_range ~min ~max = 
    let rec add_next n s = if n > max
                           then s
                           else add_next (n+1) (Set_of.add (of_int n) s) 
                           in
                               add_next min (empty_set:set)


let fold_set = Set_of.fold
let iteration_over_set = Set_of.iter 
let for_all_constants = Set_of.for_all 
let exists_a_constant = Set_of.exists 
let member = Set_of.mem
let choose_in = Set_of.choose
let add_in = Set_of.add
let remove_from = Set_of.remove
let union = Set_of.union
let is_empty = Set_of.is_empty

let print = function
    | Integer n -> print_int n
    | Symbol s -> print_string s
    | FreeConst -> print_string "Free value"

let print_list = create_print_list print

let print_set_name n = print_string n

let print_set = create_print_set iteration_over_set print

let string_of = function
    | Integer n -> string_of_int n
    | Symbol s -> s
    | FreeConst -> "Free value"

let string_of_list = create_string_of_list string_of

let string_of_set_name n = n

let string_of_set = create_string_of_set fold_set string_of






(**                    Value type                                                                  *)
type value = | Range of (int * int)
             | Val of t
             | FreeVal
	     | FreeSet of string


let compare_val c1 c2 = match (c1,c2) with
    | (Val(Integer n1), Val(Integer n2)) -> compare n1 n2
    | (Val(Symbol s1), Val(Symbol s2)) -> compare s1 s2
    | (Range(a,b),Range(c,d))-> if a=c then compare b d
                                       else compare a c
    | (Val(Integer n1), Range(a,b))->if n1=a then compare n1 (a+1)
                                             else compare n1 a
    | (Range(a,b),Val(Integer n1))->if n1=a then compare (a+1) n1
                                             else compare a n1
    | _ -> -1

module Domain = Set.Make( struct type t = value
                                 let compare = compare_val
                          end) 

  (*type domain=Domain.t*)

type domain=Domain.t

let val_to_int a = match a with
  |Val(Integer v)-> v
  |_-> failwith "should be used with a number"
;;

let val_to_string a = match a with
  |Val(Symbol s) ->s
  |_-> failwith "should be used with a string"


let range_of a b = if a<b then Range(a,b)
                          else failwith "in a range(a,b), we sould have a<b"
;;

let value_of a= match a with
     |Symbol b -> Val a
     |Integer b -> Val a
     |FreeConst -> FreeVal
;;




let val_to_const a=match a with
|Val(a)->a
|_->failwith "not appropriate use of val_to_const"



let int_of_val a=match a with
|Val(Integer a)->a
|_->failwith "not appropriate use of int_of_val"

let string_of_val a=match a with
|Val(Symbol a)-> a
|_->failwith "not appropriate use of int_of_val"


let kind_of_val a = match a with
|Integer b -> true
|Symbol b -> false
|_->failwith "whatever the value"



let rec contain_free l =match l with
|FreeConst::t->true
|a::t->contain_free t
|[]->false


(**                         Domain type                                       *)





let empty_dom = Domain.empty

let is_empty_dom = Domain.is_empty 

let create_dom_from_val value= Domain.add value empty_dom


let get_first_tail dom = if is_empty_dom dom
                         then failwith "first_tail impossible : empty dom"
                         else let first = Domain.min_elt dom 
                              in (first,Domain.remove first dom)




let suppression_from_max_of_inf to_modify elem = match (to_modify,elem) with
  |(Range(a,b),Val(Integer i))-> 
                    if b<i
                    then (Domain.add (Range(a,b)) (Domain.empty))
                    else if i=b 
                         then if a=b-1 
                              then (Domain.add (Val(Integer a)) (Domain.empty))
                              else (Domain.add (Range(a,b-1)) (Domain.empty))
                         else if i=b-1 
                              then if a=i-1 
                                   then (Domain.add (Val(Integer a)) (Domain.add (Val(Integer b)) (Domain.empty)))
                                   else (Domain.add (Range(a,i-1)) (Domain.add (Val(Integer b)) (Domain.empty)))
                              else if a+1=i 
                                   then (Domain.add (Val(Integer a)) (Domain.add (Range(i+1,b)) (Domain.empty)))
                                   else (Domain.add (Range(a,i-1)) (Domain.add (Range(i+1,b)) (Domain.empty)))
(*Nb, le cas i=a n'est pas à envisager puisque range<val ici et que si i=a, on a range>val *)

  |(Range(a,b),Range(c,d))->
          if  a=c 
          then (*cas b<d*) (Domain.empty)
          else (*a<c*) if b<c 
                       then (Domain.add (Range(a,b)) (Domain.empty))
                       else if d<b 
                            then if c=a+1
                                 then if d=b-1
                                      then (Domain.add (Val(Integer a)) (Domain.add (Val(Integer b)) (Domain.empty)))
                                      else (Domain.add (Val(Integer a)) (Domain.add (Range(d+1,b)) (Domain.empty)))
                                 else if d=b-1
                                      then (Domain.add (Range(a,c-1)) (Domain.add (Val(Integer b)) (Domain.empty)))
                                      else (Domain.add (Range(a,c-1)) (Domain.add (Range(d+1,b)) (Domain.empty)))
                            else if c=a+1
                                 then (Domain.add (Val(Integer a)) (Domain.empty))
                                 else (Domain.add (Range(a,c-1)) (Domain.empty))



  |(Val(Integer i),Val(Integer j))-> (Domain.add (Val(Integer i)) (Domain.empty))

  |(Val(Integer i),Range(a,b))-> if i<a 
                                    then (Domain.add (Val(Integer i)) (Domain.empty))
                                    else (*cas i=a*) if a+1=b 
                                                     then (Domain.add (Val(Integer b)) (Domain.empty))
                                                     else (Domain.add (Range(a+1,b)) (Domain.empty))

  |(Val(Symbol s),Val(Symbol t))-> (Domain.add (Val(Symbol s)) (Domain.empty))
  |_->failwith "supression from max of inferior impossible"
;;




let suppression_from_min_of_sup to_modify elem = match (elem,to_modify) with 
  |(Range(a,b),Val(Integer i))-> (*cas i>a*) if i<=b then (Domain.empty,false)
                                                     else ((Domain.add (Val(Integer i)) (Domain.empty)),true)

  |(Range(a,b),Range(c,d))-> (*cas c >= a*)if c > b 
                                           then (Domain.add (Range(c,d)) (Domain.empty),true)
                                           else if d>b
                                                then if d=b+1 
                                                     then (Domain.add (Val(Integer d)) (Domain.empty),true)
                                                     else (Domain.add (Range(b+1,d)) (Domain.empty),true)
                                                else (Domain.empty,false)
  |(Val(Integer i),Val(Integer j))-> ((Domain.add (Val(Integer j)) (Domain.empty)),true)
  |(Val(Integer i),Range(a,b))-> (*cas i<=a*) if i=a then if b=a+1 then (Domain.add (Val(Integer b)) (Domain.empty),true)
                                                                   else (Domain.add (Range(a+1,b)) (Domain.empty),true)
                                                     else (Domain.add (Range(a,b)) (Domain.empty),true)
  |(Val(Symbol s),Val(Symbol t))-> ((Domain.add (Val(Symbol t)) (Domain.empty)),true)
  |_->failwith "supression from min of superior impossible"
;;



let rec suppression_from_sup superior elem =
if (is_empty_dom superior)
   then empty_dom
   else let to_modify=Domain.min_elt superior
        in let sup=(Domain.remove to_modify superior)
        in let (value,removed)=suppression_from_min_of_sup to_modify elem
        in if removed then (Domain.union value sup)
                      else (suppression_from_sup sup elem) 



let rec remove_domain_from elem_list dom = begin 
                                   let (elem,tail)=get_first_tail elem_list
                                   in let (inferior,is_included,superior)=(Domain.split elem dom)
                                   in if is_included 
                                      then if Domain.is_empty tail 
                                           then (Domain.union inferior superior)
                                           else remove_domain_from tail (Domain.union inferior superior)
                                      else let new_inf = begin 
                                                    if Domain.is_empty inferior 
                                                    then Domain.empty 
                                                    else let to_modify=Domain.max_elt inferior
                                                         in let inf=(Domain.remove to_modify inferior)
                                                         in (Domain.union inf (suppression_from_max_of_inf to_modify elem))
                                                         end
                                           and new_sup = suppression_from_sup superior elem
                                           in if Domain.is_empty tail 
                                              then (Domain.union new_inf new_sup)
                                              else remove_domain_from tail (Domain.union new_inf new_sup)
                                           end


let remove elem dom = 
             remove_domain_from ( create_dom_from_val elem ) dom;;



let fusion_with_max_of_inf to_modify elem = match (to_modify,elem) with
  |(Range(a,b),Val(Integer i))-> (*cas i>a*) if i>b+1 
                                             then (elem,false)
                                             else if i=b+1
                                                  then (Range(a,i),true)
                                                  else (Range(a,b),true)
  |(Range(a,b),Range(c,d))-> (*cas c >= a*) if c > b+1 
                                            then (elem,false)
                                            else if d>b
                                                 then (Range(a,d),true)
                                                 else (Range(a,b),true)
  |(Val(Integer i),Val(Integer j))-> (*cas i<j*) if j=i+1 then (Range(i,j),true)
                                                          else(elem,false)
  |(Val(Integer i),Range(a,b))-> (*cas i<=a*) if i>=a-1 then (Range(i,b),true)
                                                     else (elem,false)
  |(Val(Symbol s),Val(Symbol t))-> (*cas s<t*) (elem,false)
  |_->failwith "fusion with max of inferior impossible"
;;


let fusion_with_min_of_sup to_modify elem = match (elem,to_modify) with
  |(Range(a,b),Val(Integer i))-> (*cas i>a*) if i>b+1 
                                             then (elem,false)
                                             else if i=b+1
                                                  then (Range(a,i),true)
                                                  else (Range(a,b),true)
  |(Range(a,b),Range(c,d))-> (*cas c >= a*) if c > b+1 
                                            then (elem,false)
                                            else if d>b
                                                 then (Range(a,d),true)
                                                 else (Range(a,b),true)
  |(Val(Integer i),Val(Integer j))-> (*cas i<j*) if j=i+1 then (Range(i,j),true)
                                                          else(elem,false)
  |(Val(Integer i),Range(a,b))-> (*cas i<=a*) if i>=a-1 then (Range(i,b),true)
                                                     else (elem,false)
  |(Val(Symbol s),Val(Symbol t))-> (*cas s<t*) (elem,false)
  |_->failwith "fusion with min of superior impossible"
;;





let rec fusion_with_sup superior elem =
if is_empty_dom superior
   then create_dom_from_val elem
   else let to_modify=Domain.min_elt superior
        in let (new_elem,modified)=fusion_with_min_of_sup to_modify elem
        in if modified
           then (fusion_with_sup (Domain.remove to_modify superior) new_elem) 
           else (Domain.union (Domain.add new_elem (Domain.empty)) superior)







let rec fusion elem_list dom =
                let (elem,tail)=get_first_tail elem_list
                in let (inferior,is_included,superior)=(Domain.split elem dom)
                in if is_included 
                   then if Domain.is_empty tail then dom
                                                else fusion tail dom
                   else if Domain.is_empty inferior
                        then fusion_with_sup superior elem
                        else let to_modify=Domain.max_elt inferior
                             in let (new_val,modified)=fusion_with_max_of_inf to_modify elem
                             in let new_sup=fusion_with_sup superior new_val
                             in if modified 
                                then if Domain.is_empty tail 
                                     then Domain.union (Domain.remove to_modify inferior) (new_sup)
                                     else fusion tail (Domain.union (Domain.remove to_modify inferior) (new_sup))
                                else if Domain.is_empty tail 
                                     then Domain.union inferior (new_sup)
                                     else fusion tail (Domain.union inferior (new_sup))
                                                


let insert elem dom = 
             fusion ( create_dom_from_val elem ) dom;;


let rec map_dom funct dom=
           if Domain.is_empty dom then [] else
           let head=Domain.min_elt dom
           in let tail =Domain.remove head dom
           	in (funct(head))::(map_dom funct tail)


let head_tail d =if (is_empty_dom d)
                    then failwith "head_tail impossible : empty dom"
                    else let v =Domain.min_elt d 
                         in match v with 
                          |Val(a) -> (a,Domain.remove v d)
                          |Range(a,b)->(Integer a,remove (Val(Integer a)) d )
                          |FreeVal->failwith"head_tail is impossible to use with freeval"


let is_included_elem elem value = match value with
  |Range(a,b)-> ((int_of elem)>=a)&&((int_of elem)<=b)
  |_->false


let print_value v s = match v with
 |Val(Integer i)->s^"/"^("Value "^(string_of_int i))
 |Val(Symbol s)-> s^"/"^("Value "^(s))
 |Val(FreeConst)-> s^"/"^("FreeConst")
 |Range(a,b)-> s^"/"^("Range "^(string_of_int a)^"-"^(string_of_int b))
 |FreeVal->s^"FreeValue"
;;


let print_dom d = if is_empty_dom d then "empty domain"
                                    else Domain.fold (print_value) d ""





let rec is_included elem dom =  
               begin 
                let value=Val(elem) 
                in let (inf,is_in,sup)=Domain.split value dom
                in if is_in 
                   then true
                   else if (is_empty_dom inf)
                        then if (is_empty_dom sup)
                             then false
                             else begin 
                                    (is_included_elem elem (Domain.min_elt sup)) 
                                  end
                        else if (is_empty_dom sup)
                             then (is_included_elem elem (Domain.max_elt inf))
                             else (is_included_elem elem (Domain.max_elt inf))||(is_included_elem elem (Domain.min_elt sup))
               end





