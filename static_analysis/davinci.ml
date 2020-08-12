(*
 * SNU 4541.664A Program Analysis 2019 Fall
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 *)


(*
 * Chanhee Cho (cksgml@snu.ac.kr) 
 * In this approach, there are two stages.
 * At first, pre-analysis simplies definite branch and produce simplied program
 * e.g. if(1) c1 c2  to c1,   while(0) do c  to  skip
 * Next, we do main-analysis using power set domain of remainders
 *)
 
open Program 
open DomFunctor

exception Error of string
 
type result =
  | YES
  | NO
  | DONTKNOW

let result_to_str : result -> string = fun a -> match a with
  | YES -> "Yes, it is davinci code"
  | NO -> "No, it is not davinci code"
  | DONTKNOW -> "I don't know"
  
let divisor = 1867
let constant = 415


module MyInt
=
struct
  type t = int
  let compare = compare
end

(* variable name = string *)
module Var 
= 
struct
  type t = string
  let compare = compare
end

(*  module for  abstract Pre_value, abstract Pre_memory *)
module Pre_value = FlatDomain(MyInt)
module Pre_memory = FunDomain(Var)(Pre_value)


open Pre_value

let int_of_bool b = if b then 1 else 0
let bool_of_int i = if (i=0) then false else true
let virtual_var = "aWT!%#!@S!@$)(@*#%ASzlkmD"



(* define abstract semantics of expression for pre-analysis *)
let rec pre_calculate : exp -> Pre_memory.t -> Pre_value.t = fun e m -> match e with
  | NUM i -> ELT ( i )
  | VAR name -> let (Pre_memory.ELT n) = m in (* assume m is not TOP : TOP memory is useless *)
                (Pre_memory.Map.find name n) 
  | ADD (e1,e2) ->  let (v1,v2) = ( (pre_calculate e1 m) , (pre_calculate e2 m) ) in
                    (match (v1,v2) with
                    | (BOT , _) -> BOT
                    | (_, BOT)  -> BOT
                    | (TOP , _) -> TOP
                    | (_, TOP)  -> TOP
                    | (ELT i1, ELT i2) -> ELT (i1+i2)
                    )
  | MINUS e1 -> let v1 = (pre_calculate e1 m) in
                    (match v1 with
                    | BOT -> BOT
                    | TOP -> TOP 
                    | ELT i -> ELT( -i )                     
                    )
  | READ -> TOP
  | NOT e1 -> let v1 = (pre_calculate e1 m) in
                    (match v1 with
                    | BOT -> BOT
                    | TOP -> TOP 
                    | ELT i ->  if(i=0) then ELT(1) else ELT(0)                   
                    )
  | ANDALSO (e1,e2) ->  let (v1,v2) = ( (pre_calculate e1 m) , (pre_calculate e2 m) ) in
                    (match (v1,v2) with
                    | (BOT , _) -> BOT
                    | (_, BOT)  -> BOT
                    | (TOP , _) -> TOP
                    | (_, TOP)  -> TOP
                    | (ELT i1, ELT i2) -> let b1 = bool_of_int i1 in
                                          let b2 = bool_of_int i2 in
                                          ELT( int_of_bool(b1 && b2) )
                    )
  | ORELSE (e1,e2) ->  let (v1,v2) = ( (pre_calculate e1 m) , (pre_calculate e2 m) ) in
                    (match (v1,v2) with
                    | (BOT , _) -> BOT
                    | (_, BOT)  -> BOT
                    | (TOP , _) -> TOP
                    | (_, TOP)  -> TOP
                    | (ELT i1, ELT i2) -> let b1 = bool_of_int i1 in
                                          let b2 = bool_of_int i2 in
                                          ELT( int_of_bool(b1 || b2) )
                    )
  | LESS (e1,e2) ->  let (v1,v2) = ( (pre_calculate e1 m) , (pre_calculate e2 m) ) in
                    (match (v1,v2) with
                    | (BOT , _) -> BOT
                    | (_, BOT)  -> BOT
                    | (TOP , _) -> TOP
                    | (_, TOP)  -> TOP
                    | (ELT i1, ELT i2) -> ELT( int_of_bool(i1 < i2))
                    )




(* define abstract semantics of command  for pre-analysis *)
let rec pre_evaluate : cmd -> Pre_memory.t -> cmd * Pre_memory.t = fun c m -> (match c with
  | SEQ (c1,c2) ->  let (c1', m1) = (pre_evaluate c1 m) in
                    let (c2', m2) = (pre_evaluate c2 m1) in
                    ( SEQ(c1', c2') , m2 )

  | IF (e1, c1, c2) -> let v1 = pre_calculate e1 m in (match v1 with
                      | BOT -> raise (Error("undefined ref to v"))
                      | TOP -> let (c1', m1) = (pre_evaluate c1 m) in
                               let (c2', m2) = (pre_evaluate c2 m) in
                               (IF(e1,c1',c2'), Pre_memory.join m1 m2)
                      | ELT i -> if(i = 0) then (pre_evaluate c2 m)
                                 else (pre_evaluate c1 m) 
                      )
  
  | ASSIGN (name, e1) -> let v1 = pre_calculate e1 m in
                                  (c, Pre_memory.update m name v1)

  | WHILE (e1, c1) ->  let v = pre_calculate e1 m in 
                        match v with
                        | BOT ->  raise (Error("undefined ref to v"))
                        | TOP ->  (c, (urgent_evaluate c m))
                        | ELT i -> if (i = 0) then (* delete this while loop *)
                                                    (ASSIGN( virtual_var , (NUM 1)) ,m)
                                   else  (c, (urgent_evaluate c m)  )
  )


(* urgent_evaluate searches assignment in while loop and assign everything to TOP
 * to exit while loop immediately 
 *)
and urgent_evaluate : cmd -> Pre_memory.t -> Pre_memory.t = fun c m -> (match c with
  | SEQ (c1,c2) ->  let m1 = (urgent_evaluate c1 m) in
                    let m2 = (urgent_evaluate c2 m1) in
                    m2

  | IF (e1, c1, c2) -> let v1 = pre_calculate e1 m in (match v1 with
                      | BOT -> raise (Error("undefined ref to v"))
                      | TOP -> let m1 = (urgent_evaluate c1 m) in
                               let m2 = (urgent_evaluate c2 m) in
                               (Pre_memory.join m1 m2)
                      | ELT i -> if(i = 0) then (urgent_evaluate c2 m)
                                 else (urgent_evaluate c1 m) 
                      )
  
  | ASSIGN (name, e1) -> (Pre_memory.update m name TOP)

  | WHILE (e1 , c1) ->  (urgent_evaluate c1 m)
)
                        

   










(* main analysis begin : use powerset domain of remainders *)

module Residue 
=
struct
  type t = int
  let compare = compare
  let rec modulo input = if( input < 0) then modulo(input + divisor)
                         else if(input >= divisor ) then modulo(input - divisor)
                         else input
end


module ResSet =  PrimitiveSet(Residue)
module Value = PowerSetDomain(ResSet)
module Memory = FunDomain(Var)(Value)


open Value


(* inefficient when a lot of duplicates are produced *)
let get_cartesian_list : 'a list -> 'b list -> ('a * 'b) list = fun l1 l2 -> 
  let cartesian_list = [] in
  let cartesian_ref = ref cartesian_list in
  let traverse_l2  elt_froml1 = 
    let curr_cart_list = (!cartesian_ref) in
    let tmp_list = (List.map (fun elt2 -> (elt_froml1, elt2) ) l2) in
    let _ = (cartesian_ref := (curr_cart_list @ tmp_list )) in
    () in 
  let _ = (List.iter traverse_l2 l1) in
  (! cartesian_ref)
  
    

(* boolean for residue *)
type res_bool = BOOL of bool | UNDEF | BOTH

let rbool_not = function
  | UNDEF -> UNDEF
  | BOTH -> BOTH
  | BOOL b -> BOOL (not b)

let rbool_and = function
  | (UNDEF, _) -> UNDEF
  | (_, UNDEF) -> UNDEF
  | (BOTH , _) -> BOTH
  | (_ , BOTH) -> BOTH
  | (BOOL b1, BOOL b2) -> BOOL(b1 && b2)

let rbool_or = function
  | (UNDEF, _) -> UNDEF
  | (_, UNDEF) -> UNDEF
  | (BOTH , _) -> BOTH
  | (_ , BOTH) -> BOTH
  | (BOOL b1, BOOL b2) -> BOOL(b1 || b2)  

let rbool_of_ResList : int list -> res_bool = fun l -> 
  if( (List.length l) = 0) then UNDEF 
  else if(not(List.mem 0 l)) then BOOL(true)
  else BOTH

let resList_of_rbool : res_bool -> int list = function
  | UNDEF -> []
  | BOTH -> [0;1]
  | BOOL b -> if(b=true) then [1] else [0;1]

let rbool_of_residue i = if (i=0) then BOTH else BOOL(true)

(* define abstract semantics of expression for main-analysis *)
let rec calculate : exp -> Memory.t -> Value.t = fun e m -> match e with
  | NUM i -> Value.make [( Residue.modulo i )]  (* ResSet.ELT ( Residue.modulo i ) *)
  | VAR name -> let (Memory.ELT n) = m in (* assume m is not TOP : TOP memory is useless *)
                (Memory.Map.find name n) 
  | ADD (e1,e2) ->  let (v1,v2) = ( (calculate e1 m) , (calculate e2 m) ) in
                    (match (v1,v2) with
                    | (TOP , _) -> TOP
                    | (_, TOP)  -> TOP
                    | (ELT s1, ELT s2) ->  let l1 = ResSet.to_list s1 in
                                           let l2 = ResSet.to_list s2 in 
                                           let cartesian_list = get_cartesian_list l1 l2 in
                                           let added_list = (List.map 
                                              (fun (a,b) -> Residue.modulo (a + b)) cartesian_list ) in
                                          
                                           if( (List.length added_list) > 30) then TOP
                                           else (Value.make added_list)
                    )

  | MINUS e1 -> let v1 = (calculate e1 m) in
                    (match v1 with
                    | TOP -> TOP 
                    | ELT s ->  let l = ResSet.to_list s in
                                let minused_list = (List.map
                                  (fun a -> Residue.modulo( divisor - a )) l) in
                                if( (List.length minused_list) > 30) then TOP
                                else (Value.make minused_list)  
                                
                    )
  | READ -> TOP
  | NOT e1 -> let v1 = (calculate e1 m) in
                    (match v1 with
                    | TOP -> TOP 
                    | ELT s ->  let l = ResSet.to_list s in
                                let bool_l = (List.map  (fun a -> rbool_of_residue a ) l) in
                                let bool_l_noted = (List.map  (fun a -> rbool_not a ) bool_l) in
                                let noted_list = ( List.concat ( List.map 
                                                  (fun a -> resList_of_rbool a) bool_l_noted ) ) in
                                if( (List.length noted_list) > 30) then TOP
                                else (Value.make noted_list)
                    )             
                    
  | ANDALSO (e1,e2) ->  let (v1,v2) = ( (calculate e1 m) , (calculate e2 m) ) in
                    (match (v1,v2) with
                    | (TOP , _) -> TOP
                    | (_, TOP)  -> TOP
                    | (ELT s1, ELT s2) -> let l1 = ResSet.to_list s1 in
                                          let l2 = ResSet.to_list s2 in 
                                          let bool_l1 = (List.map  (fun a -> rbool_of_residue a ) l1) in
                                          let bool_l2 = (List.map  (fun a -> rbool_of_residue a ) l2) in
                                          let cartesian_list = get_cartesian_list bool_l1 bool_l2 in
                                          let bool_anded = (List.map 
                                            (fun a -> (rbool_and a)) cartesian_list) in
                                          let anded_list = ( List.concat ( List.map 
                                            (fun a -> resList_of_rbool a) bool_anded ) ) in
                                          if( (List.length anded_list) > 30) then TOP
                                          else (Value.make anded_list)
                                          
                    )
  | ORELSE (e1,e2) ->  let (v1,v2) = ( (calculate e1 m) , (calculate e2 m) ) in
                    (match (v1,v2) with
                    | (TOP , _) -> TOP
                    | (_, TOP)  -> TOP
                    | (ELT s1, ELT s2) -> let l1 = ResSet.to_list s1 in
                                          let l2 = ResSet.to_list s2 in 
                                          let bool_l1 = (List.map  (fun a -> rbool_of_residue a ) l1) in
                                          let bool_l2 = (List.map  (fun a -> rbool_of_residue a ) l2) in
                                          let cartesian_list = get_cartesian_list bool_l1 bool_l2 in
                                          let bool_ored = (List.map 
                                            (fun a -> (rbool_or a)) cartesian_list) in
                                          let ored_list = ( List.concat ( List.map 
                                            (fun a -> resList_of_rbool a) bool_ored ) ) in
                                          
                                          if( (List.length ored_list) > 30) then TOP
                                          else (Value.make ored_list)
                                          
                    )
  | LESS (e1,e2) ->  (* in domain using remainder, cannot determin any of this *)
                    Value.make [0;1]    (* false = 0   or true = 1 *)







(* track abstract memory after each operation *)
let mem_list = []
let list_ref = ref mem_list
let append_mem m = let curr_list = !list_ref in
                   let _ = ( list_ref := m :: curr_list) in
                   ()



(* define abstract semantics of command *)
let rec evaluate : cmd -> Memory.t -> Memory.t = fun c m -> (match c with
  | SEQ (c1,c2) ->  let m1 = (evaluate c1 m) in
                    let m2 = (evaluate c2 m1) in
                    let _ = append_mem m1 in
                    let _ = append_mem m2 in
                    m2

  | IF (e1, c1, c2) -> let v1 = calculate e1 m in (match v1 with
                      | TOP -> Memory.join (evaluate c1 m) (evaluate c2 m)
                      | ELT s -> if( not( List.mem 0 (ResSet.to_list s) )) then (evaluate c1 m)
                                 else Memory.join (evaluate c1 m) (evaluate c2 m)
                      )
              
  | ASSIGN (name, e1) -> let v1 = calculate e1 m in
                                  Memory.update m name v1

  | WHILE (e1 , c1) -> (while_E_C c1 e1 m)
  )


and while_E_C : cmd -> exp -> Memory.t -> Memory.t = fun c1 e1 m ->
                        let m1 = evaluate c1 m in
                        (* m = m1 works? *)
                        if( m = m1 ) then m else  
                        let v1 = calculate e1 m1 in 
                        let m2 = match v1 with
                        | TOP ->  Memory.join m1 m  
                        | ELT s -> if( not( List.mem 0 (ResSet.to_list s) )) 
                                   then m1 else Memory.join m1 m  
                        in (while_E_C c1 e1 m2)








module Map2 =  Map.Make(struct type t = string let compare = compare end)
type result_map = result Map2.t

(* davinci analysis *)
let rec davinciAnalyzer : program -> result = fun pgm ->
  let mem0 = (Pre_memory.make []) in 
  let (pgm', _) = pre_evaluate pgm mem0 in
  (* let _= (pp pgm') in *)
  let mem_init = (Memory.make []) in
  let mem_last = evaluate pgm' mem_init in
  let (variable_list0, _) = List.split( Memory.to_list mem_last) in
  let variable_list = List.filter (fun x -> not (virtual_var = x))  variable_list0 in (* remove garbage *)
  let result_init : result_map = (List.fold_left (fun m str -> Map2.add str YES m) Map2.empty variable_list) in
  let memory_list = !list_ref in


  let update_with_m :  result_map -> Memory.t  -> result_map  = fun result_in m_curr ->
    let update_x_with_m result_in x =
      let (Memory.ELT n_curr) = m_curr in (* assume m is not TOP : TOP memory is useless *)

      
      if(Memory.Map.mem x n_curr) then
           let s = Memory.Map.find x n_curr in

           let l = (match s with
            | TOP -> [0;1;2;3;4;5;6;124; constant]
            | ELT s_in -> ResSet.to_list s_in) in
           let size = (List.length l) in
           if(size = 0) then result_in
           else if( (size > 1) && (List.mem constant l) ) then (Map2.add x DONTKNOW result_in) (* donknow case *)
           else if(List.mem constant l) then result_in    (* YES case do nothing *)
           else let x_curr_result = Map2.find x result_in in  (* no case :  switch yes to no,  do not change dontknow*)
                if( x_curr_result = YES) then (Map2.add x NO result_in)
                else result_in
      else result_in
    in
    (List.fold_left update_x_with_m  result_in  variable_list) in


  
  let result_last = List.fold_left update_with_m result_init memory_list in
  let (_, result_list) = List.split (Map2.bindings result_last) in
  if( List.mem YES result_list) then YES 
  else if(List.mem DONTKNOW result_list) then DONTKNOW 
  else NO

