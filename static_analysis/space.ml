(*
 * SNU 4541.664A Program Analysis 2019 Fall
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 * Chanhee Cho (cksgml@snu.ac.kr)
 *)


(*
 * space analyzer
 *)
 
open Program 
open DomFunctor


exception Error of string
 
type result =
  | YES         (* all var has value 0~12 mod 768 *)
  | NO          (* some var doesn't has value 0~12 mod 768 *)
  | DONTKNOW    (* can't determine *)

let result_to_str : result -> string = fun a -> match a with
  | YES -> "Yes"
  | NO -> "No"
  | DONTKNOW -> "I don't know"



let constant = 768
let limit = 12


module Residue 
=
struct
  type t = int
  let compare = compare
  let rec modulo input = if( input < 0) then modulo(input + constant)
                         else if(input >= constant ) then modulo(input - constant)
                         else input
end

(* variable name = string *)
module Var 
= 
struct
  type t = string
  let compare = compare
end


(*  module for  abstract value, abstract memory *)
module Value = FlatDomain(Residue)
module Memory = FunDomain(Var)(Value)


open Value



(* define abstract semantics of expression *)
let rec calculate : exp -> Memory.t -> Value.t = fun e m -> match e with
  | NUM i -> ELT ( Residue.modulo i)
  | VAR name -> let (Memory.ELT n) = m in
                (Memory.Map.find name n) 
  | ADD (e1,e2) ->  let (v1,v2) = ( (calculate e1 m) , (calculate e2 m) ) in
                    (match (v1,v2) with
                    | (BOT , _) -> BOT
                    | (_, BOT)  -> BOT
                    | (TOP , _) -> TOP
                    | (_, TOP)  -> TOP
                    | (ELT i1, ELT i2) -> ELT ( Residue.modulo (i1 + i2)  )
                    )
  | MINUS e1 -> let v1 = (calculate e1 m) in
                    (match v1 with
                    | BOT -> BOT
                    | TOP -> TOP 
                    | ELT i -> ELT( Residue.modulo( constant - i ) )                     
                    )


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
                      | BOT -> raise (Error("undefined ref to v"))
                      | TOP -> Memory.join (evaluate c1 m) (evaluate c2 m)
                      | ELT i -> if( i > 0) then (evaluate c1 m)
                                 else Memory.join (evaluate c1 m) (evaluate c2 m)
                      )
              
  | ASSIGN (name, e1) -> let v1 = calculate e1 m in
                                  Memory.update m name v1

  | REPEAT (c1 , e1) -> let m1 =  (evaluate c1 m) in
                        (while_E_C c1 e1 m1)
  )


and while_E_C : cmd -> exp -> Memory.t -> Memory.t = fun c e m ->
                        let m1 = evaluate c m in

                        (* m = m1 works? *)
                        if( m = m1 ) then m else  
                        let v1 = calculate e m1 in 
                        let m2 = match v1 with
                        | BOT ->  raise (Error("undefined ref to v"))
                        | TOP ->  Memory.join m1 m  
                        | ELT i -> if (i > 0) then m1 else Memory.join m1 m  
                        in (while_E_C c e m2)






(* result of one abstract memory *)
let result_of_abstract_memmory : Memory.t -> result = fun m ->
  let (_, value_list) = List.split (Memory.to_list m) in
  let is_above_limit = fun v -> match v with
    | BOT -> true
    | TOP -> false
    | ELT i ->  (i > 12)
  in
  if(List.mem TOP value_list ) then DONTKNOW
  else if(List.exists is_above_limit value_list ) then NO   (* if num > 12 then NO *)
  else YES


  
(* space analysis *)
let rec spaceAnalyzer : program -> result = fun pgm -> 
  let mem0 = (Memory.make []) in 
  let _ = evaluate pgm mem0 in
  let memory_list = !list_ref in 
  let result_list = (List.map   result_of_abstract_memmory  memory_list)  in
  
  if(List.mem DONTKNOW result_list ) then DONTKNOW
  else if(List.mem NO result_list ) then NO
  else YES


