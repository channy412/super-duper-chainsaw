(*
 * SNU 4541.664A Program Analysis 2019 Fall
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 * Chanhee Cho (cksgml@snu.ac.kr)
 *)


(*
 * fairSW analyzer
 *)
 
open Program 
open DomFunctor

exception Error of string
 
type result =
  | YES
  | NO
  | DONTKNOW

let result_to_str : result -> string = fun a -> match a with
  | YES -> "Yes"
  | NO -> "No"
  | DONTKNOW -> "I don't know"










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
                        










(* main analysis begin *)

module Intv 
=
struct
  type bound = Z of int | Pinfty | Ninfty
  type t = BOT | ELT of bound * bound


  let str_of_bound = function
    | Pinfty -> "+inf"
    | Ninfty -> "-inf"
    | Z i ->  string_of_int i

  let string_of_intv = function
    | BOT -> "empty"
    | ELT(a,b) -> "[" ^ (str_of_bound a) ^ ", " ^ (str_of_bound b) ^ "]"

  let top = ELT (Ninfty, Pinfty)
  let bot = BOT
  let bound_leq a b = 
    match a,b with
    | (Ninfty, _) -> true
    | (_, Pinfty) -> true
    | (_, Ninfty) -> false
    | (Pinfty, _) -> false
    | (Z i1, Z i2) -> i1 <= i2


    let bound_lq a b = 
    match a,b with
    | (Ninfty, _) -> true
    | (_, Pinfty) -> true
    | (_, Ninfty) -> false
    | (Pinfty, _) -> false
    | (Z i1, Z i2) -> i1 < i2


  let smaller a b = if bound_leq a b then a else b

  let bigger a b = if bound_leq a b then b else a

  let join x y = 
    match x,y with
    | (BOT, _) -> y
    | (_, BOT) -> x
    | (ELT (l1, u1), ELT (l2, u2)) -> ELT (smaller l1 l2, bigger u1 u2)

  let leq x y = match x,y with
    | (BOT, _) -> true
    | (_, BOT) -> false
    | (ELT (l1,u1), ELT (l2,u2)) -> bound_leq l2 l1 && bound_leq u1 u2

  let make low upper = ELT (low, upper)

  let minimum a b =
    match a,b with
    | (Ninfty, _)  -> Ninfty
    | (_ , Ninfty) -> Ninfty
    | (Z i1, Pinfty) -> Z i1
    | (Pinfty, Z i2) -> Z i2
    | (Pinfty, Pinfty) -> Pinfty
    | (Z i1, Z i2) -> if( i1 < i2) then Z i1 else Z i2

  let maximum a b =
    match a,b with
    | (Pinfty, _)  -> Pinfty
    | (_ , Pinfty) -> Pinfty
    | (Z i1, Ninfty) -> Z i1
    | (Ninfty, Z i2) -> Z i2
    | (Ninfty, Ninfty) -> Ninfty
    | (Z i1, Z i2) -> if( i1 > i2) then Z i1 else Z i2

  let adder a b = 
    match a,b with
    | (Ninfty, _)  -> Ninfty
    | (_ , Ninfty) -> Ninfty
    | (Pinfty, _)  -> Pinfty
    | (_ , Pinfty) -> Pinfty
    | (Z i1, Z i2) -> Z (i1 + i2)

  let minus = function
    | Pinfty -> Ninfty
    | Ninfty -> Pinfty
    | Z i -> Z (-i)

  let length_of_intv = function
    | BOT -> 0
    | ELT(a,b) -> (match a,b with
        | (Ninfty, _) -> 100000000
        | (_, Pinfty) -> 100000000
        | (_, Ninfty) ->  0
        | (Pinfty, _) ->  0
        | (Z i1, Z i2) ->  (i2 - i1))

  let include_zero x = leq (ELT(Z 0, Z 0)) x
  let include_one x = leq (ELT(Z 1, Z 1)) x

end



module Value =  Intv
module Memory = FunDomain(Var)(Value)


open Value

type rbool = BOOL of bool | UNDEF | BOTH

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

let rbool_of_intv = fun i -> (match i with
  | BOT -> UNDEF
  | ELT(low, high) -> if(include_zero i) then ( if( (length_of_intv i) > 0) then BOTH else BOOL false)
                      else BOOL true
)

let intv_of_rbool = function
  | UNDEF -> BOT
  | BOTH -> (Value.make (Z 0) (Z 1) )
  | BOOL b -> if(b) then (Value.make (Z 1) (Z 1) ) else (Value.make (Z 0) (Z 0) )



(* define abstract semantics of expression for main-analysis *)
let rec calculate : exp -> Memory.t -> Value.t = fun e m -> match e with
  | NUM i -> (Value.make (Z i) (Z i) )
  | VAR name -> 
                (* let (Memory.ELT n) = m in (* assume m is not TOP : TOP memory is useless *)
                (Memory.Map.find name n)  *)

                (match m with 
                | Memory.ELT n -> (Memory.Map.find name n) 
                | Memory.TOP -> Value.make Ninfty Pinfty)

  | ADD (e1,e2) ->  let (v1,v2) = ( (calculate e1 m) , (calculate e2 m) ) in
                    (match (v1,v2) with
                    | (BOT , _) -> BOT
                    | (_, BOT)  -> BOT
                    | (ELT (low1, high1), ELT (low2, high2) ) -> Value.make (adder low1 low2)(adder high1 high2)
                    )

  | MINUS e1 -> let v1 = (calculate e1 m) in
                    (match v1 with
                    | BOT -> BOT
                    | ELT (low, high) -> Value.make (minus high) (minus low)
                    )
  | READ -> (Value.make Ninfty Pinfty )
  | NOT e1 -> let v1 = (calculate e1 m) in
                     (match v1 with
                    | BOT -> BOT
                    | ELT (low, high) -> let rb = rbool_of_intv v1 in
                                         let not_rb = rbool_not rb in
                                         intv_of_rbool not_rb
                    )
  | ANDALSO (e1,e2) ->  let (v1,v2) = ( (calculate e1 m) , (calculate e2 m) ) in
                    (match (v1,v2) with
                    | (BOT , _) -> BOT
                    | (_, BOT)  -> BOT
                    | (ELT (low1, high1), ELT (low2, high2) ) -> 
                        let rb1 = rbool_of_intv v1 in
                        let rb2 = rbool_of_intv v2 in
                        let and_rb = rbool_and (rb1, rb2) in
                        intv_of_rbool and_rb               
                    )
  | ORELSE (e1,e2) ->  let (v1,v2) = ( (calculate e1 m) , (calculate e2 m) ) in
                    (match (v1,v2) with
                    | (BOT , _) -> BOT
                    | (_, BOT)  -> BOT
                    | (ELT (low1, high1), ELT (low2, high2) ) -> 
                        let rb1 = rbool_of_intv v1 in
                        let rb2 = rbool_of_intv v2 in
                        let or_rb = rbool_or (rb1, rb2) in
                        intv_of_rbool or_rb               
                    )
  | LESS (e1,e2) -> let (v1,v2) = ( (calculate e1 m) , (calculate e2 m) ) in
                    (match (v1,v2) with
                    | (BOT , _) -> BOT
                    | (_, BOT)  -> BOT
                    | (ELT (low1, high1), ELT (low2, high2) ) -> 
                        if( bound_leq high1 low2 ) then (Value.make (Z 1) (Z 1) ) (* true *)
                        else if ( bound_leq high2 low1 ) then (Value.make (Z 0) (Z 0) ) (* false *)
                        else (Value.make (Z 0) (Z 1) )  (* both *)
                    )




 
let count = 0
let count_ref = ref count
let inc_count = let curr_cnt = (! count_ref) in
                let _ = (count_ref := curr_cnt + 1) in
                ()
              


(* define abstract semantics of command *)
let rec evaluate : string -> cmd -> Memory.t -> Memory.t = fun x c m -> (match c with
  | SEQ (c1,c2) ->  let m1 = (evaluate x c1 m) in
                    let m2 = (evaluate x c2 m1) in
                    m2

  | IF (e1, c1, c2) -> let v1 = calculate e1 m in
                       let rb1 = rbool_of_intv v1 in
                       (match rb1 with
                        | UNDEF -> raise (Error("undefined ref to v"))
                        | BOTH -> Memory.join (evaluate x c1 m) (evaluate x c2 m)
                        | BOOL b -> if(b) then (evaluate x c1 m) else (evaluate x c2 m)     
                       )

  | ASSIGN (name, e1) -> let v1 = 
                         if((name = x) && (e1 = READ)) then ELT(Z 100, Pinfty)
                         else calculate e1 m in
                         Memory.update m name v1

  | WHILE (e1 , c1) ->  
                       let _ = inc_count in
                       if( (!count_ref) > 10000 ) then let _ = count_ref := 0 in  (urgent_evaluate2 c1 m  )
                       else





                       let v1 = calculate e1 m in
                       let rb1 = rbool_of_intv v1 in
                       let m1 = (match rb1 with
                        | UNDEF -> raise (Error("undefined ref to v"))
                        | BOTH -> Memory.join (evaluate x c1 m) m
                        | BOOL b -> if(b) then (evaluate x c1 m) else m
                       ) in
                       if( m = m1 ) then m 
                       else (  evaluate x c m1  )
                        (* let filter_B : exp -> Memory.t -> Memory.t = fun e_fil m_in ->
                           let v1 = calculate e1 m in
                           let rb1 = rbool_of_intv v1 in
                            (match rb1 with
                              | UNDEF -> raise (Error("undefined ref to v"))
                              | BOTH -> m_in
                              | BOOL b -> if(b) then m_in else Memory.bot
                            ) in
                        let filter_B_not : exp -> Memory.t -> Memory.t = fun e_fil m_in ->
                           let v1 = calculate e1 m in
                           let rb0 = rbool_of_intv v1 in
                           let rb1 = rbool_not rb0 in
                            (match rb1 with
                              | UNDEF -> raise (Error("undefined ref to v"))
                              | BOTH -> m_in
                              | BOOL b -> if(b) then m_in else Memory.bot
                            ) in
                        let f_sharp : Memory.t -> Memory.t = fun x_sharp ->
                          Memory.join m (evaluate x c1 (filter_B e1 x_sharp)) in
                        (* let widen f =  *)
                        Memory.TOP *)

  )


and urgent_evaluate2 : cmd -> Memory.t -> Memory.t = fun c m -> (match c with
  | SEQ (c1,c2) ->  let m1 = (urgent_evaluate2 c1 m) in
                    let m2 = (urgent_evaluate2 c2 m1) in
                    m2
  | IF (e1, c1, c2) -> let v1 = calculate e1 m in
                       let rb1 = rbool_of_intv v1 in
                       (match rb1 with
                        | UNDEF -> raise (Error("undefined ref to v"))
                        | BOTH -> Memory.join (urgent_evaluate2 c1 m) (urgent_evaluate2  c2 m)
                        | BOOL b -> if(b) then (urgent_evaluate2 c1 m) else (urgent_evaluate2  c2 m)     
                       )
  | ASSIGN (name, e1) -> (Memory.update m name (Value.make Ninfty Pinfty))
  | WHILE (e1 , c1) ->  (urgent_evaluate2 c1 m)
)


(* get at most three READ variable *)
let var_list = []
let list_ref = ref var_list
let append_list var = let curr_list = !list_ref in
                      let _ = ( list_ref := var :: curr_list) in
                      ()


let rec getReadVariables : program -> unit = fun c -> (match c with
  | SEQ (c1,c2) ->    let _ = getReadVariables c1 in getReadVariables c2
  | IF (e1, c1, c2) ->  let _ = getReadVariables c1 in getReadVariables c2
  | ASSIGN (name, e1) ->  if(e1 = READ) then append_list name else ()
  | WHILE (e1 , c1) ->  getReadVariables c1 
)





(* fairSW analysis *)
let rec fairAnalyzer : program -> result = fun pgm ->
  try (
  let _ = getReadVariables pgm in
  let read_var_list = !list_ref in

  let mem0 = (Pre_memory.make []) in 
  let (pgm', _) = pre_evaluate pgm mem0 in

  (* let _= (pp pgm') in *)
  (* let _= List.iter (fun x-> print_endline x) read_var_list in *)

  let mem_init = (Memory.make []) in
  let liber_var = "liberation" in
  let liberated_by_x x = 
    let mem_x_in = evaluate x pgm' mem_init in
    let (Memory.ELT m_x) = mem_x_in in (* assume m is not TOP : TOP memory is useless *)
    if(Memory.Map.mem liber_var m_x) then 
       let liber_value : Value.t = Memory.Map.find liber_var m_x in
       (* let _ = print_endline(string_of_intv liber_value) in *)
       if( liber_value =  (Value.make (Z 1) (Z 1) )  ) then YES
       else if( include_one liber_value ) then DONTKNOW
       else NO
    else NO
  in
  let result_list = List.map  liberated_by_x  read_var_list in

  (* let _= List.iter (fun x-> print_endline (result_to_str x)) result_list in *)

  if( not(List.mem NO result_list) && not(List.mem DONTKNOW result_list) ) then YES
  else if( not(List.mem NO result_list) ) then DONTKNOW
  else NO
  
  ) with
  _ -> DONTKNOW 


