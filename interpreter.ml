(*++++++++++++++++++++++++++++++++++++++*)
(*  Interpretador para L2               *)
(*   - inferência de tipos              *)
(*   - avaliador big step com ambiente  *)
(*++++++++++++++++++++++++++++++++++++++*)


(**+++++++++++++++++++++++++++++++++++++++++*)
(*  SINTAXE, AMBIENTE de TIPOS e de VALORES *)
(*++++++++++++++++++++++++++++++++++++++++++*)

type tipo =
    TyInt
  | TyBool
  | TyFn of tipo * tipo
  | TyPair of tipo * tipo
  | TyRef of tipo
  | TyUnit

type ident = string

type op = Sum | Sub | Mult | Eq | Gt | Lt | Geq | Leq

type expr =
  | Num of int
  | Var of ident
  | True
  | False
  | Binop of op * expr * expr
  | Pair of expr * expr
  | Fst of expr
  | Snd of expr
  | If of expr * expr * expr
  | Fn of ident * tipo * expr
  | App of expr * expr
  | Let of ident * tipo * expr * expr
  | LetRec of ident * tipo * expr  * expr
  | Asg of expr * expr
  | Dref of expr
  | New of expr
  | Seq of expr * expr
  | Whl of expr * expr
  | Skip
              
type tenv = (ident * tipo) list

type valor =
    VNum of int
  | VTrue
  | VFalse
  | VPair of valor * valor
  | VClos  of ident * expr * renv
  | VRclos of ident * ident * expr * renv
  | Skip of memory
  | Address of int * memory
and renv = (ident * valor) list
and memory = (int * valor) list

(* funções polimórficas para ambientes *)

let rec lookup a k =
  match a with
    [] -> None
  | (y,i) :: tl -> if (y=k) then Some i else lookup tl k 
       
let update a k i =
  (k,i) :: a   

let rec restore list key new_value =
  match list with
  (current_key, value) :: tail ->
     if current_key = key then 
      (key, new_value) :: restore list key new_value 
    else (current_key, value) :: restore list key new_value
  | [] -> []

(* exceções que não devem ocorrer  *)

exception BugParser of string
exception BugTypeInfer
exception NotImplemented
  

(**+++++++++++++++++++++++++++++++++++++++++*)
(*         INFERÊNCIA DE TIPOS              *)
(*++++++++++++++++++++++++++++++++++++++++++*)

exception TypeError of string

let rec typeinfer (tenv:tenv) (e:expr) : tipo =
  match e with

  (* TInt  *)
  | Num _ -> TyInt

  (* TVar *)
  | Var x ->
      (match lookup tenv x with
         Some t -> t
       | None -> raise (TypeError ("variábel não declarada: " ^ x)))

  (* TBool *)
  | True  -> TyBool
  | False -> TyBool

  (*TOP+  e outras para demais peradores binários *)
  | Binop(oper,e1,e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      if t1 = TyInt && t2 = TyInt then
        (match oper with
           Sum | Sub | Mult -> TyInt
         | Eq | Lt | Gt | Geq | Leq -> TyBool)
      else raise (TypeError "operando não é do tipo int")

  (* TPair *)
  | Pair(e1,e2) -> TyPair(typeinfer tenv e1, typeinfer tenv e2)
  (* TFst *)
  | Fst e1 ->
      (match typeinfer tenv e1 with
         TyPair(t1,_) -> t1
       | _ -> raise (TypeError "fst espera tipo par"))
  (* TSnd  *)
  | Snd e1 ->
      (match typeinfer tenv e1 with
         TyPair(_,t2) -> t2
       | _ -> raise (TypeError "fst espera tipo par"))

  (* TIf  *)
  | If(e1,e2,e3) ->
      (match typeinfer tenv e1 with
         TyBool ->
           let t2 = typeinfer tenv e2 in
           let t3 = typeinfer tenv e3
           in if t2 = t3 then t2
           else raise (TypeError "then/else com tipos diferentes")
       | _ -> raise (TypeError "condição de IF não é do tipo bool"))

  (* TFn *)
  | Fn(x,t,e1) ->
      let t1 = typeinfer (update tenv x t) e1
      in TyFn(t,t1)

  (* TApp *)
  | App(e1,e2) ->
      (match typeinfer tenv e1 with
         TyFn(t, t') ->  if (typeinfer tenv e2) = t then t'
           else raise (TypeError "tipo argumento errado" )
       | _ -> raise (TypeError "tipo função era esperado"))

  (* TLet *)
  | Let(x,t,e1,e2) ->
      if (typeinfer tenv e1) = t then typeinfer (update tenv x t) e2
      else raise (TypeError "expr não é do tipo declarado em Let" )

  (* TLetRec *)
  | LetRec(f,(TyFn(t1,t2) as tf), Fn(x,tx,e1), e2) ->
      let tenv_com_tf = update tenv f tf in
      let tenv_com_tf_tx = update tenv_com_tf x tx in
      if (typeinfer tenv_com_tf_tx e1) = t2
      then typeinfer tenv_com_tf e2
      else raise (TypeError "tipo da função diferente do declarado")

  (* TLetRec mal construido*)
  | LetRec _ -> raise (TypeError "tipos das funções não estão corretamente definidos")

  (* Assignment *)
  | Asg(e1, e2) -> 
      (match typeinfer tenv e1 with
       TyRef(t) -> if (typeinfer tenv e2) = t then TyUnit
       else raise (TypeError "atribuição de um tipo para uma referência de outra tipo")
       | _ -> raise(TypeError "atribuição para uma expressão que não é referência a algum tipo"))
  
  (* Dereference *)
  | Dref(e) ->
      (match typeinfer tenv e with
        TyRef(t) -> t
        | _ -> raise(TypeError "rereferência de uma expressão que não é referência a algum tipo"))
  
  (* New *)
  | New (e) ->
      let t = typeinfer tenv e in
      TyRef(t)
  
  (* Sequence of commands *)
  | Seq (e1, e2) ->
      if (typeinfer tenv e1) = TyUnit then (typeinfer tenv e2)
      else raise (TypeError "primeiro comando é de um tipo não unit")
  
  (* While *)
  | Whl (e1, e2) -> 
    if (typeinfer tenv e1) = TyBool then
      if (typeinfer tenv e2) = TyUnit then TyUnit
      else raise (TypeError "o comando interno do while é de um tipo não unit")
    else raise (TypeError "a condição do while não é do tipo bool")
  
  (* Skip *)
  | Skip -> TyUnit

  
(**+++++++++++++++++++++++++++++++++++++++++*)
(*                 AVALIADOR                *)
(*++++++++++++++++++++++++++++++++++++++++++*)

let compute (oper: op) (v1: valor) (v2: valor) : valor =
  match (oper, v1, v2) with
    (Sum, VNum(n1), VNum(n2)) -> VNum (n1 + n2)
  | (Sub, VNum(n1), VNum(n2)) -> VNum (n1 - n2)
  | (Mult, VNum(n1),VNum(n2)) -> VNum (n1 * n2)
  | (Eq, VNum(n1), VNum(n2))  -> if (n1 = n2)  then VTrue else VFalse
  | (Gt, VNum(n1), VNum(n2))  -> if (n1 > n2)  then VTrue else VFalse
  | (Lt, VNum(n1), VNum(n2))  -> if (n1 < n2)  then VTrue else VFalse
  | (Geq, VNum(n1), VNum(n2)) -> if (n1 >= n2) then VTrue else VFalse
  | (Leq, VNum(n1), VNum(n2)) -> if (n1 <= n2) then VTrue else VFalse
  | _ -> raise BugTypeInfer


let rec eval (mem: memory) (renv:renv) (e:expr) : valor =
  match e with
    Num n -> VNum n
  | True -> VTrue
  | False -> VFalse

  | Var x ->
      (match lookup renv x with
         Some v -> v
       | None -> raise BugTypeInfer)
      
  | Binop(oper,e1,e2) ->
      let v1 = eval mem renv e1 in
      let v2 = eval mem renv e2 in
      compute oper v1 v2

  | Pair(e1,e2) ->
      let v1 = eval mem renv e1 in
      let v2 = eval mem renv e2
      in VPair(v1,v2)

  | Fst e ->
      (match eval mem renv e with
       | VPair(v1,_) -> v1
       | _ -> raise BugTypeInfer)

  | Snd e ->
      (match eval mem renv e with
       | VPair(_,v2) -> v2
       | _ -> raise BugTypeInfer)


  | If(e1,e2,e3) ->
      (match eval mem renv e1 with
         VTrue  -> eval mem renv e2
       | VFalse -> eval mem renv e3
       | _ -> raise BugTypeInfer )

  | Fn (x,_,e1) ->  VClos(x,e1,renv)

  | App(e1,e2) ->
      let v1 = eval mem renv e1 in
      let v2 = eval mem renv e2 in
      (match v1 with
         VClos(x,ebdy,renv') ->
           let renv'' = update renv' x v2
           in eval mem renv'' ebdy

       | VRclos(f,x,ebdy,renv') ->
           let renv''  = update renv' x v2 in
           let renv''' = update renv'' f v1
           in eval mem renv''' ebdy
       | _ -> raise BugTypeInfer)

  | Let(x,_,e1,e2) ->
      let v1 = eval mem renv e1
      in eval mem (update renv x v1) e2

  | LetRec(f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
      let renv'= update renv f (VRclos(f,x,e1,renv))
      in eval mem renv' e2
        
  | LetRec _ -> raise (BugParser "funções recursivas não estão corretamente definidas")

  | Asg(e1, e2) -> 
      (match eval mem renv e1 with
          Address(v, mem') -> (match lookup mem' v with
              Some valor -> 
                let new_value = eval mem' renv e2 in
                let mem'' = restore mem' v new_value in
                 Skip(mem'')
              | None -> raise (BugParser "não há valor nesse endereço buscado"))
          | _ -> raise (BugParser "um valor que não é endereço foi usado para acessar a memória"))

  | Dref(e) ->
    (match eval mem renv e with
      Address(v, mem') -> (match lookup mem' v with
      Some valor -> valor
      | None -> raise (BugParser "não há valor nesse endereço buscado"))
      | _ -> raise (BugParser "um valor que não é endereço foi usado para acessar a memória"))

  | New (e) -> 
    let value = eval mem renv e in
    let new_address = (match mem with
    [] -> 0
    | (head_address, _) :: _ -> head_address + 1
    ) in
    let new_mem = update mem new_address value in
    Address(new_address, new_mem) 

  | Seq (e1, e2) -> 
    (match eval mem renv e1 with
      Skip(mem') -> eval mem' renv e2
      | _ -> raise (BugParser "primeira expressão não é do tipo skip")
    )

  | Whl (e1, e2) -> raise NotImplemented
    
  | Skip -> Skip(mem)
                  
(* função auxiliar que converte tipo para string *)

let rec ttos (t:tipo) : string =
  match t with
    TyInt  -> "int"
  | TyBool -> "bool"
  | TyFn(t1,t2)   ->  "("  ^ (ttos t1) ^ " --> " ^ (ttos t2) ^ ")"
  | TyPair(t1,t2) ->  "("  ^ (ttos t1) ^ " * "   ^ (ttos t2) ^ ")"
  | _-> raise NotImplemented

(* função auxiliar que converte valor para string *)

let rec vtos (v: valor) : string =
  match v with
    VNum n -> string_of_int n
  | VTrue -> "true"
  | VFalse -> "false"
  | VPair(v1, v2) ->
      "(" ^ vtos v1 ^ "," ^ vtos v1 ^ ")"
  | VClos _ ->  "fn"
  | VRclos _ -> "fn"
  | Skip _ -> "skip"
  | Address(n, _) -> "Address" ^ string_of_int n

(* principal do interpretador *)

let int_bse (e:expr) : unit =
  try
    let t = typeinfer [] e in
    let v = eval [] [] e
    in  print_string ((vtos v) ^ " : " ^ (ttos t))
  with
    TypeError msg ->  print_string ("erro de tipo - " ^ msg)
   
 (* as exceções abaixo nao podem ocorrer   *)
  | BugTypeInfer  ->  print_string "corrigir bug em typeinfer"
  | BugParser error    ->  print_string error
                        

 (* +++++++++++++++++++++++++++++++++++++++*)
 (*                TESTES                  *)
 (*++++++++++++++++++++++++++++++++++++++++*)



(*
     let x:int = 2 
     in let foo: int --> int = fn y:int => x + y 
        in let x: int = 5
           in foo 10 
*)

let e'' = Let("x", TyInt, Num 5, App(Var "foo", Num 10))

let e'  = Let("foo", TyFn(TyInt,TyInt), Fn("y", TyInt, Binop(Sum, Var "x", Var "y")), e'')

let tst = Let("x", TyInt, Num(2), e') 
    
    (*
     let x:int = 2 
     in let foo: int --> int = fn y:int => x + y 
        in let x: int = 5
           in foo 
*)


let e2 = Let("x", TyInt, Num 5, Var "foo")

let e1  = Let("foo", TyFn(TyInt,TyInt), Fn("y", TyInt, Binop(Sum, Var "x", Var "y")), e2)

let tst2 = Let("x", TyInt, Num(2), e1) 


  
    
    
              
              