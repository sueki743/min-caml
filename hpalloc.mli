

type t = 
  | Unit
  | Int of int
  | Float of float
  | Neg of Id.t
  | Add of Id.t * Id.t
  | Sub of Id.t * Id.t
  | Mul of Id.t * Id.t
  | Div of Id.t * Id.t
  | FNeg of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | IfEq of Id.t * Id.t * t * t (* 比較 + 分岐 (caml2html: knormal_branch) *)
  | IfLE of Id.t * Id.t * t * t (* 比較 + 分岐 *)
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | LetRec of fundef * t
  | App of Id.t * Id.t list
  | ConstTuple of Id.l
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.t
  | ConstArray of Id.l
  | ExtFunApp of Id.t * Id.t list
  |Ftoi of Id.t
  |Itof of Id.t
  |FAbs of Id.t
  |FSqrt of Id.t
  |Read_int of Id.t(*引数はunit型*)
  |Read_float of Id.t(*引数はunit型*)
  |Print_char of Id.t

 and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

type arraydef = {name :Id.l * Type.t;
                 size :int;
                 initv:t }

type tupledef = {name :Id.l * Type.t;
                 body:t list}

val arrays : arraydef list ref
val tuples : tupledef list ref

val f : KNormal.t -> t
