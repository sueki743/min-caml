
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
  | IfEq of Id.t * Id.t * t * t
  | IfLE of Id.t * Id.t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | LetRec of fundef * t
  | App of Id.t * Id.t list
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.t
  | ExtFunApp of Id.t * Id.t list
  (*以下を追加*)
  |Ftoi of Id.t
  |Itof of Id.t
  |FAbs of Id.t
  |FSqrt of Id.t
  |Read_int of Id.t(*引数はunit型*)
  |Read_float of Id.t(*引数はunit型*)
  |Print_char of Id.t
  |ForLE of ((Id.t* Id.t) * (Id.t * Id.t) * t) *t
  |Let_Ref of (Id.t * Type.t) *t *t(*再代入可能変数,1要素配列のように扱うが
                                    配列と違いレジスタに割り当てる*)
  |Ref_Get of Id.t
  |Ref_Put of Id.t * Id.t

  |LetPara of parallel*t
  |Run_parallel of Id.t*Id.t*Id.t list*(Id.t*int) list
  |Accum of Id.t*Id.t*Id.t
                        
 and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }
                
 and parallel ={pargs:(Id.t*Type.t) list;
                index:(Id.t*(Id.vc*Id.vc)) ;
                accum:(Id.t*int)list list;
                pbody : t }     (* 自由変数を解決するのはclosure.g *)

val fv : t -> S.t
val cons : t ->t->t
val f : Syntax.t -> t
