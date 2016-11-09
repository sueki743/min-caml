type t = (* MinCamlの構文を表現するデータ型 (caml2html: syntax_t) *)
  | Unit of  pos
  | Bool of bool * pos
  | Int of int * pos
  | Float of float *pos
  | Not of t
  | Neg of t
  | Add of t * t
  | Sub of t * t
  | Mul of t * t
  | Div of t * t
  | FNeg of t
  | FAdd of t * t
  | FSub of t * t
  | FMul of t * t
  | FDiv of t * t
  | Eq of t * t
  | LE of t * t
  | If of t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t * pos
  | LetRec of fundef * t
  | App of t * t list
  | Tuple of t list
  | LetTuple of (Id.t * Type.t) list * t * t
  | Array of t * t
  | Get of t * t
  | Put of t * t * t
 and fundef = { name : (Id.t * Type.t) *pos; args : (Id.t * Type.t) list; body : t }
 and pos = {line : int ; characters : int}

let rec  startpos e =
  (match e with
   |Unit pos |Bool (_,pos) |Int (_,pos) |Float (_,pos) |Var (_,pos)
    ->pos
   |Not t |Neg t |Add (t,_) |Sub (t,_) |Mul (t,_) | Div (t,_)
    |FNeg t|FAdd (t,_) |FSub (t,_) |FMul (t,_) |FDiv (t,_) |Eq (t,_)
    |LE (t,_) |If (t,_,_) |App (t,_) |Tuple (t::_) |Array (t,_) | Get (t,_) |Put (t,_,_)
    ->startpos t
   |Let (_,t,_)|LetTuple (_,t,_)
    ->startpos t
   |LetRec ({name = _,pos;args = _;body =_},_)
    ->pos)
                                          
