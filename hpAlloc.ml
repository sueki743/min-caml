open KNormal

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
 and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

type arraydef = {name :Id.l * Type.t;
                 size :int;
                 initv:t }

type tupledef = {name :Id.l * Type.t;
                 body:t list}

(*Etype prog = Prog of (arraydef list) * (tupledef list) * t*)

let arrays :(arraydef list ref) = ref [](*静的割り当て配列*)
                                      
let tuples :(tupledef list ref) = ref [](*静的割り当て組*)

                                    
let rec eval constenv = function(*定数なら値を評価*)
  |Unit|Int(_)|Float(_)|ConstTuple(_)|ConstArray(_) as const ->
    Some const
  |Add(x,y) when M.mem x constenv&&M.mem y constenv ->
    let v1=(match M.find x constenv with
            |(Int(i),_)->i|_ ->assert false) in
    let v2=(match M.find y constenv with
            |(Int(i),_)->i|_ ->assert false) in          
    Some (Int(v1+v2))
  |Sub(x,y) when M.mem x constenv&&M.mem y constenv ->
    let v1=(match M.find x constenv with
            |(Int(i),_)->i|_ ->assert false) in
    let v2=(match M.find y constenv with
            |(Int(i),_)->i|_ ->assert false) in          
    Some (Int(v1-v2))
  |Mul(x,y) when M.mem x constenv&&M.mem y constenv ->
    let v1=(match M.find x constenv with
            |(Int(i),_)->i|_ ->assert false) in
    let v2=(match M.find y constenv with
            |(Int(i),_)->i|_ ->assert false) in          
    Some (Int(v1*v2))
  |Div(x,y) when M.mem x constenv&&M.mem y constenv ->
    let v1=(match M.find x constenv with
            |(Int(i),_)->i|_ ->assert false) in
    let v2=(match M.find y constenv with
            |(Int(i),_)->i|_ ->assert false) in          
    Some (Int(v1/v2))
  |Neg(x) when M.mem x constenv ->
    let v1=(match M.find x constenv with
            |(Int(i),_)->i|_->assert false) in
    Some (Int(-v1))
  |FNeg(x) when M.mem x constenv ->
    let v1=(match M.find x constenv with
            |(Float(d),_)->d|_->assert false) in
    Some (Float(-.v1))
  |FAdd(x,y) when M.mem x constenv &&M.mem y constenv ->
    let v1=(match M.find x constenv with
            |(Float(d),_)->d|_->assert false) in
    let v2=(match M.find y constenv with
            |(Float(d),_)->d|_->assert false) in
    Some (Float(v1+.v2))
  |FSub(x,y) when M.mem x constenv &&M.mem y constenv ->
    let v1=(match M.find x constenv with
            |(Float(d),_)->d|_->assert false) in
    let v2=(match M.find y constenv with
            |(Float(d),_)->d|_->assert false) in
    Some (Float(v1-.v2))
  |FMul(x,y) when M.mem x constenv &&M.mem y constenv ->
    let v1=(match M.find x constenv with
            |(Float(d),_)->d|_->assert false) in
    let v2=(match M.find y constenv with
            |(Float(d),_)->d|_->assert false) in
    Some (Float(v1*.v2))
  |FDiv(x,y) when M.mem x constenv &&M.mem y constenv ->
    let v1=(match M.find x constenv with
            |(Float(d),_)->d|_->assert false) in
    let v2=(match M.find y constenv with
            |(Float(d),_)->d|_->assert false) in
    Some (Float(v1/.v2))
  |IfEq(_)|IfLE(_)->None (*if文は追わない*)
  |Let((x,t),e1,e2) ->
    (match eval constenv e1 with
     |Some const ->eval (M.add x (const,t) constenv) e2
     |None -> eval constenv e2)
  |Var(x) when M.mem x constenv->
    let (const,_)=M.find x constenv in
    Some const
  |LetRec(f,e1)->
    eval constenv e1
  |App _ ->None(*関数呼び出しは追わない*)
  |Tuple _->None(*constTupleへの変換はgが行っている*)
  |LetTuple(xts,y,e)->
    (try
      (match M.find y constenv with
       |ConstTuple(l),_->
         (match List.find (fun {name=(x,_);body=_} ->l=x) !tuples with
          |{name=_;body=y'}->
            let constenv'=List.fold_left2
                            (fun env (id,t) const ->M.add id (const,t) env)
                            constenv
                            xts
                            y' in
            eval constenv' e)
       |_ ->assert false)
    with
      Not_found->eval constenv e)
  |Get _|Put _ |ExtArray _|ExtFunApp _->None
  |_ ->None


let rec g_unchange =function(*knormal.t->hpAlloc.t、そのまま変換*)
  | KNormal.Unit -> Unit
  | KNormal.Int(i) -> Int(i)
  | KNormal.Float(d) -> Float(d)
  | KNormal.Neg(x) -> Neg(x)
  | KNormal.Add(x, y) -> Add(x, y)
  | KNormal.Sub(x, y) -> Sub(x, y)
  | KNormal.Mul(x, y) -> Mul(x, y)
  | KNormal.Div(x, y) -> Div(x, y)
  | KNormal.FNeg(x) -> FNeg(x)
  | KNormal.FAdd(x, y) -> FAdd(x, y)
  | KNormal.FSub(x, y) -> FSub(x, y)
  | KNormal.FMul(x, y) -> FMul(x, y)
  | KNormal.FDiv(x, y) -> FDiv(x, y)
  | KNormal.IfEq(x, y, e1, e2) -> IfEq(x, y, g_unchange e1, g_unchange e2)
  | KNormal.IfLE(x, y, e1, e2) -> IfLE(x, y, g_unchange e1, g_unchange e2)
  | KNormal.Let((x, t),e1, e2) -> Let((x,t),g_unchange e1,g_unchange e2)
  | KNormal.Var(x) -> Var(x)
  | KNormal.LetRec({KNormal.name=(x,t);KNormal.args=ys;KNormal.body=e}, e2) ->
     let e'=g_unchange e in
     LetRec({name=(x,t);args=ys;body=e'},g_unchange e2)
  | KNormal.App(f, xs) -> App(f, xs)
  | KNormal.Tuple(xs) ->Tuple(xs)
  | KNormal.LetTuple(xts, y, e) -> LetTuple(xts, y, g_unchange e)
  | KNormal.Get(x, y) -> Get(x, y)
  | KNormal.Put(x, y, z) -> Put(x, y, z)
  | KNormal.ExtArray(x) -> ExtArray(x)
  | KNormal.ExtFunApp(x, ys) ->ExtFunApp(x,ys)

         
let rec g constenv = function
    (*constenv: 変数->z(定数(t型),その型)*)
  | KNormal.Unit -> Unit
  | KNormal.Int(i) -> Int(i)
  | KNormal.Float(d) -> Float(d)
  | KNormal.Neg(x) -> Neg(x)
  | KNormal.Add(x, y) -> Add(x, y)
  | KNormal.Sub(x, y) -> Sub(x, y)
  | KNormal.Mul(x, y) -> Mul(x, y)
  | KNormal.Div(x, y) -> Div(x, y)
  | KNormal.FNeg(x) -> FNeg(x)
  | KNormal.FAdd(x, y) -> FAdd(x, y)
  | KNormal.FSub(x, y) -> FSub(x, y)
  | KNormal.FMul(x, y) -> FMul(x, y)
  | KNormal.FDiv(x, y) -> FDiv(x, y)
  | KNormal.IfEq(x, y, e1, e2) -> IfEq(x, y, g constenv e1, g constenv e2)
  | KNormal.IfLE(x, y, e1, e2) -> IfLE(x, y, g constenv e1, g constenv e2)
  | KNormal.Let((x, t),e1, e2) ->
     let e1'=g constenv e1 in
     (match eval constenv e1' with
     |Some const ->(*定数*)
        let e2'=g (M.add x (const,t) constenv) e2 in
        Let((x,t), e1', e2')
     |None ->
       let e2' = g constenv e2 in
       Let((x,t), e1' , e2'))
  | KNormal.Var(x) -> Var(x)
  | KNormal.LetRec({KNormal.name=(x,t);KNormal.args=ys;KNormal.body=e}, e2) ->
     let e'=g_unchange e in
     LetRec({name=(x,t);args=ys;body=e'},g constenv e2)
  | KNormal.App(f, xs) -> App(f, xs)
  | KNormal.Tuple(xs) ->
     (try
        let const_xs_ts =List.map (fun x ->M.find x constenv) xs in
        let (const_xs,ts) =List.split const_xs_ts in
        let t=Type.Tuple(ts) in
        let x=Id.genid "const_tuple" in
        (tuples := {name=(Id.L(x),t);body=const_xs}::!tuples);
        ConstTuple(Id.L(x))
      with
        Not_found->Tuple(xs))
  | KNormal.LetTuple(xts, y, e) ->
     (try
       (match M.find y constenv with(*yの要素の一部が定数の場合はまでは考えない*)
        |ConstTuple(l),_->
          (match List.find (fun {name=(x,_);body=_} ->l=x) !tuples with
           |{name=_;body=y'}->
             let constenv'=List.fold_left2
                             (fun env (id,t) const ->M.add id (const,t) env)
                             constenv
                             xts
                             y' in
             LetTuple(xts,y,g constenv' e))
        |_ ->assert false)
     with
       Not_found -> LetTuple(xts, y, g constenv e))
  | KNormal.Get(x, y) -> Get(x, y)
  | KNormal.Put(x, y, z) -> Put(x, y, z)
  | KNormal.ExtArray(x) -> ExtArray(x)
  | KNormal.ExtFunApp(l, [arg1;arg2]) when (l="create_array"||l="create_float_array")->
     (*sizeとinitvの型はID.t*)
     (try
        let arg1'=(match M.find arg1 constenv with (Int(i),_) ->i |_ ->assert false) in(*sizeの値をconstenvから検索*)
        let (arg2',t2)=M.find arg2 constenv in(*arg2の値を検索*)
        let x=Id.genid "const_array" in
        (arrays := {name=(Id.L(x),Type.Array(t2));size=arg1';initv=arg2'}::!arrays);
        ConstArray(Id.L(x))
      with Not_found ->(*size,initvが定数でなかった場合*)
           ExtFunApp(l, [arg1;arg2]))
  | KNormal.ExtFunApp(x, ys) ->ExtFunApp(x,ys)



                                        
let f e =
  let e'=g (M.empty) e in
  arrays:=List.rev !arrays;
  tuples:=List.rev !tuples;(*定義順に*)
  e'
