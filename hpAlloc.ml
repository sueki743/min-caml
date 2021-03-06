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
                   
  |ForLE of ((Id.t* Id.t) * (Id.t * Id.t) * t) *t
  |Let_Ref of (Id.t * Type.t) *t *t
  |Ref_Get of Id.t
  |Ref_Put of Id.t * Id.t

  |LetPara of parallel * t
  |Run_parallel of Id.t*Id.t*Id.t list*(Id.t*int) list
  |Accum of Id.t*Id.t*Id.t
                       

 and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

 and parallel ={pargs :(Id.t *Type.t) list;
                index:(Id.t*(Id.vc*Id.vc)) ;
                accum:(Id.t*int) list list ;
                pbody : t }

              
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
  |Ftoi(x) when M.mem x constenv ->
    let v1=(match M.find x constenv with
            |(Float(d),_)->d|_->assert false) in
    Some (Int(int_of_float(v1)))
  |Itof(x) when M.mem x constenv ->
    let v1=(match M.find x constenv with
            |(Int(i),_)->i|_->assert false) in
    Some (Float(float_of_int(v1)))
  |FAbs(x) when M.mem x constenv ->
    let v1=(match M.find x constenv with
            |(Float(d),_)->d|_->assert false) in
    Some (if(v1<0.0)then(Float(-.v1)) else Float(v1))
  |FSqrt(x) when M.mem x constenv ->
    let v1=(match M.find x constenv with
            |(Float(d),_)->d|_->assert false) in
    Some(Float(sqrt(v1)))
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
  |Let_Ref(_,e1,e2) ->eval constenv e2
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
  | KNormal.Ftoi(x) ->Ftoi(x)
  | KNormal.Itof(x) ->Itof(x)
  | KNormal.FAbs(x) ->FAbs(x)
  | KNormal.FSqrt(x) ->FSqrt(x)
  | KNormal.Read_int(x) ->Read_int(x)
  | KNormal.Read_float(x) ->Read_float(x)
  | KNormal.Print_char(x) ->Print_char(x)
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
  | KNormal.ForLE((a,b,step),e) ->ForLE((a,b,g_unchange step),g_unchange e)
  | KNormal.Let_Ref(xt,e1,e2) ->Let_Ref(xt,g_unchange e1,g_unchange e2)
  | KNormal.Ref_Get(x) ->Ref_Get(x)
  | KNormal.Ref_Put(x,y) ->Ref_Put(x,y) 
  | KNormal.LetPara({KNormal.pargs=xts;
                     KNormal.index=(i,(j',k'));
                     KNormal.accum=acc;
                     KNormal.pbody=e1},e2) ->
     LetPara({pargs=xts
             ;index =(i,(j', k'))
             ;accum=acc
             ;pbody=g_unchange e1},g_unchange e2)
  |KNormal.Run_parallel(a,d,xs,ys) ->Run_parallel(a,d,xs,ys)
  |KNormal.Accum(a,n,x)->Accum(a,n,x)


let not_changed_array =ref []

                           
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
  | KNormal.Ftoi(x) ->Ftoi(x)
  | KNormal.Itof(x) ->Itof(x)
  | KNormal.FAbs(x) ->FAbs(x)
  | KNormal.FSqrt(x) ->FSqrt(x)
  | KNormal.Read_int(x) ->Read_int(x)
  | KNormal.Read_float(x) ->Read_float(x)
  | KNormal.Print_char(x) ->Print_char(x)
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
  | KNormal.App(f, xs) -> not_changed_array:=[];App(f, xs)
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
  | KNormal.Get(x, y) when M.mem x constenv->
     (match M.find x constenv with
      |ConstArray(l),_->
        if(List.mem l !not_changed_array) then(*配列が初期値から変更なしの場合*)
          (let a=List.find
                  (fun {name=(l',_);size=_;initv=_}->l'=l)
                  !arrays in
          (match a with
           |{name=_;size=_;initv=const}->const))
        else
          Get(x,y)
      |_ ->assert false)
  | KNormal.Get(x, y) -> Get(x, y)
  | KNormal.Put(x, y, z) when M.mem x constenv ->
     (match M.find x constenv with
      |ConstArray(l),_->not_changed_array:=(List.filter (fun l' ->not (l=l'))
                                                        !not_changed_array);
                      Put(x,y,z)
      |_ ->assert false)
  | KNormal.Put(x, y, z) -> Put(x, y, z)
  | KNormal.ExtArray(x) -> ExtArray(x)
  | KNormal.ExtFunApp(l, [arg1;arg2]) when (l="create_array"||l="create_float_array")->
     (*sizeとinitvの型はID.t*)
     (try
        let arg1'=(match M.find arg1 constenv with (Int(i),_) ->i |_ ->assert false) in(*sizeの値をconstenvから検索*)
        let (arg2',t2)=M.find arg2 constenv in(*arg2の値を検索*)
        let x=Id.genid "const_array" in
        (arrays := {name=(Id.L(x),Type.Array(t2));size=arg1';initv=arg2'}::!arrays);
        not_changed_array:=(Id.L(x))::!not_changed_array;
        ConstArray(Id.L(x))
      with Not_found ->(*size,initvが定数でなかった場合*)
           ExtFunApp(l, [arg1;arg2]))
  | KNormal.ExtFunApp(x, ys) ->ExtFunApp(x,ys)
  | KNormal.ForLE((a,b,step),e) ->ForLE((a,b,g_unchange step),g_unchange e)
  | KNormal.Let_Ref(xt,e1,e2) ->Let_Ref(xt,g constenv e1,g constenv e2)
  | KNormal.Ref_Get(x) ->Ref_Get(x)
  | KNormal.Ref_Put(x,y) ->Ref_Put(x,y)
  | KNormal.LetPara({KNormal.pargs=xts;
                     KNormal.index=(i,(j',k'));
                     KNormal.accum=acc;
                     KNormal.pbody=e1},e2) ->
     LetPara({pargs=xts
             ;index =((i,(j',k')))
             ;accum=acc
             ;pbody=g_unchange e1},g constenv e2)
  | KNormal.Run_parallel(a,d,xs,ys) ->not_changed_array:=[];Run_parallel(a,d,xs,ys)
  | KNormal.Accum(a,n,x) ->Accum(a,n,x)            



                                        
let f e =
  let e'=g (M.empty) e in
  arrays:=List.rev !arrays;
  tuples:=List.rev !tuples;(*定義順に*)
  e'
