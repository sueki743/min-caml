type closure = { entry : Id.l; actual_fv : Id.t list }
type t = (* クロージャ変換後の式 (caml2html: closure_t) *)
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
  | MakeCls of (Id.t * Type.t) * closure * t
  | AppCls of Id.t * Id.t list
  | AppDir of Id.l * Id.t list
  | Tuple of Id.t list
  | ConstTuple of Id.l
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ConstArray of Id.l
  | ExtArray of Id.l
  | Ftoi of Id.t
  | Itof of Id.t
  | FAbs of Id.t 
  | FSqrt of Id.t
  |Read_int of Id.t(*引数はunit型*)
  |Read_float of Id.t(*引数はunit型*)
  |Print_char of Id.t

  |ForLE of ((Id.t* Id.t) * (Id.t * Id.t) * t) *t
  |Let_Ref of (Id.t * Type.t) *t *t
  |Ref_Get of Id.t
  |Ref_Put of Id.t * Id.t

  |Run_parallel of Id.t*Id.t*Id.t list*(Id.t*int) list
  |Accum of Id.t *Id.t*Id.t

type fundef = { name : Id.l * Type.t;
		args : (Id.t * Type.t) list;
		formal_fv : (Id.t * Type.t) list;
		body : t }

type parallel ={pargs :(Id.t *Type.t) list;
                index:(Id.t*(Id.vc*Id.vc)) ;
                accum:(Id.t*int) list  list ;
                pbody : t }

                

type prog = Prog of (fundef list) *(parallel list)* t

let toplevel : fundef list ref = ref []
let parallel_part : parallel list ref =ref []
                                      
let rec fv = function
  | Unit | Int(_) | Float(_) | ExtArray(_)|ConstArray(_)|ConstTuple(_) -> S.empty
  | Neg(x) | FNeg(x)|Ref_Get(x) -> S.singleton x
  | Add(x, y) | Sub(x, y)| Mul(x,y)| Div(x,y) | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | Get(x, y)|Ref_Put(x,y) -> S.of_list [x; y]
  | IfEq(x, y, e1, e2)| IfLE(x, y, e1, e2) -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | Let((x, t), e1, e2) -> S.union (fv e1) (S.remove x (fv e2))
  | Let_Ref((x,t),e1,e2)-> S.union (fv e1) (S.remove x (fv e2))
  | Var(x) -> S.singleton x
  | MakeCls((x, t), { entry = l; actual_fv = ys }, e) -> S.remove x (S.union (S.of_list ys) (fv e))
  | AppCls(x, ys) -> S.of_list (x :: ys)
  | AppDir(_, xs) | Tuple(xs) -> S.of_list xs
  | LetTuple(xts, y, e) -> S.add y (S.diff (fv e) (S.of_list (List.map fst xts)))
  | Put(x, y, z) -> S.of_list [x; y; z]
  | Ftoi (x) | Itof (x)|Read_int(x)|Read_float(x)|Print_char(x) ->S.singleton x
  | FAbs (x) |FSqrt (x) ->S.of_list [x]
  | ForLE(((i,a),(j,k),step),e1)->
     S.union (S.of_list [j;k]) (S.union (fv step) (fv e1))
  | Run_parallel(a,d,xs,ys) ->
     let ys'=List.map fst ys in
     S.of_list (a::((d::xs)@ys'))
  | Accum(a,n,x) ->S.of_list [a;n;x]
     
                                      
                                    

let const_fv constenv e =
  S.filter (fun x->M.mem x constenv) (fv e) 
    
      
let rec insert_const constenv = function
  |Let(xt,e1,e2) ->
    let const_set = const_fv constenv e1 in
    (*constenvからconst_set中の変数を削除*)
    let constenv' = M.filter (fun x ->(fun ct->not (S.mem x const_set))) constenv in
    S.fold (fun x exp ->let (const,t)=M.find x constenv in
                        Let((x,t),const,exp))
             const_set
             (Let(xt,e1,(insert_const constenv' e2)))
  |LetTuple(xts,y,e) ->
    (try
       let (const,t) =M.find y constenv in
       let constenv'=M.remove y constenv in
       let e'=insert_const constenv' e in
       Let((y,t),const,(LetTuple(xts,y,e')))
     with
       Not_found ->LetTuple(xts,y,insert_const constenv e))
  |Let_Ref(xt,e1,e2) ->
    let const_set = const_fv constenv e1 in
    (*constenvからconst_set中の変数を削除*)
    let constenv' = M.filter (fun x ->(fun ct->not (S.mem x const_set))) constenv in
    S.fold (fun x exp ->let (const,t)=M.find x constenv in
                        Let((x,t),const,exp))
           const_set
           (Let_Ref(xt,e1,(insert_const constenv' e2)))
  |ForLE(cs,e1) as e ->
    let const_set = const_fv constenv e in
        S.fold (fun x exp ->let (const,t)=M.find x constenv in
                        Let((x,t),const,exp))
             const_set
             (ForLE(cs,e1))
    
  |e ->
    let const_set = const_fv constenv e in
    S.fold (fun x exp ->let (const,t)=M.find x constenv in
                          Let((x,t),const,exp))
             const_set
             e
let added_args = ref []    
                                     
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
  |MakeCls(x,cls,e)->eval constenv e
  |AppCls _|AppDir _ ->None(*関数呼び出しは追わない*)
  |Tuple _->None
  |LetTuple(xts,y,e)->
    (try
      (match M.find y constenv with
       |ConstTuple(l),_->
         (match
            List.find (fun {HpAlloc.name=(x,_);HpAlloc.body=_} ->l=x) !HpAlloc.tuples
          with
          |{HpAlloc.name=_;HpAlloc.body=y'}->
            let constenv'=List.fold_left2
                            (fun env (id,t) const ->
                              let const = g M.empty M.empty S.empty const in
                              (*t型に変換*)
                              M.add id (const,t) env)
                            constenv
                            xts
                            y' in
            eval constenv' e)
       |_ ->assert false)
    with
      Not_found->eval constenv e)
  |Get _|Put _ |ExtArray _->None
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
    (if (v1>0.0) then
        Some (Float(v1))
      else
        Some (Float(-.v1)))
  |FSqrt(x) when M.mem x constenv ->
    let v1=(match M.find x constenv with
            |(Float(d),_)->d|_->assert false) in
    Some (Float(sqrt(v1)))
  |Let_Ref((x,t),_,e2) ->eval constenv e2
  |_ ->None



and g env constenv known = function (* クロージャ変換ルーチン本体 (caml2html: closure_g) *)
  (*env      :変数->型　の環境
　　constenv :定数変数->(定数(colosure.t),型)　の環境
    known    :直接適用可能な関数の集合*)
  | HpAlloc.Unit -> Unit
  | HpAlloc.Int(i) -> Int(i)
  | HpAlloc.Float(d) -> Float(d)
  | HpAlloc.Neg(x) -> Neg(x)
  | HpAlloc.Add(x, y) -> Add(x, y)
  | HpAlloc.Sub(x, y) -> Sub(x, y)
  | HpAlloc.Mul(x, y) -> Mul(x, y)
  | HpAlloc.Div(x, y) -> Div(x, y)
  | HpAlloc.FNeg(x) -> FNeg(x)
  | HpAlloc.FAdd(x, y) -> FAdd(x, y)
  | HpAlloc.FSub(x, y) -> FSub(x, y)
  | HpAlloc.FMul(x, y) -> FMul(x, y)
  | HpAlloc.FDiv(x, y) -> FDiv(x, y)
  | HpAlloc.Ftoi(x)->Ftoi(x)
  | HpAlloc.Itof(x)->Itof(x)
  | HpAlloc.FAbs(x)->FAbs(x)
  | HpAlloc.FSqrt(x)->FSqrt(x)
  | HpAlloc.Read_int(x)->Read_int(x)
  | HpAlloc.Read_float(x)->Read_float(x)
  | HpAlloc.Print_char(x)->Print_char(x)
  | HpAlloc.Accum(a,n,x) ->Accum(a,n,x)
  | HpAlloc.IfEq(x, y, e1, e2) -> IfEq(x, y, g env constenv known e1, g env constenv known e2)
  | HpAlloc.IfLE(x, y, e1, e2) -> IfLE(x, y, g env constenv known e1, g env constenv known e2)
  | HpAlloc.Let((x, t),e1, e2) ->
     let e1'=g env constenv known e1 in
     (match eval constenv e1' with
      |Some const ->let e2'=g (M.add x t env) (M.add x (const,t) constenv) known e2 in
                    Let((x,t),e1',e2')(*x定数でもe1'は副作用ある可能性がある*)
                    (*if(S.mem x (fv e2')) then
                      Let((x,t),const,e2')
                    else
                      e2'(*xの定義不要*)*)
      |None ->Let((x,t),e1',g (M.add x t env) constenv known e2))
  | HpAlloc.Var(x) -> Var(x)
  | HpAlloc.LetRec({ HpAlloc.name = (x, t); HpAlloc.args = yts; HpAlloc.body = e1 }, e2) -> (* 関数定義の場合 (caml2html: closure_letrec) *)
      (* 関数定義let rec x y1 ... yn = e1 in e2の場合は、
	 xに自由変数がない(closureを介さずdirectに呼び出せる)
	 と仮定し、knownに追加してe1をクロージャ変換してみる *)
      let toplevel_backup = !toplevel in
      let env' = M.add x t env in
      let known' = S.add x known in
      let e1' = g (M.add_list yts env') constenv  known' e1 in
      let e1'=insert_const constenv e1' in(*定数変数に定義文を入れる*)
      (* 本当に自由変数がなかったか、変換結果e1'を確認する *)
      (* 注意: e1'にx自身が変数として出現する場合はclosureが必要!
         (thanks to nuevo-namasute and azounoman; test/cls-bug2.ml参照) *)
      let zs = S.diff (fv e1') (S.of_list (List.map fst yts)) in
      let known', e1' =
	if S.is_empty zs then known', e1' else
	  (* 駄目だったら状態(toplevelの値)を戻して、クロージャ変換をやり直す *)
	  (Format.eprintf "free variable(s) %s found in function %s@." (Id.pp_list (S.elements zs)) x;
	   Format.eprintf "function %s cannot be directly applied in fact@." x;
	   toplevel := toplevel_backup;
	   let e1' = g (M.add_list yts env') constenv known e1 in
           let e1' = insert_const constenv e1' in
	   known, e1') in
      let zs = S.elements (S.diff (fv e1') (S.add x (S.of_list (List.map fst yts)))) in (* 自由変数のリスト *)
      let zts = List.map (fun z -> (z, M.find z env')) zs in (* ここで自由変数zの型を引くために引数envが必要 *)
      toplevel := { name = (Id.L(x), t); args = yts; formal_fv = zts; body = e1' } :: !toplevel; (* トップレベル関数を追加 *)
      let e2' = g env' constenv known' e2 in
      if S.mem x (fv e2') then (* xが変数としてe2'に出現するか *)
	MakeCls((x, t), { entry = Id.L(x); actual_fv = zs }, e2')
      else
	(*Format.eprintf "eliminating closure(s) %s@." x;*)
	 e2' (* 出現しなければMakeClsを削除 *)
  | HpAlloc.App(x, ys) when S.mem x known -> (* 関数適用の場合 (caml2html: closure_app) *)
     (*Format.eprintf "directly applying %s@." x;*)
      AppDir(Id.L(x), ys)
  | HpAlloc.App(f, xs) -> AppCls(f, xs)
  | HpAlloc.Tuple(xs) -> Tuple(xs)
  | HpAlloc.ConstTuple(l)->ConstTuple(l)
  | HpAlloc.LetTuple(xts, y, e) when M.mem y constenv ->
      (match M.find y constenv with
       |ConstTuple(l),_->
         (match
            List.find (fun {HpAlloc.name=(x,_);HpAlloc.body=_} ->l=x) !HpAlloc.tuples
          with
          |{HpAlloc.name=_;HpAlloc.body=y'}->
            let constenv'=List.fold_left2
                            (fun env (id,t) const ->
                              let const = g M.empty M.empty S.empty const in
                              (*t型に変換*)
                              M.add id (const,t) env)
                            constenv
                            xts
                            y' in
            let e'=g (M.add_list xts env) constenv' known e in
            LetTuple(xts, y, e'))
       |_ ->assert false)
  | HpAlloc.LetTuple(xts, y, e) -> LetTuple(xts, y, g (M.add_list xts env) constenv known e)
  | HpAlloc.Get(x, y) -> Get(x, y)
  | HpAlloc.Put(x, y, z) -> Put(x, y, z)
  | HpAlloc.ExtArray(x) -> ExtArray(Id.L(x))
  | HpAlloc.ConstArray(l)->ConstArray(l)
  | HpAlloc.ExtFunApp(x, ys) ->  AppDir(Id.L("min_caml_" ^ x), ys)
  | HpAlloc.ForLE((a,b,step),e) ->ForLE((a,b,g env constenv known step),g env constenv known e)
  | HpAlloc.Let_Ref((x,t),e1,e2) ->
     Let_Ref((x,t),g env constenv known e1,g (M.add x t env) constenv known e2)
  | HpAlloc.Ref_Get(x) ->Ref_Get(x)
  | HpAlloc.Ref_Put(x,y)->Ref_Put(x,y)
  | HpAlloc.LetPara({HpAlloc.pargs=xts;
                     HpAlloc.index=(i,(j,k));
                     HpAlloc.accum=acc;
                     HpAlloc.pbody=e1},
                    e2) ->
     (* let find_int x constenv = *)
     (*   match M.find x constenv with Int(i) ->i|_ ->assert false in *)
     (* j,k,dが引数になるか、ならないか *)
     (* let const_jkd,notC_jkd=List.partition (fun x ->M.mem x constenv) [j;k;d] in *)
     (* let arg_ajkd=if(List.mem a notC_jkd)then *)
     (*                List.filter (fun x ->x<>i) notC_ajkd *)
     (*              else *)
     (*                a::(List.filter (fun x ->x<>i) notC_ajkd) in *)
     (* let j'=if j=i||(not(List.mem j const_jkd)) then V(j) *)
     (*        else C(find_int j constenv) in *)
     (* let k'=if k=i||(not(List.mem k const_jkd)) then V(k) *)
     (*        else C(find_int k constenv) in *)
     (* let d'=if (not(List.mem d const_jkd)) then V(d) *)
     (*        else C(find_int d constenv) in *)
     let e1' = g env constenv known e1 in
     let e1' = insert_const constenv e1' in
     let xs = List.map fst xts in
     let zs =                   (* 自由変数 *)
       S.elements (S.diff (fv e1') (S.of_list (i::xs))) in
     let zts = List.map (fun z -> (z, M.find z env)) zs in
     (* let arg_ajkd'=List.map (fun z ->(z,M.find z env)) arg_ajkd in *)
     let parallel={pargs=xts@zts;
                   index=(i,(j,k));
                   accum=acc;
                   pbody=e1'}
     in
     added_args:=zts;
     parallel_part:=parallel::(!parallel_part);
     g env constenv known e2
  |HpAlloc.Run_parallel (a,d,xs,ys)->
    (assert ((List.length (!parallel_part))=1);
    let zts= !added_args in
    let zs = List.map fst zts in
    Run_parallel(a,d,xs@zs,ys))        (* 仮引数として追加されたものを、追加 *)
     
     
     
     
     
let f e =
  toplevel := [];
  let e' = g M.empty M.empty S.empty e in
  Prog(List.rev !toplevel, !parallel_part,e')
