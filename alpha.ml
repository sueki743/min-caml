(* rename identifiers to make them unique (alpha-conversion) *)

open KNormal

let find x env = try M.find x env with Not_found -> x
let find' x' env =
  match x' with
  |Id.V(x) ->Id.V(find x env)
  |Id.C(i) ->Id.C(i)

let rec g env = function (* α変換ルーチン本体 (caml2html: alpha_g) *)
  | Unit -> Unit
  | Int(i) -> Int(i)
  | Float(d) -> Float(d)
  | Neg(x) -> Neg(find x env)
  | Add(x, y) -> Add(find x env, find y env)
  | Sub(x, y) -> Sub(find x env, find y env)
  | Mul(x, y) -> Mul(find x env, find y env)
  | Div(x, y) -> Div(find x env, find y env)
  | FNeg(x) -> FNeg(find x env)
  | FAdd(x, y) -> FAdd(find x env, find y env)
  | FSub(x, y) -> FSub(find x env, find y env)
  | FMul(x, y) -> FMul(find x env, find y env)
  | FDiv(x, y) -> FDiv(find x env, find y env)
  | Ftoi(x) ->Ftoi(find x env)
  | Itof(x) ->Itof(find x env)
  | FAbs(x) ->FAbs(find x env)
  | FSqrt(x) ->FSqrt(find x env)
  | Read_int(x) ->Read_int(find x env)
  | Read_float(x) ->Read_float(find x env)
  | Print_char(x) ->Print_char(find x env)
 | IfEq(x, y, e1, e2) -> IfEq(find x env, find y env, g env e1, g env e2)
  | IfLE(x, y, e1, e2) -> IfLE(find x env, find y env, g env e1, g env e2)
  | Let((x, t), e1, e2) -> (* letのα変換 (caml2html: alpha_let) *)
      let x' = Id.genid x in
      Let((x', t), g env e1, g (M.add x x' env) e2)
  | Let_Ref((x, t), e1, e2) ->
      let x' = Id.genid x in
      Let_Ref((x', t), g env e1, g (M.add x x' env) e2)
  | Var(x) -> Var(find x env)
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* let recのα変換 (caml2html: alpha_letrec) *)
      let env = M.add x (Id.genid x) env in
      let ys = List.map fst yts in
      let env' = M.add_list2 ys (List.map Id.genid ys) env in
      LetRec({ name = (find x env, t);
	       args = List.map (fun (y, t) -> (find y env', t)) yts;
	       body = g env' e1 },
	     g env e2)
  | App(x, ys) -> App(find x env, List.map (fun y -> find y env) ys)
  | Tuple(xs) -> Tuple(List.map (fun x -> find x env) xs)
  | LetTuple(xts, y, e) -> (* LetTupleのα変換 (caml2html: alpha_lettuple) *)
      let xs = List.map fst xts in
      let env' = M.add_list2 xs (List.map Id.genid xs) env in
      LetTuple(List.map (fun (x, t) -> (find x env', t)) xts,
	       find y env,
	       g env' e)
  | Get(x, y) -> Get(find x env, find y env)
  | Put(x, y, z) -> Put(find x env, find y env, find z env)
  | ExtArray(x) -> ExtArray(x)
  | ExtFunApp(x, ys) -> ExtFunApp(x, List.map (fun y -> find y env) ys)
                                 
  | ForLE(((i,a),(j,k),step),e) ->
     ForLE(((find i env,find a env),(find j env,find k env),g env step),
           g env e)
  | Ref_Get(x)->Ref_Get(find x env)
  | Ref_Put(x,y)->Ref_Put(find x env,find y env)
  | LetPara({pargs=xts;
             index =(i,(j,k))
             ;accum=acc
             ;pbody=e1},e2) ->
      let xs = List.map fst xts in
      let env' = M.add_list2 (i::xs) (List.map Id.genid (i::xs)) env in
      let acc'=List.map
                 (fun acum ->
                   List.map
                     (fun (a,pos) ->(find a env' ,pos)) acum)
                 acc
      in

     LetPara({pargs=List.map (fun (x,t) ->(find x env',t)) xts;
              index=(find i env',(find' j env',find' k env'));
              accum=acc';
              pbody=g env' e1},
             g env e2)
  | Run_parallel (a,d,xs,ys)->
     let ys'=List.map (fun (y,i) ->(find y env,i)) ys in
     Run_parallel (find a env,find d env,List.map (fun x ->find x env) xs,ys')
  |Accum(a,n,x) ->Accum(find a env,find n env,find x env)
                         

let rec subst env = function (* 代入*)
  | Unit -> Unit
  | Int(i) -> Int(i)
  | Float(d) -> Float(d)
  | Neg(x) -> Neg(find x env)
  | Add(x, y) -> Add(find x env, find y env)
  | Sub(x, y) -> Sub(find x env, find y env)
  | Mul(x, y) -> Mul(find x env, find y env)
  | Div(x, y) -> Div(find x env, find y env)
  | FNeg(x) -> FNeg(find x env)
  | FAdd(x, y) -> FAdd(find x env, find y env)
  | FSub(x, y) -> FSub(find x env, find y env)
  | FMul(x, y) -> FMul(find x env, find y env)
  | FDiv(x, y) -> FDiv(find x env, find y env)
  | Ftoi(x) ->Ftoi(find x env)
  | Itof(x) ->Itof(find x env)
  | FAbs(x) ->FAbs(find x env)
  | FSqrt(x) ->FSqrt(find x env)
  | Read_int(x) ->Read_int(find x env)
  | Read_float(x) ->Read_float(find x env)
  | Print_char(x) ->Print_char(find x env)
  | IfEq(x, y, e1, e2) -> IfEq(find x env, find y env, subst env e1, subst env e2)
  | IfLE(x, y, e1, e2) -> IfLE(find x env, find y env, subst env e1, subst env e2)
  | Let((x, t), e1, e2) -> 
     Let((x, t), subst env e1, subst env e2)
  | Let_Ref((x, t), e1, e2) ->
     Let_Ref((x, t), subst env e1, subst env e2)
  | Var(x) -> Var(find x env)
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* let recのα変換 (caml2html: alpha_letrec) *)
     LetRec({ name = (find x env, t);
	      args =yts;
	      body = subst env e1 },
	    subst env e2)
  | App(x, ys) -> App(find x env, List.map (fun y -> find y env) ys)
  | Tuple(xs) -> Tuple(List.map (fun x -> find x env) xs)
  | LetTuple(xts, y, e) -> (* LetTupleのα変換 (caml2html: alpha_lettuple) *)
      LetTuple(List.map (fun (x, t) -> (find x env, t)) xts,
	       find y env,
	       subst env e)
  | Get(x, y) -> Get(find x env, find y env)
  | Put(x, y, z) -> Put(find x env, find y env, find z env)
  | ExtArray(x) -> ExtArray(x)
  | ExtFunApp(x, ys) -> ExtFunApp(x, List.map (fun y -> find y env) ys)
                                 
  | ForLE(((i,a),(j,k),step),e) ->
     ForLE(((find i env,find a env),(find j env,find k env),subst env step),
           subst env e)
  | Ref_Get(x)->Ref_Get(find x env)
  | Ref_Put(x,y)->Ref_Put(find x env,find y env)
  | LetPara({pargs=xts;
             index =(i,(j,k))
             ;accum=acc
             ;pbody=e1},e2) ->
      let acc'=List.map
                 (fun acum ->
                   List.map
                     (fun (a,pos) ->(find a env ,pos)) acum)
                 acc
      in

     LetPara({pargs=List.map (fun (x,t) ->(find x env,t)) xts;
              index=(i,(find' j env,find' k env));
              accum=acc';
              pbody=g env e1},
             g env e2)
  | Run_parallel (a,d,xs,ys)->
     let ys'=List.map (fun (y,i) ->(find y env,i)) ys in
     Run_parallel (find a env,find d env,List.map (fun x ->find x env) xs,ys')
  |Accum(a,n,x) ->Accum(find a env,find n env,find x env)                         

let f = g M.empty
