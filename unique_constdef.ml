open KNormal


let find x env = try M.find x env with Not_found -> x (* 置換のための関数 (caml2html: beta_find) *)

let rec g env const_var = function
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
                      
  | IfEq(x, y, e1, e2) ->
     IfEq(find x env, find y env, g env const_var e1, g env const_var e2)
  | IfLE(x, y, e1, e2) ->
     IfLE(find x env, find y env, g env const_var e1, g env const_var e2)
  | Let((x,t),(Int(_) as const),e2)
    |Let((x,t),(Float(_) as const),e2)->
     if List.mem_assoc const const_var then
       let x'=List.assoc const const_var in
       g (M.add x x' env) const_var e2
     else
       Let((x,t),const,g env ((const,x)::const_var) e2)
     
  | Let((x, t), e1, e2) -> 
	  Let((x, t), g env const_var e1, g env const_var e2)
  | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
     LetRec({ name = xt; args = yts; body = g M.empty [] e1 },
            g env const_var e2)
  | Var(x) -> Var(find x env)
  | Tuple(xs) -> Tuple(List.map (fun x -> find x env) xs)
  | LetTuple(xts, y, e) -> LetTuple(xts, find y env, g env const_var e)
  | Get(x, y) -> Get(find x env, find y env)
  | Put(x, y, z) -> Put(find x env, find y env, find z env)
  | App(g, xs) -> App(find g env, List.map (fun x -> find x env) xs)
  | ExtArray(x) -> ExtArray(x)
  | ExtFunApp(x, ys) -> ExtFunApp(x, List.map (fun y -> find y env) ys)
  | Let_Ref((x,t),e1,e2) ->
     Let_Ref((x,t),g env const_var e1,g env const_var e2)
  | Ref_Get(x) ->Ref_Get(find x env)
  | Ref_Put(x,y) ->Ref_Put(find x env,find y env)
  | ForLE(((i,a),(j,k),step),e) ->
     ForLE(((find i env,find a env),(find j env,find k env),g env const_var step),
           g env const_var e)
  | LetPara({pargs=xts;
             index =cs
            ;accum=acc
            ;pbody=e1},e2) ->
     LetPara({pargs=xts;
              index=cs;
              accum=acc;
              pbody= e1},
             g env const_var e2)
            
  |Run_parallel(a,d,xs,ys)->
    let ys'=List.map (fun (y,i) ->(find y env,i)) ys in
    Run_parallel(find a env,find d env,( List.map (fun x -> find x env) xs),ys')
  |Accum(a,n,x) ->
    Accum(find  a env,find n env,find x env)
          

  let f e = g M.empty [] e
