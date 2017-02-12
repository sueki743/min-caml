open Asm

let find env x' =
  match x' with
  |V(a) ->if M.mem a env then C(M.find a env)
          else x'
  |C(i) ->C(i)
       
let rec g env  = function (* 命令列の16bit即値最適化 (caml2html: simm13_g) *)
    
  | Ans(exp) -> Ans(g' env exp)
  | Let((x, Type.Ref t),exp,e) ->(*xがref型の時は定数でも登録しない*)
     Let((x, Type.Ref t),g' env exp,g env e)
  | Let((x, t), Movi(i), e)
       when (-32768 <= i) && (i < 32768) ->
      let e' = g (M.add x i env) e in
      if List.mem x (fv e') then Let((x, t), Movi(i), e') else
      ((* Format.eprintf "erased redundant Set to %s@." x; *)
       e')
  | Let((x,t),La(lavel),e2) as e -> (*無駄なlaを除去 *)
     if List.mem x (fv e2) then e else e2
  | Let(xt, exp, e) -> Let(xt, g' env exp, g env e)
and g' env = function (* 各命令の13bit即値最適化 (caml2html: simm13_gprime) *)
  | Add(x, V(y)) when M.mem y env -> Add(x, C(M.find y env))
  | Add(x, V(y)) when M.mem x env -> Add(y, C(M.find x env))
  | IfEq(x, V(y), e1, e2) when M.mem y env -> IfEq(x, C(M.find y env), g env e1, g env e2)
  | IfLE(x, V(y), e1, e2) when M.mem y env -> IfLE(x, C(M.find y env), g env e1, g env e2)
  | IfEq(x, V(y), e1, e2) when M.mem x env -> IfEq(y, C(M.find x env), g env e1, g env e2)
  | IfLE(x, V(y), e1, e2) when M.mem x env -> IfLE(y, C((M.find x env)-1), g env e2, g env e1)
  |ForLE(((i,a'),(j',k'),step),e) ->
    ForLE(((i,find env a'),(find env j',find env k'),g env step),g env e)
  | IfEq(x, y', e1, e2) -> IfEq(x, y', g env e1, g env e2)
  | IfLE(x, y', e1, e2) -> IfLE(x, y', g env e1, g env e2)
  | IfFZ(x, e1, e2) -> IfFZ(x, g env e1, g env e2)
  | IfFLE(x, y, e1, e2) -> IfFLE(x, y, g env e1, g env e2)
  | e -> e

let h { name = l; args = xs; fargs = ys; body = e; ret = t } = (* トップレベル関数の16bit即値最適化 *)
  { name = l; args = xs; fargs = ys; body = g M.empty e; ret = t }

let i =function
  |Some {pargs=xs;
         pfargs=ys;
         index=(i,(j',k'));
         pbody=e} ->

    Some {pargs=xs;
          pfargs=ys;
          index=(i,(j',k'));
          pbody=g M.empty e}
  |None ->None
                                        
    
let f (Prog(data, fundefs,parallel, e)) = (* プログラム全体の13bit即値最適化 *)
  Prog(data, List.map h fundefs,i parallel, g M.empty e)
