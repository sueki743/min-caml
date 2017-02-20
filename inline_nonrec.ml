open KNormal

(* 非再帰関数を無差別に展開 *)

           

let rec g env = function (* インライン展開ルーチン本体 (caml2html: inline_g) *)
  | IfEq(x, y, e1, e2) -> IfEq(x, y, g env e1, g env e2)
  | IfLE(x, y, e1, e2) -> IfLE(x, y, g env e1, g env e2)
  | Let(xt, e1, e2) -> Let(xt, g env e1, g env e2)
  | Let_Ref(xt,e1,e2) ->Let_Ref(xt,g env e1,g env e2)
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* 関数定義の場合 (caml2html: inline_letrec) *)
     let env = if (S.mem x (fv e1))(*||(loop_exit e1)(*再帰関数か判定*)*)
               then env
               else M.add x (yts, e1) env in
      LetRec({ name = (x, t); args = yts; body = g env e1}, g env e2)
  | App(x, ys) when M.mem x env -> (* 関数適用の場合 (caml2html: inline_app) *)
      let (zs, e) = M.find x env in
      (*Format.eprintf "inlining %s@." x;*)
      let env' =
	List.fold_left2
	  (fun env' (z, t) y -> M.add z y env')
	  M.empty
	  zs
	  ys in
      Alpha.g env' e
  | LetTuple(xts, y, e) -> LetTuple(xts, y, g env e)
  |ForLE(cs,e) ->ForLE(cs,g env e)
  |LetPara({pargs=xts;
            index =cs
            ;accum=acc
            ;pbody=e1},e2) ->
    LetPara({pargs=xts;
             index =cs
            ;accum=acc
            ;pbody=g env e1},g env e2) 
                   
  | e -> e

let f e =(* Printf.printf "\n";*) g M.empty e
