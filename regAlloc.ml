open Asm


(*

メモ

regenvとは別にref変数のレジスタ割り当てを表すref_envを引数として持つ


*ref変数のレジスタ割り当てについて

z=Ref_Get(x)   ->

 if  { zが生きている間にxがRef_PUTされない }
 Non  (z->(x格納されているレジスタ））
 else
 MOVE(rz,x) (z ->rz)


let z= …       ->

 if {zが将来Put(x,a)される
　　&&　xが次にputされるまでにgetされない
　　&&　zが生きている間にxがputされない　　　}
  let (x格納レジスタ）... (z ->(x格納されているレジスタ）)
 else
  そのまま割り当て


let_ref z=var(x)    ->

 if(xが生きている間にzがputされない
　　&&xに対応しているレジスタに、割り当てられている別のref変数がない}
  Non(z ->(xに対応するレジスタ)
 else
  Move((z格納レジスタ）,(xに対応するレジスタ））


Put(x,y);  ->

 if((yレジスタ）==(x格納レジスタ））
  Non
 else      
   Move(　(xが格納されているレジスタ）,(yレジスタ）)



*save擬似命令について
　今までは、2回目以降のsaveはemit.mlで自動的に無視されている
　しかしref変数は値が変化する
　2回目以降のsaveでも、レジスタがrefreshされたref変数に当たればstoreし直すようにした　(emit.mlの処理）


*for文のレジスタ割り当て

　for文に出現しないが生きている変数は、for文直前に退避する(for分が小さかったら退避しない方が良い？？）
  その状態で中身をレジスタ割り当て
  結果、退避されたり、レジスタ割り当ての位置が変わってしまったりした変数をfor文末尾で元の状態に戻す
  (for文の最初にまず退避される変数だったら、無駄なsave,restoreになってしまうけど）



*レジスタ割り当て全般

　ある変数が退避された時、save_refに(変数名、元レジスタ）の組を保存しておく。restoreされた時可能なら元レジスタを割り当てる
  新しく変数にレジスタ割り当てする時は、退避中の変数の元レジスタに当たるものをできるだけ避ける
　(for文の最初と最後でレジスタ割り当てが変化することが少なくなる）



*)

let save_ref:(Id.t*Id.t) list ref = ref [](*saveされたrefと昔のレジスタ*)

let save x r =
  if List.mem_assoc x !save_ref then ()
  else
    save_ref:=(x,r)::!save_ref

let rec shuffle (sw,fsw) xys =
  (* remove identical moves *)
  let _, xys = List.partition (fun (x, y) -> x = y) xys in
  (* find acyclic moves *)
  match List.partition (fun (_, y) -> List.mem_assoc y xys) xys with
  | [], [] -> []
  | (x, y) :: xys, [] -> (* no acyclic moves; resolve a cyclic move *)
     let swap= if List.mem x allregs then sw else fsw in
     (y, swap) :: (x, y) :: shuffle (sw,fsw) (List.map
					        (function
					         | (y', z) when y = y' -> (swap, z)
					         | yz -> yz)
					        xys)
  | xys, acyc -> acyc @ shuffle (sw,fsw) xys

(* for register coalescing *)
(* [XXX] Callがあったら、そこから先は無意味というか逆効果なので追わない。
         そのために「Callがあったかどうか」を返り値の第1要素に含める。 *)
let rec target' src (dest, t) = function
  (*srcが将来どのレジスタとして使われそうか調べる*)
  | Mov(x) when x = src && is_reg dest ->
     assert (t <> Type.Unit);
     assert (t <> Type.Float);
     false, [dest](*srcは将来destに格納される*)
  | FMov(x) when x = src && is_reg dest ->
      assert (t = Type.Float);
      false, [dest]
  | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2) 
  | IfFZ( _, e1, e2) | IfFLE(_, _, e1, e2) ->
      let c1, rs1 = target src (dest, t) e1 in
      let c2, rs2 = target src (dest, t) e2 in
      c1 && c2, rs1 @ rs2
  | CallCls(x, ys, zs) ->
      true, (target_args src regs 0 ys @
	     target_args src fregs 0 zs @
               if x = src then [reg_cl] else [])(*srcが引数として使われる場合*)
  | CallDir(_, ys, zs) ->
      true, (target_args src regs 0 ys @
	     target_args src fregs 0 zs)
  | _ -> false, []
and target src dest = function (* register targeting (caml2html: regalloc_target) *)
  | Ans(exp) -> target' src dest exp
  | Let(xt, exp, e) ->
     let c1, rs1 = target' src xt exp in(*destをxtにセット計算*)
      if c1 then true, rs1 else
      let c2, rs2 = target src dest e in
      c2, rs1 @ rs2
and target_args src all n = function (* auxiliary function for Call *)
  | [] -> []
  | y :: ys when src = y -> all.(n) :: target_args src all (n + 1) ys
  | _ :: ys -> target_args src all (n + 1) ys

let rec will_put_to x =function(*xが将来確実に最初にputされるref変数を返す*)
  |Let(_,Ref_Put(a,x'),_)|Let(_,Ref_FPut(a,x'),_) when x'=x ->Some a
  |Let(_,IfEq(_,_,e1,e2),e3)|Let(_,IfLE(_,_,e1,e2),e3)
   |Let(_,IfFZ(_,e1,e2),e3)|Let(_,IfFLE(_,_,e1,e2),e3) ->
    (match (will_put_to x e1,will_put_to x e2) with
     |(Some a',Some b') when a'=b' ->Some a'
     |_ ->will_put_to x e3)
  |Let(_,ForLE(cs,e1),e2) ->(*ループは実行されないこともあるので,*)
    will_put_to x e2
  |Let(_,exp,e2) ->will_put_to x e2
  |Ans(Ref_Put(a,x'))|Ans(Ref_FPut(a,x')) when x'=x ->Some a
  |Ans(IfEq(_,_,e1,e2))|Ans(IfLE(_,_,e1,e2))
   |Ans(IfFZ(_,e1,e2))|Ans(IfFLE(_,_,e1,e2))->
    (match (will_put_to x e1,will_put_to x e2) with
     |(Some a',Some b') when a'=b' ->Some a'
     |_ ->None)
  |Ans(ForLE(_,e1)) ->
    None
  |Ans(exp) ->None


let rec search_put'_exp x a cont_fv = function
  |IfEq(_,_,e1,e2)|IfLE(_,_,e1,e2)
   |IfFZ(_,e1,e2)|IfFLE(_,_,e1,e2) ->
    (search_put' x a cont_fv e1)||(search_put' x a cont_fv e2)
  |ForLE((_,_,step),e) as for_exp->
    (search_put' x a (cont_fv@(fv_exp for_exp)) e)
    ||(search_put' x a (cont_fv@(fv_exp for_exp)) step)
  |Ref_Put(a',_)|Ref_FPut(a',_)
       when a'=a ->List.mem x cont_fv(*xが生きているか*)
  |exp ->false

and search_put' x a cont_fv = function
  |Let(xt,exp,e) ->
    let cont_fv' = (fv e)@cont_fv in
    if(search_put'_exp x a cont_fv' exp) then
      true
    else
      search_put' x a cont_fv e
  |Ans(exp) ->
    search_put'_exp x a cont_fv exp
let search_put x a e =
  search_put' x a [] e

let rec search_get' a = function(*aがputされる前にgetされるか,健全性のみ*)
  |Let(xt,exp,e)->
    let t,there_is_put = search_get'_exp a exp in
    if(t) then true,there_is_put
    else if(there_is_put) then false,there_is_put
    else
      search_get' a e
  |Ans(exp) ->search_get'_exp a exp
and search_get'_exp a = function
  |IfEq(_,_,e1,e2)|IfLE(_,_,e1,e2)
   |IfFZ(_,e1,e2)|IfFLE(_,_,e1,e2) ->
    let t1,there_is_put1=search_get' a e1 in
    let t2,there_is_put2=search_get' a e2 in
    (t1||t2,there_is_put1||there_is_put2)
  |ForLE((_,_,step),e) as for_exp->(*ループは手抜き,aが出現すればそのままyes*)
    if(List.mem a (fv_exp for_exp)) then(true,true)
    else
      (false,false)
  |Ref_Put(a',_)|Ref_FPut(a',_) when a'=a ->
    (false,true)
  |Ref_Get(a')|Ref_FGet(a') when a'=a ->
    (true,false)
  |_ ->(false,false)
let search_get a e = fst (search_get' a e)
      
type alloc_result = (* allocにおいてspillingがあったかどうかを表すデータ型 *)
  | Alloc of Id.t (* allocated register *)
  | Spill of Id.t (* spilled variable *)
let rec alloc dest cont regenv ref_env x t =
  (* allocate a register or spill a variable *)
  assert (not (M.mem x regenv));
  let all =
    match t with
    | Type.Unit -> ["%g0"] (* dummy *)
    | Type.Float|Type.Ref (Type.Float) -> allfregs
    | _ -> allregs in
  if all = ["%g0"] then Alloc("%g0") else 
    if is_reg x then Alloc(x) else
      let free = fv cont in
      try
        let (c, prefer) = target x dest cont in
        let prefer = if List.mem_assoc x !save_ref then
                       let a = List.assoc x !save_ref in
                       a::prefer
                     else
                       prefer in
        let live = (* 生きているレジスタ *)
             List.fold_left
               (fun live y ->
	         if is_reg y then S.add y live else(
                   if(M.mem y regenv) then
                     S.add (M.find y regenv) live
                   else if (M.mem y ref_env) then
                     S.add (M.find y ref_env) live
                   else
                     live))
               
               S.empty
               free in
        save_ref:=List.filter
                    (fun (x,_) ->List.mem x (fv cont)) !save_ref;
        let real_save=(*現在実際に退避されている変数*)
          List.filter
            (fun (x,_) ->not (M.mem x regenv)&&not (M.mem x ref_env))
            !save_ref in
        let _,save_ref_rs =List.split real_save in
        let save_ref_rs = List.filter (fun r ->List.mem r all) save_ref_rs in(*型合わせ*)
        assert (List.for_all (fun r ->List.mem r all) save_ref_rs);
        let all' =(*save_ref_rsを後ろへ、並び替える*)
          (List.filter (fun r ->not(List.mem r save_ref_rs)) all)
          @List.rev save_ref_rs in
        let r = (* そうでないレジスタを探す *)
          List.find
            (fun r -> not (S.mem r live))
            (prefer @ all') in
        (* Format.eprintf "allocated %s to %s@." x r; *)
        Alloc(r)
      with Not_found ->
        Format.eprintf "register allocation failed for %s@." x;
        let y = (* 型の合うレジスタ変数を探す *)
          List.find
            (fun y ->
	      not (is_reg y) &&
                try List.mem (M.find y regenv) all(*allはxの型を反映してる*)
                with Not_found ->
                  (try List.mem (M.find y ref_env) all
                   with Not_found ->false))
            (List.rev free) in(*近くで使われる変数をspillしないように、revする*)
        Format.eprintf "spilling %s from %s@." y (M.find y regenv);
        Spill(y)
             

(* auxiliary function for g and g'_and_restore *)
let add x r regenv =
  assert (is_reg r);
  if is_reg x then (assert (x = r); regenv) else
    M.add x r regenv

let remove r regenv =
  assert (is_reg r);
  M.filter 
    (fun x r' ->r<>r')
    regenv
               
(* auxiliary functions for g' *)
exception NoReg of Id.t * Type.t
let find x t regenv =
  if is_reg x then x else
  try M.find x regenv
  with Not_found -> raise (NoReg(x, t))
let find' x' regenv =
  match x' with
  | V(x) -> V(find x Type.Int regenv)
  | c -> c

let find_ref x t ref_env =
  match t with
  |Type.Ref _ ->
    if is_reg x then x else
      (try M.find x ref_env
       with Not_found -> raise (NoReg(x, t)))
  |_ ->assert false

let rec g (dest:Id.t*Type.t) (cont:Asm.t) regenv ref_env = function (* 命令列のレジスタ割り当て (caml2html: regalloc_g) *)
  | Ans(exp) -> g'_and_restore dest cont regenv ref_env exp
                               
  | Let((x, t) as xt,(Ref_Get(a) as exp),e)
    |Let((x,t) as xt,(Ref_FGet(a) as exp),e)->(*ref_getの場合*)
     if (M.mem x regenv) then (Emit_asm.emit_exp stdout exp;
                               Printf.printf "%s:%s\n" x (M.find x ref_env);
                               assert false)
     else if(match t with |Type.Ref _ ->true|_ ->false) then assert false
     else
       (*Format.eprintf "%s\n" x;
       Emit_asm.emit_exp stderr exp;*)
     let cont' = concat e dest cont in
     let (e1',regenv1,ref_env1) = g'_and_restore xt cont' regenv ref_env exp in
     let a_r = M.find a ref_env1 in
     if not( search_put x a e) then(*xが生きている間にaがputされるない*)
       let (e',regenv2,ref_env2) =
         g dest cont (add x a_r regenv1) ref_env1 e in
       (cons e1' e',regenv2,ref_env2)
     else
       (match alloc dest cont' regenv1 ref_env1 x t with
        | Spill(y) ->
	 let r =(try M.find y regenv1
                 with Not_found ->M.find y ref_env1 )in
         let save = if M.mem y regenv then
                      (save y (M.find y regenv);Save(M.find y regenv,y))
                    else if M.mem y ref_env then
                      (save y (M.find y ref_env);Save(M.find y ref_env,y))
                    else(*regenvの時点では退避されている場合*)
                      Nop in
	 let (e2', regenv2,ref_env2) =
           (if (M.mem y regenv1) then
              g dest cont (add x r (M.remove y regenv1)) ref_env1 e
            else if M.mem y ref_env1 then
              g dest cont (add x r regenv1) (M.remove y ref_env1) e
            else
              assert false) in
         let e1'=
           if t=Type.Float ||t=Type.Ref (Type.Float) then
             cons e1'  (Ans(FMov(a_r)))
           else
             cons e1' (Ans(Mov(a_r))) in
	 (seq(save, concat e1' (r, t) e2'), regenv2, ref_env2)
      | Alloc(r) ->
	 let (e2', regenv2,ref_env2) =
           g dest cont (add x r regenv1) ref_env1 e in
         let e1'=
           if t=Type.Float ||t=Type.Ref (Type.Float) then
             cons e1' (Ans(FMov(a_r)))
           else
             cons e1' (Ans(Mov(a_r))) in
	 (concat e1' (r, t) e2', regenv2,ref_env2))
         
  | (Let((x,(Type.Ref t' as t)) as xt,((Mov(a)) as exp) ,e)) as e0
    | (Let((x,(Type.Ref t' as t)) as xt,((FMov(a)) as exp) ,e) as e0)->
     if (M.mem x regenv) then (Emit_asm.emit_exp stdout exp;
                               Printf.printf "%s:%s\n" x (M.find x ref_env);
                               assert false)
     else
       (*Format.eprintf "%s\n" x;
       Emit_asm.emit_exp stderr exp;*)
     let cont' = concat e dest cont in
     
     if (not (search_put a x e))&&
          ( (not (is_reg a)) || (List.mem a (allregs@allfregs)))
          &&(if(M.mem a regenv)
             then not(M.exists (fun x r->((List.mem x (fv cont'))&&
                                             (M.find a regenv)=r)) ref_env)
             else true)
     then
       (assert (not (is_reg a));
       (try
          let a_r=find a t' regenv in
          g dest cont regenv (add x a_r ref_env) e
        with
        |NoReg _ ->g dest cont regenv ref_env (Let((a,t'),Restore(a),e0))))
     else
            
       let (e1',regenv1,ref_env1) = g'_and_restore xt cont' regenv ref_env exp in

       (match alloc dest cont' regenv1 ref_env1 x t with
        | Spill(y) ->
	 let r =(try M.find y regenv1
                 with Not_found ->M.find y ref_env1 )in
         let save = if M.mem y regenv then
                      (save y (M.find y regenv);Save(M.find y regenv,y))
                    else if M.mem y ref_env then
                      (save y (M.find y ref_env);Save(M.find y ref_env,y))
                    else(*regenvの時点では退避されている場合*)
                      Nop in
	 let (e2', regenv2,ref_env2) =
           (if (M.mem y regenv1) then
              g dest cont (M.remove y regenv1) (add x r ref_env1) e
            else if M.mem y ref_env1 then
              g dest cont regenv1 (add x r (M.remove y ref_env1)) e
            else
              assert false) in
         (seq(save, concat e1' (r, t) e2'), regenv2, ref_env2)
      | Alloc(r) ->
	 let (e2', regenv2,ref_env2) =
             g dest cont regenv1 (add x r ref_env1) e in
	 (concat e1' (r, t) e2', regenv2,ref_env2))
  
     
  | Let((x, t) as xt, exp, e) ->
     if (M.mem x regenv) then (Emit_asm.emit_exp stdout exp;
                               Printf.printf "%s:%s\n" x (M.find x ref_env);
                               assert false)
     else
       (*Format.eprintf "%s\n" x;
       Emit_asm.emit_exp stderr exp;*)
       
     let cont' = concat e dest cont in(*cont更新*)
     let (e1', regenv1,ref_env1) = g'_and_restore xt cont' regenv ref_env exp in
     (*xtをdestにして計算*)
     let x_is_ref = (match t with |Type.Ref _ ->true|_ ->false) in
     (match will_put_to x e with
      |Some a when ((not (search_put x a e))&&(not (search_get a e))
                    &&(M.mem a ref_env1))
                   &&(M.for_all
                        (fun y r'->r'<>(M.find a ref_env1)||not (List.mem y (fv cont')))
                        regenv1)
                       (*aと同じレジスタを割り当てられた変数が生きていない*)
       ->
        let a_r=M.find a ref_env1 in
        let e,removed = if(List.mem a_r allregs) then(*eから最初のput(a,x)除去*)
                          remove_exp (Ref_Put(a,x)) e
                        else
                          remove_exp (Ref_FPut(a,x)) e in
        if (removed=false) then assert false
        else
          let (e2',regenv2,ref_env2) =
            g dest cont (add x a_r regenv1) ref_env1 e in
          ((concat e1' (a_r,(Type.Ref t))) e2',regenv2,ref_env2)
      |_ ->
        
        (match alloc dest cont' regenv1 ref_env1 x t with
         | Spill(y) ->
	    let r =(try M.find y regenv1
                    with Not_found ->M.find y ref_env1 )in
            let save = if M.mem y regenv then
                         (save y (M.find y regenv);Save(M.find y regenv,y))
                       else if M.mem y ref_env then
                         (save y (M.find y ref_env);Save(M.find y ref_env,y))
                       else(*regenvの時点では退避されている場合*)
                         Nop in
	    let (e2', regenv2,ref_env2) =
              (if (M.mem y regenv1) &&x_is_ref then
                 g dest cont (M.remove y regenv1) (add x r ref_env1) e
               else if (M.mem y regenv1)&& not x_is_ref then
                 g dest cont (add x r (M.remove y regenv1)) ref_env1 e 
            else if M.mem y ref_env1 then
                 (if x_is_ref then
                    g dest cont regenv1 (add x r (M.remove y ref_env1)) e
                  else 
                    g dest cont (add x r regenv1) (M.remove y ref_env1) e)
               else
                 assert false) in
	    (seq(save, concat e1' (r, t) e2'), regenv2, ref_env2)
         | Alloc(r) ->
	    let (e2', regenv2,ref_env2) =
              if x_is_ref then
                g dest cont regenv1 (add x r ref_env1) e
              else
                g dest cont (add x r regenv1) ref_env1 e in(*再帰*)
	    (concat e1' (r, t) e2', regenv2,ref_env2)))
       
and g'_and_restore dest cont regenv ref_env exp = (* 使用される変数をスタックからレジスタへRestore (caml2html: regalloc_unspill) *)
  try g' dest cont regenv ref_env exp
  with NoReg(x, t) ->
    (*Format.eprintf "restoring %s@." x;*)
       (if(not (List.mem_assoc x !save_ref)) then
          (print_string (x^"!");print_string "hello";assert false)
        else
          (match t with
      |Type.Ref _ ->
        g dest cont regenv ref_env (Let((x,t),Restore(x),Ans(exp)))
      |_ ->
        g dest cont regenv ref_env (Let((x, t), Restore(x), Ans(exp)))))
and g' dest cont regenv ref_env = function (* 各命令のレジスタ割り当て 変数をレジスタで置き換えていく*)
  | Nop |Movi _|Lwi _ |FLwi _| Comment _ | Restore _|In|FIn|Next  as exp -> (Ans(exp), regenv,ref_env)
  | Mov(x) ->(Ans(Mov(find x Type.Int regenv))),regenv,ref_env
  | Add(x, y') -> (Ans(Add(find x Type.Int regenv, find' y' regenv)), regenv,ref_env)
  | Sub(x, y) -> (Ans(Sub(find x Type.Int regenv, find y Type.Int regenv)), regenv,ref_env)
  | Mul(x, y) -> (Ans(Mul(find x Type.Int regenv, find y Type.Int regenv)), regenv,ref_env)
  | Div(x, y) -> (Ans(Div(find x Type.Int regenv, find y Type.Int regenv)), regenv,ref_env)
  | SLL(x, i) -> (Ans(SLL(find x Type.Int regenv,i)), regenv,ref_env)
  | SRL(x, i) -> (Ans(SRL(find x Type.Int regenv,i)), regenv,ref_env)
  | SRA(x, i) -> (Ans(SRA(find x Type.Int regenv,i)), regenv,ref_env)
  | FMov(x) -> (Ans(FMov(find x Type.Float regenv)), regenv,ref_env)
  | FNeg(x) -> (Ans(FNeg(find x Type.Float regenv)), regenv,ref_env)
  | FAdd(x, y) -> (Ans(FAdd(find x Type.Float regenv, find y Type.Float regenv)), regenv,ref_env)
  | FSub(x, y) -> (Ans(FSub(find x Type.Float regenv, find y Type.Float regenv)), regenv,ref_env)
  | FMul(x, y) -> (Ans(FMul(find x Type.Float regenv, find y Type.Float regenv)), regenv,ref_env)
  | FDiv(x, y) -> (Ans(FDiv(find x Type.Float regenv, find y Type.Float regenv)), regenv,ref_env)
  | Ftoi(x) ->(Ans(Ftoi(find x Type.Float regenv)), regenv,ref_env)
  | Itof(x) ->(Ans(Itof(find x Type.Int regenv)), regenv,ref_env)
  | FAbs(x) ->(Ans(FAbs(find x Type.Float regenv)), regenv,ref_env)
  | FSqrt(x) ->(Ans(FSqrt(find x Type.Float regenv)), regenv,ref_env)
  | Out(x) ->(Ans(Out(find x Type.Int regenv)), regenv,ref_env)

  | Lw(i, x) -> (Ans(Lw(i,find x Type.Int regenv)), regenv,ref_env)
  | Sw(x, i, y) -> (Ans(Sw(find x Type.Int regenv,i, find y Type.Int regenv)), regenv,ref_env)
  | Swi(x,i,l) ->(Ans(Swi(find x Type.Int regenv,i,l))),regenv,ref_env
  | FLw(i, x) -> (Ans(FLw(i,find x Type.Int regenv)), regenv,ref_env)
  | FSw(x,i,y) -> (Ans(FSw(find x Type.Float regenv,i, find y Type.Int regenv)), regenv,ref_env)
  | FSwi(x,i,l) ->(Ans(FSwi(find x Type.Float regenv,i,l))),regenv,ref_env
  | Ref_Get(x) ->ignore (find_ref x (Type.Ref (Type.Int)) ref_env);(Ans(Nop),regenv,ref_env)(*(Ans(Add(find_ref x (Type.Ref (Type.Int)) ref_env,C(0))),regenv,ref_env)*)
  | Ref_FGet(x)->ignore (find_ref x (Type.Ref (Type.Float)) ref_env);(Ans(Nop),regenv,ref_env)(*(Ans(FMov(find_ref x (Type.Ref (Type.Float)) ref_env )),regenv,ref_env)*)
  | Ref_Put(x,y) ->let x_r = find_ref x (Type.Ref (Type.Int)) ref_env in
                   let y_r = find y Type.Int regenv in
                   if x_r=y_r then assert false
                   else
                     (Let((x_r,Type.Ref (Type.Int)),Mov(y_r),Ans(Nop)),regenv,ref_env)
  | Ref_FPut(x,y) ->let x_r = find_ref x (Type.Ref (Type.Float)) ref_env in
                    let y_r = find y Type.Float regenv in
                    if x_r=y_r then assert false
                    else
                      (Let((x_r,Type.Ref (Type.Float)),FMov(y_r),Ans(Nop)),regenv,ref_env)
  | IfEq(x, y', e1, e2) as exp -> g'_if dest cont regenv ref_env exp (fun e1' e2' -> IfEq(find x Type.Int regenv, find' y' regenv, e1', e2')) e1 e2
  | IfLE(x, y', e1, e2) as exp -> g'_if dest cont regenv ref_env exp (fun e1' e2' -> IfLE(find x Type.Int regenv, find' y' regenv, e1', e2')) e1 e2
  | IfFZ(x, e1, e2) as exp -> g'_if dest cont regenv ref_env exp (fun e1' e2' -> IfFZ(find x Type.Float regenv, e1', e2')) e1 e2
  | IfFLE(x, y, e1, e2) as exp -> g'_if dest cont regenv ref_env exp (fun e1' e2' -> IfFLE(find x Type.Float regenv, find y Type.Float regenv, e1', e2')) e1 e2
  | CallCls(x, ys, zs) as exp -> g'_call dest cont regenv ref_env exp (fun ys zs -> CallCls(find x Type.Int regenv, ys, zs)) ys zs
  | CallDir(l, ys, zs) as exp -> g'_call dest cont regenv ref_env exp (fun ys zs -> CallDir(l, ys, zs)) ys zs
  | ForLE(((i,a'),(j',k'),step),e) as exp ->g'_for dest cont regenv ref_env exp (fun step e -> ForLE(((find_ref i (Type.Ref (Type.Int)) ref_env , a'),
                                                                                               ((if j'=V(i) then V(find_ref i (Type.Ref(Type.Int)) ref_env)
                                                                                                 else find' j' regenv),
                                                                                                (if k'=V(i) then V(find_ref i (Type.Ref(Type.Int)) ref_env)
                                                                                                 else find' k' regenv)),
                                                                                                   step),e)) step e 
  | Save(x, y) -> assert false
  |Run_parallel(a,d,xs,ys) as exp-> g'_call dest cont regenv ref_env exp (fun xs ys -> Run_parallel(find a (Type.Int) regenv,find d Type.Float regenv,xs, ys)) xs ys
  |Acc(acc,x) ->(Ans(Acc(acc,find x (Type.Float) regenv))),regenv,ref_env

and g'_for dest cont regenv ref_env exp constr step e  =
 
  
  let free_for = fv (Ans(exp)) in
  let free_afterloop=(List.filter (fun x->not (List.mem x free_for)) (fv cont)) in
  let e_save,regenv',ref_env' =
    (*for分内で出現しないが、for文後で出現する変数達を退避する*)
    List.fold_left
      (fun (e_save,regenv',ref_env') x ->
        if (not (M.mem x regenv)) && not(M.mem x ref_env)
        then
          (e_save,regenv',ref_env')
        else(*exist in (regenv,ref_env)*)
          (try (let r= M.find x regenv  in
                save x r;
               (seq(Save(r,x),e_save),M.remove x regenv',ref_env'))
          with
            Not_found ->(let r=M.find x ref_env in
                         save x r;
                         (seq(Save(r,x),e_save),regenv',M.remove x ref_env'))))
      (Ans(Nop),regenv,ref_env)
  free_afterloop in
  (*後続命令にcontにループ自身を加えループの中をレジスタ割り当て*)
  let cont' = concat (Ans(exp)) (Id.genid "unit",Type.Unit) cont in
  let save_ref_backup = !save_ref in
  let (e',regenv1,ref_env1) =
    g dest cont' regenv' ref_env' e in
  let (step',regenv2,ref_env2) =
    g dest cont' regenv1 ref_env1 step in
  (*ループの最初と最後でループ内自由変数のレジスタ割り当てを同じにする*)
  
  let (adj_save,adj_mv_list,adj_restore),(regenv3,ref_env3) =
    adjust (regenv',ref_env') (regenv2,ref_env2) free_for in
  let adj_mv =
    List.fold_left
      (fun adj_mv' (r',r) ->
        if(List.mem r allregs) then
          Let((r,Type.Int),Mov(r'),adj_mv')
        else
          Let((r,Type.Float),(FMov(r')),adj_mv'))
      (Ans(Nop))
      (List.rev (shuffle (reg_sw,reg_fsw) adj_mv_list)) in
  (if adj_save <>(Ans(Nop)) then Format.eprintf "there are adj_save\n";
   if adj_mv_list<>[] then Format.eprintf "there are adj_move\n";
   if adj_restore <>(Ans(Nop)) then Format.eprintf "there are adj_restore\n");
  let step' =
    cons step' (cons adj_save (cons adj_mv adj_restore)) in
    
  assert (List.for_all (fun x ->if(M.mem x regenv')then
                                  let r'=M.find x regenv' in
                                  let r=M.find x regenv3 in
                                  r=r'
                                else if(M.mem x ref_env') then
                                  let r'=M.find x ref_env' in
                                  let r=M.find x ref_env3 in
                                  r=r'
                                else
                                  true)
                       free_for);(*整合性チェック*)
                                  
  let  save_ref_backup2= !save_ref in
  save_ref:=save_ref_backup;
  let for_exp = constr step' e'  in
   save_ref:=save_ref_backup2;
   cons e_save (Ans(for_exp)),regenv',ref_env'
  
and adjust (regenv1,ref_env1) (regenv2,ref_env2) f_v =
  (*ループの最初と末尾でレジスタの整合性を保つ*)
  List.fold_left
    (fun ((save',adjust_mv,restore),(regenv,ref_env)) x ->

      if M.mem x regenv1||M.mem x ref_env1 then
        let r =
          (try M.find x regenv1 with Not_found ->M.find x ref_env1) in
        if M.mem x regenv2||M.mem x ref_env2 then
          let r' =
            (try M.find x regenv2 with Not_found ->M.find x ref_env2) in
          if(r<>r') then
            if M.mem x regenv1 then
              (save',(r',r)::adjust_mv,restore),(add x r regenv,ref_env)
            else
              (save',(r',r)::adjust_mv,restore),(regenv,add x r ref_env)
          else (save',adjust_mv,restore),(regenv,ref_env)

        else(*xがregenv2,ref_env2で割り当てられていない*)
          if(List.mem r allregs)&&(M.mem x regenv1) then
            (save',adjust_mv,Let((r,Type.Int),Restore(x),restore)),
            (add x r (remove r regenv),remove r ref_env)
          else if(List.mem r allregs)&&(M.mem x ref_env1) then
            (save',adjust_mv,Let((r,Type.Ref (Type.Int)),Restore(x),restore)),
              (remove r regenv,add x r (remove r ref_env))
          else if(List.mem r allfregs)&&(M.mem x regenv1) then
            (save',adjust_mv,Let((r,Type.Float),Restore(x),restore)),
            (add x r (remove r regenv),remove r ref_env)
          else
            (save',adjust_mv,Let((r,Type.Ref(Type.Float)),Restore(x),restore)),
            (remove r regenv,add x r (remove r ref_env))
            
      else(*xがregenv1,ref_env1で割り当てられていない*)
        if M.mem x regenv2||M.mem x ref_env2 then
          let r' =
            (try M.find x regenv2 with Not_found ->M.find x ref_env2) in
          let tmp = Id.genid "unit" in
          (Let((tmp,Type.Unit),Save(r',x),save'),adjust_mv,restore),
          (M.remove x regenv,M.remove x ref_env)

        else
          (save',adjust_mv,restore),(regenv,ref_env))

    (((Ans(Nop)),[],(Ans(Nop))),(regenv2,ref_env2))
    f_v
and g'_if dest cont regenv ref_env  exp constr e1 e2 = (* ifのレジスタ割り当て (caml2html: regalloc_if) *)
  let save_ref_backup = !save_ref in
  let (e1', regenv1,ref_env1) = g dest cont regenv ref_env  e1 in
  save_ref:=save_ref_backup;
  let (e2', regenv2,ref_env2) = g dest cont regenv ref_env  e2 in
    let regenv' = (* 両方に共通のレジスタ変数だけ利用 *)
    List.fold_left
      (fun regenv' x ->
        try
	  if is_reg x then regenv' else
          let r1 = M.find x regenv1 in
          let r2 = M.find x regenv2 in
          if r1 <> r2 then regenv' else
	    add x r1 regenv'
        with Not_found -> regenv')
      M.empty
      (fv cont) in
  let ref_env' =
    List.fold_left
      (fun ref_env' x ->
        try
	  if is_reg x then ref_env' else
          let r1 = M.find x ref_env1 in
          let r2 = M.find x ref_env2 in
          if r1 <> r2 then ref_env' else
	    add x r1 ref_env'
        with Not_found -> ref_env')
      M.empty
      (fv cont) in
  let save_r_x =
    List.fold_left
      (fun r_x x ->
        if x = fst dest || (not (M.mem x regenv)) && not(M.mem x ref_env) || M.mem x regenv' || M.mem x ref_env'
        then r_x else(
          let r=(try M.find x regenv with Not_found->M.find x ref_env) in
          (r,x)::r_x))
      []
      (fv cont) in
  let (e1',e2') =
    List.fold_left
      (fun (e1',e2') (r,x)->
        if M.mem x regenv then
          (e1',e2')
        else
          let e1'= if M.mem x ref_env1 then
                     before_ans (Save(M.find x ref_env1,x)) e1'
                   else e1' in
          let e2'= if M.mem x ref_env2 then
                     before_ans (Save(M.find x ref_env2,x)) e2'
                   else e2' in
          (e1',e2'))
      (e1',e2')
      save_r_x in
  save_ref:=save_ref_backup;
  let if_exp = constr e1' e2' in(*ここでexception:NoRegが出る可能性がある*)
  (List.fold_left
    (fun e (r,x)->save x r;seq(Save(r,x),e))
     (Ans(if_exp))
     save_r_x,
   regenv',ref_env')
and g'_call dest cont regenv ref_env exp constr ys zs = (* 呼び出し前の退避 *)
  let call_exp = constr
	           (List.map (fun y -> find y Type.Int regenv) ys)
	           (List.map (fun z -> find z Type.Float regenv) zs) in
  (List.fold_left
     (fun e x ->
       if x = fst dest || (not (M.mem x regenv))&&not (M.mem x ref_env) then e else
         (if M.mem x regenv then
            (save x (M.find x regenv);
            seq(Save(M.find x regenv, x), e))
          else
            (save x (M.find x ref_env);
            seq(Save(M.find x ref_env,x), e))))
     (Ans(call_exp))(*この時点でys,zsのレジスタ割り当ては終わっているので、置き換える*)
     (fv cont),
   M.empty,M.empty)

let h { name = Id.L(x); args = ys; fargs = zs; body = e; ret = t } = (* 関数のレジスタ割り当て (caml2html: regalloc_h) *)
  let regenv = M.add x reg_cl M.empty in
  save_ref:=[];
  let (i, arg_regs, regenv) =
    List.fold_left
      (fun (i, arg_regs, regenv) y ->
        let r = regs.(i) in
        (i + 1,
	 arg_regs @ [r],
	 (assert (not (is_reg y));
	  M.add y r regenv)))
      (0, [], regenv)
      ys in
  let (d, farg_regs, regenv) =
    List.fold_left
      (fun (d, farg_regs, regenv) z ->
        let fr = fregs.(d) in
        (d + 1,
	 farg_regs @ [fr],
	 (assert (not (is_reg z));
	  M.add z fr regenv)))
      (0, [], regenv)
      zs in
  let a =
    match t with
    | Type.Unit -> Id.gentmp Type.Unit
    | Type.Float |Type.Ref (Type.Float)-> fregs.(0)
    | _ -> regs.(0) in
  let (e', regenv',ref_env') =
    if(t=Type.Float||t=Type.Ref (Type.Float)) then
      g (a, t) (Ans(FMov(a))) regenv M.empty e
    else
      g (a, t) (Ans(Mov(a))) regenv M.empty e in
  { name = Id.L(x); args = arg_regs; fargs = farg_regs; body = e'; ret = t }

let i =function
  |Some {pargs=xs;
         pfargs=ys;
         index=(index,(j',k'));
         pbody=e
        } ->
    save_ref:=[];

    let (i, arg_regs, regenv) =
      List.fold_left
        (fun (i, arg_regs, regenv) y ->
          let r = regs.(i) in
          (i + 1,
	   arg_regs @ [r],
	   (assert (not (is_reg y));
	    M.add y r regenv)))
        (0, [], M.empty)
        xs in
    let (d, farg_regs, regenv) =
      List.fold_left
        (fun (d, farg_regs, regenv) z ->
          let fr = fregs.(d) in
          (d + 1,
	   farg_regs @ [fr],
	   (assert (not (is_reg z));
	    M.add z fr regenv)))
        (0, [], regenv)
        ys in
    let ref_env = M.add index regs.(i) (M.empty) in
    let index_regs=(find_ref index (Type.Ref (Type.Int)) ref_env,
                    ((if j'=V(index) then
                        V(find_ref index (Type.Ref(Type.Int)) ref_env)
                       else find' j' regenv),
                     (if k'=V(index) then
                        V(find_ref index (Type.Ref(Type.Int)) ref_env)
                       else find' k' regenv))
                    ) in
                     
    let (e',regenv2,ref_env2)=
      g (Id.gentmp Type.Unit,Type.Unit) e regenv ref_env e in
    let free_in_body = (xs@ys) in
    let (adj_save,adj_mv_list,adj_restore),(regenv3,ref_env3) =
      adjust (regenv,ref_env) (regenv2,ref_env2) free_in_body in
    let adj_mv =
      List.fold_left
        (fun adj_mv' (r',r) ->
          if(List.mem r allregs) then
            Let((r,Type.Int),Mov(r'),adj_mv')
          else
            Let((r,Type.Float),(FMov(r')),adj_mv'))
        (Ans(Nop))
        (List.rev (shuffle (reg_sw,reg_fsw) adj_mv_list)) in
    (if adj_save <>(Ans(Nop)) then Format.eprintf "there are adj_save(p)\n";
     if adj_mv_list<>[] then Format.eprintf "there are adj_move(p)\n";
     if adj_restore <>(Ans(Nop)) then Format.eprintf "there are adj_restore(p)\n");
  let e'' =
    cons e' (cons adj_save (cons adj_mv adj_restore)) in
    
  assert (List.for_all (fun x ->if(M.mem x regenv)then
                                  let r'=M.find x regenv in
                                  let r=M.find x regenv3 in
                                  r=r'
                                else if(M.mem x ref_env) then
                                  let r'=M.find x ref_env in
                                  let r=M.find x ref_env3 in
                                  r=r'
                                else
                                  true)
                       free_in_body);(*整合性チェック*)
    
    
  Some {pargs=arg_regs;
        pfargs=farg_regs;
        index=index_regs;
        pbody=e''}
        
  |None ->None


let f (Prog(data, fundefs,parallel, e)) = (* プログラム全体のレジスタ割り当て (caml2html: regalloc_f) *)
  Format.eprintf "register allocation: may take some time (up to a few minutes, depending on the size of functions)\n
                  minrtのコンパイルでは,,\n
                  -inline 300で10分、-inline 1000で40分くらいかかりましたが、動的命令数はあまり変わらないです@.";
  let fundefs' = List.map h fundefs in
  let parallel'=i parallel in
  save_ref:=[];
  let e', regenv',ref_env'= g (Id.gentmp Type.Unit, Type.Unit) (Ans(Nop)) M.empty M.empty e in(*全体はユニット型だから、dest*)
  Prog(data, fundefs',parallel', e')
