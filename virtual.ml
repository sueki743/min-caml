(* translation into SPARC assembly with infinite number of virtual registers *)

open Asm

let data = ref [] (* 浮動小数点数の定数テーブル (caml2html: virtual_data) *)

let classify xts ini addf addi =
  List.fold_left
    (fun acc (x, t) ->
      match t with
      | Type.Unit -> acc
      | Type.Float -> addf acc x(*前までの結果(acc)と連想配列の要素を受けて、addf処理をする*)
      | _ -> addi acc x t)
    ini
    xts(*何かと型との連想配列*)

let separate xts =(*xtsをintとfloatのリスト2つに分ける*)
  classify
    xts
    ([], [])
    (fun (int, float) x -> (int, float @ [x]))
    (fun (int, float) x _ -> (int @ [x], float))

let expand xts ini addf addi =
  classify
    xts
    ini
    (fun (offset, acc) x ->
      let offset =  offset in
      (offset + 1, addf x offset acc))
    (fun (offset, acc) x t ->
      (offset + 1, addi x t offset acc))

let read_int_virtual () =
  let x1 = Id.genid "x" in
  let x2 = Id.genid "x" in
  let x3 = Id.genid "x" in
  let y1 = Id.genid "y" in
  let y2 = Id.genid "y" in
  let y3 = Id.genid "y" in
  let y4 = Id.genid "y" in
  let y5 = Id.genid "y" in
  let y6 = Id.genid "y" in
  Let((x1,Type.Int),In,
      (Let((y1,Type.Int),In,
           (Let((y2,Type.Int),SLL(y1,8),
                (Let((x2,Type.Int),Or(x1,y2),
                     (Let((y3,Type.Int),In,
                          (Let((y4,Type.Int),SLL(y3,16),
                               (Let((x3,Type.Int),Or(x2,y4),
                                    (Let((y5,Type.Int),In,
                                         (Let((y6,Type.Int),SLL(y5,24),
                                              (Ans(Or(y6,x3))))))))))))))))))))

let read_float_virtual () =
  let x1 = Id.genid "x" in
  let x2 = Id.genid "x" in
  let x3 = Id.genid "x" in
  let x4 = Id.genid "x" in
  let y1 = Id.genid "y" in
  let y2 = Id.genid "y" in
  let y3 = Id.genid "y" in
  let y4 = Id.genid "y" in
  let y5 = Id.genid "y" in
  let y6 = Id.genid "y" in
  let dummy= Id.genid "unit" in
  Let((x1,Type.Int),In,
      (Let((y1,Type.Int),In,
           (Let((y2,Type.Int),SLL(y1,8),
                (Let((x2,Type.Int),Or(x1,y2),
                     (Let((y3,Type.Int),In,
                          (Let((y4,Type.Int),SLL(y3,16),
                               (Let((x3,Type.Int),Or(x2,y4),
                                    (Let((y5,Type.Int),In,
                                         (Let((y6,Type.Int),SLL(y5,24),
                                              (Let((x4,Type.Int),Or(y6,x3),
                                                   (Let((dummy,Type.Unit),Sw(x4,0,reg_hp),
                                                        (Ans(FLw(0,reg_hp))))))))))))))))))))))))

let print_char_virtual x =Ans(Out(x))
  

                                 
  
let rec g env constenv  = function (* 式の仮想マシンコード生成 (caml2html: virtual_g) *)
  | Closure.Unit -> Ans(Nop)
  | Closure.Int(i) -> Ans(Add(reg_zero,C(i)))
  | Closure.Float(d) ->
      let l =
	try
	  (* すでに定数テーブルにあったら再利用 *)
	  let (l, _) = List.find (fun (_, d') -> d = d') !data in
	  l
	with Not_found ->
	  let l = Id.L(Id.genid "l") in
	  data := (l, d) :: !data;
	  l
      in
      let x = Id.genid "l" in
      Let((x, Type.Int), La(l), Ans(FLw(0, x)))(*１段に出来そう->出来ない*)
  | Closure.Neg(x) -> Ans(Sub(reg_zero, V (x)))
  | Closure.Add(x, y) -> Ans(Add(x, V(y)))
  | Closure.Sub(x, y) -> Ans(Sub(x, V(y)))
  | Closure.Mul(x, y) -> Ans(Mul(x,y))
  | Closure.Div(x, y) -> Ans(Div(x,y))
  | Closure.FNeg(x) -> Ans(FNeg(x))
  | Closure.FAdd(x, y) -> Ans(FAdd(x, y))
  | Closure.FSub(x, y) -> Ans(FSub(x, y))
  | Closure.FMul(x, y) -> Ans(FMul(x, y))
  | Closure.FDiv(x, y) -> Ans(FDiv(x, y))
  | Closure.Ftoi(x) -> Ans(Ftoi (x))
  | Closure.Itof(x) -> Ans(Itof (x))
  | Closure.FAbs(x) ->Ans(FAbs(x))
  | Closure.FSqrt(x) ->Ans(FSqrt(x))
  | Closure.Read_int(x) ->read_int_virtual ()(*xはunitなので無視*)
  | Closure.Read_float(x) ->read_float_virtual () (*xはunitなので無視*)
  | Closure.Print_char(x) ->print_char_virtual x
  | Closure.IfEq(x, y, e1, e2) ->
      (match M.find x env with
      | Type.Bool | Type.Int -> Ans(IfEq(x, V(y), g env constenv e1, g env constenv e2))
      | Type.Float -> Ans(IfFEq(x, y, g env constenv e1, g env constenv e2))
      | _ -> failwith "equality supported only for bool, int, and float")
  | Closure.IfLE(x, y, e1, e2) ->
      (match M.find x env with
      | Type.Bool | Type.Int -> Ans(IfLE(x, V(y), g env constenv e1, g env constenv e2))
      | Type.Float -> Ans(IfFLE(x, y, g env constenv e1, g env constenv e2))
      | _ -> failwith "inequality supported only for bool, int, and float")
  | Closure.Let((x, t1), e1, e2) ->(*変数を登録していきながら、再起*)
     (match (Closure.eval) constenv e1 with
      |Some const ->let e1'=g M.empty M.empty const in
                    let e2'=g (M.add x t1 env) (M.add x (const,t1)
                                                      constenv) e2 in
                    concat e1' (x,t1) e2'
                    (*if(List.mem x (fv e2')) then
                      concat e1' (x,t1) e2'
                    else
                      e2'*)
      |None ->
        let e1' = g env constenv e1 in
        let e2' = g (M.add x t1 env) constenv e2 in(*xの型を登録すればコード作れる*)
        concat e1' (x, t1) e2')
  | Closure.Let_Ref((x,t),e1,e2) ->
     (match t with Type.Ref _ ->
                   let e1' = g env constenv e1 in
                   let e2' = g (M.add x t env) constenv e2 in
                   concat e1' (x,t) e2'
                 |_ ->assert false)
  | Closure.Var(x) ->
     (match M.find x env with
      | Type.Unit -> Ans(Nop)
      | Type.Float -> Ans(FMov(x))
      | _ -> Ans(Add(x,C(0))))
  | Closure.MakeCls((x, t), { Closure.entry = l; Closure.actual_fv = ys }, e2) -> (* クロージャの生成 (caml2html: virtual_makecls) *)
      (* Closureのアドレスをセットしてから、自由変数の値をストア *)
      let e2' = g (M.add x t env) constenv e2 in
      let offset, store_fv =
	expand
	  (List.map (fun y -> (y, M.find y env)) ys)(*この時点でysは環境に入ってる*)
	  (1, e2')
	  (fun y offset store_fv -> seq(FSw(y, offset, x), store_fv))
	  (fun y _ offset store_fv -> seq(Sw(y, offset, x), store_fv)) in
      Let((x, t), Add(reg_hp,C(0)),
	  Let((reg_hp, Type.Int), Add(reg_hp, C(offset)),
	      let z = Id.genid "l" in(*zにラベルのアドレスを入れる*)
	      Let((z, Type.Int), La(l),
		  seq(Sw(z, 0, x),(*ラベルの値をx参照先に保存*)
		      store_fv))))
  | Closure.AppCls(x, ys) ->
      let (int, float) = separate (List.map (fun y -> (y, M.find y env)) ys) in
      Ans(CallCls(x, int, float))
  | Closure.AppDir(Id.L(x), ys) ->
      let (int, float) = separate (List.map (fun y -> (y, M.find y env)) ys) in
      Ans(CallDir(Id.L(x), int, float))
  | Closure.Tuple(xs) -> (* 組の生成 (caml2html: virtual_tuple) *)
      let y = Id.genid "t" in
      let (offset, store) =
	expand
	  (List.map (fun x -> (x, M.find x env)) xs)(*型を連想づける*)
	  (0, Ans(Add(y,C(0))))
	  (fun x offset store -> seq(FSw(x, offset,y), store))(*次のstore値*)
	  (fun x _ offset store -> seq(Sw(x,offset, y), store)) in
      Let((y, Type.Tuple(List.map (fun x -> M.find x env) xs)), Add(reg_hp,C(0)),
	  Let((reg_hp, Type.Int), Add(reg_hp, C( offset)),
	      store))
  (*ヒープレジスタをoffset分伸ばして、yに組の先頭に入れてstoreする*)
  | Closure.ConstTuple(l) ->Ans(La(l))
  | Closure.LetTuple(xts, y, e2) ->
      let s = Closure.fv e2 in
      let (offset, load) =
	expand
	  xts
	  (0, g (M.add_list xts env) constenv e2)(*変数の型さえ分かれば、コードが作れる*)
	  (fun x offset load ->
	    if not (S.mem x s) then load else (* [XX] a little ad hoc optimization *)
	      fletd(x, FLw(offset, y), load))(*fletdは無害*)
	  (fun x t offset load ->
	    if not (S.mem x s) then load else (* [XX] a little ad hoc optimization *)
	    Let((x, t), Lw(offset,y), load)) in
      load
  | Closure.Get(x, y) when M.mem y constenv ->
     let i=(match M.find y constenv with ((Closure.Int(i)),_) ->i
                                       |_ ->assert false )
     in
     (match M.find x env with
      | Type.Array(Type.Unit) -> Ans(Nop)
      | Type.Array(Type.Float) ->
         Ans(FLw(i,x))(*メモリはワードアクセス*)
      | Type.Array(_) ->
	 Ans(Lw(i,x))
      | _ -> assert false)
  | Closure.Get(x, y) -> (* 配列の読み出し (caml2html: virtual_get) *)
      let address=Id.genid x in
      (match M.find x env with
       | Type.Array(Type.Unit) -> Ans(Nop)
       | Type.Array(Type.Float) ->
         Let((address,Type.Int),Add(x,V(y)),
	     Ans(FLw(0,address)))(*メモリはワードアクセス*)
      | Type.Array(_) ->
         Let((address,Type.Int),Add(x,V(y)),
	         Ans(Lw(0,address)))
      | _ -> assert false)
   | Closure.Put(x, y, z) when M.mem y constenv ->
      let i=(match M.find y constenv with ((Closure.Int(i)),_) ->i
                                        |_ ->assert false )
      in
      (match M.find x env with
      | Type.Array(Type.Unit) -> Ans(Nop)
      | Type.Array(Type.Float) ->
	      Ans(FSw(z, i,x))
      | Type.Array(_) ->
	 Ans(Sw(z, i,x))
      | _ -> assert false)
   | Closure.Put(x, y, z) ->
     let address=Id.genid x in
      (match M.find x env with
      | Type.Array(Type.Unit) -> Ans(Nop)
      | Type.Array(Type.Float) ->
             Let((address,Type.Int),Add(x,V(y)),
	      Ans(FSw(z, 0,address)))
      | Type.Array(_) ->
         Let((address,Type.Int),Add(x,V(y)),
	         Ans(Sw(z, 0,address)))
      | _ -> assert false)
  | Closure.ConstArray(l) -> Ans(La(l))
  | Closure.ExtArray(Id.L(x)) -> Ans(La(Id.L("min_caml_" ^ x)))
  | Closure.ForLE(((i,a),(j,k),step),e) ->
     let tmp = Id.genid "unit" in
     Ans(ForLE(((i,V(a)),(V(j),V(k)),
                concat (g env constenv step) (tmp,Type.Int) (Ans(Ref_Put(i,tmp))))
               ,g env constenv e))
  | Closure.Ref_Get(x) ->
     (match M.find x env with
      |Type.Ref(Type.Float) ->Ans(Ref_FGet(x))
      |Type.Ref(Type.Ref _) ->assert false
      |Type.Ref(_) ->Ans(Ref_Get(x))
      |_ ->assert false)
  | Closure.Ref_Put(x,y) ->
     (match M.find y env with
      |Type.Float ->Ans(Ref_FPut(x,y))
      |Type.Ref _ ->assert false
      |_ ->Ans(Ref_Put(x,y)))

(* 関数の仮想マシンコード生成 (caml2html: virtual_h) *)
let h { Closure.name = (Id.L(x), t); Closure.args = yts; Closure.formal_fv = zts; Closure.body = e } =
  let (int, float) = separate yts in
  let (offset, load) =
    expand
      zts
      (1, g (M.add x t (M.add_list yts (M.add_list zts M.empty))) M.empty e)
      (fun z offset load -> fletd(z, FLw(offset,x), load))
      (fun z t offset load -> Let((z, t), Lw(offset,x), load)) in
  (match t with
  | Type.Fun(_, t2) ->
      { name = Id.L(x); args = int; fargs = float; body = load; ret = t2 }
  | _ -> assert false)

(* プログラム全体の仮想マシンコード生成 (caml2html: virtual_f) *)
let f (Closure.Prog(fundefs, e)) =
  data := [];
  let fundefs = List.map h fundefs in
  let e = g M.empty M.empty e in
  Prog(!data, fundefs, e)
