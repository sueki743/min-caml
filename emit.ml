open Asm

external gethi : float -> int32 = "gethi"
external getlo : float -> int32 = "getlo"

let stackset = ref M.empty (* すでにSaveされた変数の集合 ここに型も入れとく *)
let stackmap = ref [] (* Saveされた変数の、スタックにおける位置 (caml2html: emit_stackmap) *)
let save x reg=
  stackset := M.add x reg !stackset;
  if not (List.mem x !stackmap) then
    stackmap := !stackmap @ [x]

(*変更点・・・stackmapは変数のリストのまま、stacksetをmapにした*)
                              
(*let savef x =
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    (let pad =
      if List.length !stackmap mod 2 = 0 then [] else [Id.gentmp Type.Int] in
    stackmap := !stackmap @ pad @ [x; x]*)
let locate x =(*stackmapにあるxのリストを作る*)
  let rec loc = function
    | [] -> []
    | y :: zs when x = y -> 0 :: List.map succ (loc zs)
    | y :: zs -> List.map succ (loc zs) in
  loc !stackmap
let offset x = 1 * List.hd (locate x)
let stacksize () = (List.length !stackmap + 1) * 1

let pp_id_or_imm = function
  | V(x) -> x
  | C(i) -> string_of_int i

(* 関数呼び出しのために引数を並べ替える(register shuffling) (caml2html: emit_shuffle) *)
let rec shuffle sw xys =
  (* remove identical moves *)
  let _, xys = List.partition (fun (x, y) -> x = y) xys in
  (* find acyclic moves *)
  match List.partition (fun (_, y) -> List.mem_assoc y xys) xys with
  | [], [] -> []
  | (x, y) :: xys, [] -> (* no acyclic moves; resolve a cyclic move *)
      (y, sw) :: (x, y) :: shuffle sw (List.map
					 (function
					   | (y', z) when y = y' -> (sw, z)
					   | yz -> yz)
					 xys)
  | xys, acyc -> acyc @ shuffle sw xys

type dest = Tail | NonTail of Id.t (* 末尾かどうかを表すデータ型 (caml2html: emit_dest) *)
let rec g oc = function (* 命令列のアセンブリ生成 (caml2html: emit_g) *)
  | dest, Ans(exp) -> g' oc (dest, exp)
  | dest, Let((x, t), exp, e) ->
      g' oc (NonTail(x), exp);
      g oc (dest, e)
and g' oc = function (* 各命令のアセンブリ生成 (caml2html: emit_gprime) *)
  (* 末尾でなかったら計算結果をdestにセット (caml2html: emit_nontail) *)
  | NonTail _, Nop ->()
  | NonTail(x), Add(y, z') ->
     (match z' with
     |V(v)->Printf.fprintf oc "\tadd\t%s, %s, %s\n" x y v;
     |C(c)->Printf.fprintf oc "\taddi\t%s, %s, %d\n" x y c;)
  | NonTail(x), Sub(y, z') ->
     (match z' with
      |V(v)->Printf.fprintf oc "\tsub\t%s, %s, %s\n" x y v;
      |C(c)->Printf.fprintf oc "\taddi\t%s, %s, -%d\n" x y c;)
  | NonTail(x), Mul(y,z) -> Printf.fprintf oc "\tmul\t%s, %s, %s\n" x y z
  | NonTail(x), Div(y,z) -> Printf.fprintf oc "\tdiv\t%s, %s, %s\n" x y z
  | NonTail(x), SLL(y, c) -> Printf.fprintf oc "\tsll\t%s, %s, %d\n" x y c
  | NonTail(x), SRL(y, c) -> Printf.fprintf oc "\tsrl\t%s, %s, %d\n" x y c
  | NonTail(x), SRA(y, c) -> Printf.fprintf oc "\tsra\t%s, %s, %d\n" x y c
  | NonTail(x), Lw(c,y) -> Printf.fprintf oc "\tlw\t%s, %d(%s)\n" x c y
  | NonTail(x), La(Id.L(y)) ->Printf.fprintf oc "\tla\t%s, %s\n" x y
  | NonTail(_), Sw(x,c,y) -> Printf.fprintf oc "\tsw\t%s, %d(%s)\n" x c y
  | NonTail(x), FLw(c,y) -> Printf.fprintf oc "\tlw.s\t%s, %d(%s)\n" x c y
  | NonTail(_), FSw(x,c,y) -> Printf.fprintf oc "\tsw.s\t%s, %d(%s)\n" x c y
  | NonTail(x), FAdd(y, z) -> Printf.fprintf oc "\tadd.s\t%s, %s, %s\n" x y z
  | NonTail(x), FSub(y, z) -> Printf.fprintf oc "\tsub.s\t%s, %s, %s\n" x y z
  | NonTail(x), FMul(y, z) -> Printf.fprintf oc "\tmul.s\t%s, %s, %s\n" x y z
  | NonTail(x), FInv(y) -> Printf.fprintf oc "\tinv.s\t%s, %s\n" x y
  | NonTail(x), FMov(y) -> Printf.fprintf oc "\tmov.s\t%s, %s\n" x y
  | NonTail(x), FNeg(y) -> Printf.fprintf oc "\tneg.s\t%s, %s\n" x y
  | NonTail(_), Comment(s) -> Printf.fprintf oc "\t! %s\n" s
  (* 退避の仮想命令の実装 (caml2html: emit_save) *)
  | NonTail(_), Save(x, y)  when List.mem x allregs && not (M.mem y !stackset) ->
      save y x;
      Printf.fprintf oc "\tsw\t%s, %d(%s)\n" x (offset y) reg_sp
  | NonTail(_), Save(x, y)  when List.mem x allfregs && not (M.mem y !stackset) ->
     save y x;
      Printf.fprintf oc "\tsw.s\t%s, %d(%s)\n" x (offset y) reg_sp
  | NonTail(_), Save(x, y) -> assert (M.mem y !stackset); ()(*同じ変数を2回退避はさせない。*)
  (* 復帰の仮想命令の実装 (caml2html: emit_restore) *)
  | NonTail(x), Restore(y) when List.mem x allregs ->
     Printf.fprintf oc "\tlw\t%s, %d(%s)\n" x (offset y) reg_sp
  | NonTail(x), Restore(y) ->
     assert (List.mem x allfregs);
     Printf.fprintf oc "\tlw.s\t%s, %d(%s)\n" x (offset y) reg_sp
  (* 末尾だったら計算結果を第一レジスタにセットしてret (caml2html: emit_tailret) *)
  | Tail, (Nop | Sw _ | FSw _ | Comment _ | Save _ as exp) ->
      g' oc (NonTail(Id.gentmp Type.Unit), exp);
      Printf.fprintf oc "\tjr\t%s\n" reg_ra
  | Tail, ( Add _ | Sub _ |Mul _|Div _| SLL _ | SRL _| SRA _| Lw _ |La _ as exp) ->
      g' oc (NonTail(regs.(0)), exp);
      Printf.fprintf oc "\tjr\t%s\n" reg_ra
  | Tail, ( FAdd _ | FSub _ | FMul _ | FInv _|FLw _ | FMov _|FNeg _  as exp) ->
     g' oc (NonTail(fregs.(0)), exp);
     Printf.fprintf oc "\tjr\t%s\n" reg_ra
  | Tail, (Restore(x) as exp) ->
     let r= M.find x !stackset in
     if List.mem r allregs then
       (g' oc (NonTail(regs.(0)),exp);
        Printf.fprintf oc "\tjr\t%s\n" reg_ra)
     else if(List.mem x allfregs) then
       (g' oc (NonTail(fregs.(0)),exp);
        Printf.fprintf oc "\tjr\t%s\n" reg_ra)
  | Tail, IfEq(x, y', e1, e2) ->
     (match y' with
      |V y ->int_tail_if oc x y e1 e2 "be" "bne"(*bneでe2へ分岐,beでe1へ*)
      |C i ->Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sw reg_zero i;
             int_tail_if oc x reg_sw e1 e2 "beq" "bne" )
  | Tail, IfLE(x, y', e1, e2) ->
     (match y' with
      |V y ->Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_cond x y;
             int_tail_if oc reg_cond regs.(0) e1 e2 "bne" "beq"
      |C i ->Printf.fprintf oc "\tslti\t%s, %s, %d\n" reg_cond x i;
             int_tail_if oc reg_cond regs.(0) e1 e2 "bne" "beq")
  | Tail, IfGE(x, y', e1, e2) ->
     (match y' with
      |V y ->Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_cond y x;
             int_tail_if oc reg_cond regs.(0) e1 e2 "bne" "beq"
      |C i ->Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sw regs.(0) i;
             Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_cond reg_sw x;
             int_tail_if oc reg_cond regs.(0) e1 e2 "bne" "beq")
  | Tail, IfFEq(x, y, e1, e2) ->
     Printf.fprintf oc "\tc.eq.s\t%d, %s, %s\n" 0 x y;(*ccは0に決め打ち*)
      f_tail_if oc e1 e2 "bt.s" "bf.s" 0
  | Tail, IfFLE(x, y, e1, e2) ->
      Printf.fprintf oc "\tc.le.s\t%d, %s, %s\n" 0 x y;
      f_tail_if oc e1 e2 "bt.s" "bf.s" 0
  | NonTail(z), IfEq(x, y', e1, e2) ->
     (match y' with
      |V y ->int_nontail_if oc (NonTail(z)) x y e1 e2 "be" "bne"(*bneでe2へ分岐,beでe1へ*)
      |C i ->Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sw reg_zero i;
             int_nontail_if oc (NonTail(z)) x reg_sw e1 e2 "beq" "bne" )
  | NonTail(z), IfLE(x, y', e1, e2) ->
      (match y' with
       |V y ->Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_cond x y;
              int_nontail_if oc (NonTail(z)) reg_cond regs.(0) e1 e2 "bne" "beq"(*bneでe1へ分岐,beqでe2へ*)
       |C i ->Printf.fprintf oc "\tslti\t%s, %s, %d\n" reg_cond x i;
              int_nontail_if oc (NonTail(z)) reg_cond regs.(0) e1 e2 "bne" "beq" )
  | NonTail(z), IfGE(x, y', e1, e2) ->
     (match y' with
      |V y ->Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_cond y x;
             int_nontail_if oc (NonTail(z)) reg_cond regs.(0) e1 e2 "bne" "beq"
      |C i ->Printf.fprintf oc "\taddi\t%s, %s, %d" reg_sw regs.(0) i;
             Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_cond reg_sw x;
             int_nontail_if oc (NonTail(z)) reg_cond regs.(0) e1 e2 "bne" "beq")
  | NonTail(z), IfFEq(x, y, e1, e2) ->
      Printf.fprintf oc "\tc.eq.s\t%d, %s, %s\n" 0 x y;
      f_nontail_if oc (NonTail(z)) e1 e2 "bt.s" "bf.s" 0
  | NonTail(z), IfFLE(x, y, e1, e2) ->
      Printf.fprintf oc "\tc.le.s\t%d, %s, %s\n" 0 x y;
      f_nontail_if oc (NonTail(z)) e1 e2 "bt.s" "bf.s" 0  (* 関数呼び出しの仮想命令の実装 (caml2html: emit_call) *)
  | Tail, CallCls(x, ys, zs) -> (* 末尾呼び出し (caml2html: emit_tailcall) *)
     g'_args oc [(x, reg_cl)] ys zs;(*レジスタ入れ替えでxの位置が分かるように*)
      Printf.fprintf oc "\tlw\t%s, 0(%s)\n" reg_sw reg_cl;
      Printf.fprintf oc "\tjr\t%s\n" reg_sw;
  | Tail, CallDir(Id.L(x), ys, zs) -> (* 末尾呼び出し *)
      g'_args oc [] ys zs;
      Printf.fprintf oc "\tj\t%s\n" x;
  | NonTail(a), CallCls(x, ys, zs) ->
      g'_args oc [(x, reg_cl)] ys zs;
      let ss = stacksize () in
      Printf.fprintf oc "\tsw\t%s, %d(%s)\n" reg_ra (ss-4) reg_sp;
      Printf.fprintf oc "\tlw\t%s, 0(%s)\n" reg_sw reg_cl;
      Printf.fprintf oc "\taddi\t%s, %s, %d,\n" reg_sp reg_sp ss;
      Printf.fprintf oc "\tjalr\t%s\n" reg_sw;(*reg_raをセットしてじゃんぶ*)
      Printf.fprintf oc "\taddi\t%s, %s, -%d\n" reg_sp reg_sp ss;(*即値引き算*)
      Printf.fprintf oc "\tlw\t%s, %d(%s)\n" reg_ra (ss - 4) reg_sp;
      if List.mem a allregs && a <> regs.(0) then
	Printf.fprintf oc "\taddi\t%s, %s, 0\n" regs.(0) a
      else if List.mem a allfregs && a <> fregs.(0) then
	Printf.fprintf oc "\tmov.s\t%s, %s\n" fregs.(0) a
  | NonTail(a), CallDir(Id.L(x), ys, zs) ->
      g'_args oc [] ys zs;
      let ss = stacksize () in
      Printf.fprintf oc "\tsw\t%s, %d(%s)\n" reg_ra (ss-4) reg_sp;
      Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss;
      Printf.fprintf oc "\tjal\t%s\n" x;
      Printf.fprintf oc "\taddi\t%s, %s, -%d\n" reg_sp reg_sp ss;
      Printf.fprintf oc "\tlw\t%s, %d(%s)\n" reg_ra (ss - 4) reg_sp;
      if List.mem a allregs && a <> regs.(0) then
	Printf.fprintf oc "\taddi\t%s, %s, 0\n" regs.(0) a
      else if List.mem a allfregs && a <> fregs.(0) then
	Printf.fprintf oc "\tmov.s\t%s, %s\n" fregs.(0) a
and int_tail_if oc r1 r2 e1 e2 b bn =
  let b_else = Id.genid (b ^ "_else") in
  Printf.fprintf oc "\t%s\t%s, %s, %s\n" bn r1 r2 b_else;
  let stackset_back = !stackset in
  g oc (Tail, e1);
  Printf.fprintf oc "%s:\n" b_else;(*同じラベルたくさん*)
  stackset := stackset_back;(*e1を展開した時の影響を除去してから*)
  g oc (Tail, e2)
and f_tail_if oc e1 e2 b bn cc =
  let b_else = Id.genid (b ^ "_else") in
  Printf.fprintf oc "\t%s\t%i, %s\n" bn cc b_else;
  let stackset_back = !stackset in
  g oc (Tail, e1);
  Printf.fprintf oc "%s:\n" b_else;
  stackset := stackset_back;(*e1を展開した時の影響を除去してから*)
  g oc (Tail, e2)
and int_nontail_if oc dest r1 r2 e1 e2 b bn =
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
  Printf.fprintf oc "\t%s\t%s, %s, %s\n" bn r1 r2 b_else;
  let stackset_back = !stackset in
  g oc (dest, e1);
  let stackset1 = !stackset in
  Printf.fprintf oc "\tj\t%s\n" b_cont;
  Printf.fprintf oc "%s:\n" b_else;
  stackset := stackset_back;
  g oc (dest, e2);
  Printf.fprintf oc "%s:\n" b_cont;
  let stackset2 = !stackset in
  stackset := M.filter (fun key _ -> M.mem key stackset1) stackset2
                (*stackset1と2の共通部分を取った*)
and f_nontail_if  oc dest e1 e2 b bn cc=
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
  Printf.fprintf oc "\t%s\t%d, %s\n" bn cc b_else;
  let stackset_back = !stackset in
  g oc (dest, e1);
  let stackset1 = !stackset in
  Printf.fprintf oc "\tj\t%s\n" b_cont;
  Printf.fprintf oc "%s:\n" b_else;
  stackset := stackset_back;
  g oc (dest, e2);
  Printf.fprintf oc "%s:\n" b_cont;
  let stackset2 = !stackset in
  stackset := M.filter (fun key _ -> M.mem key stackset1) stackset2
and g'_args oc x_reg_cl ys zs =(*関数呼び出しように、レジスタを配置*)
  let (i, yrs) =
    List.fold_left(*0でなく1から引数を割り当て,ここでは気にせずおうけい*)
      (fun (i, yrs) y -> (i + 1, (y, regs.(i)) :: yrs))
      (0, x_reg_cl)
      ys in
  List.iter
    (fun (y, r) -> Printf.fprintf oc "\taddi\t%s, %s, 0\n" r y)
    (shuffle reg_sw yrs);
  let (d, zfrs) =
    List.fold_left
      (fun (d, zfrs) z -> (d + 1, (z, fregs.(d)) :: zfrs))
      (0, [])
      zs in
      List.iter
        (fun (z, fr) ->
          Printf.fprintf oc "\taddi\t%s, %s, 0\n" fr z)
        (shuffle reg_fsw zfrs)

let h oc { name = Id.L(x); args = _; fargs = _; body = e; ret = _ } =
  Printf.fprintf oc "%s:\n" x;(*ラベル*)
  stackset := M.empty;
  stackmap := [];
  g oc (Tail, e)

let f oc (Prog(data, fundefs, e)) =
  Format.eprintf "generating assembly...@.";
  Printf.fprintf oc ".section\t\".rodata\"\n";
  Printf.fprintf oc ".align\t8\n";
  List.iter
    (fun (Id.L(x), d) ->
      Printf.fprintf oc "%s:\t! %f\n" x d;
      Printf.fprintf oc "\t.long\t0x%lx\n" (gethi d);
      Printf.fprintf oc "\t.long\t0x%lx\n" (getlo d))
    data;
  Printf.fprintf oc ".section\t\".text\"\n";
  List.iter (fun fundef -> h oc fundef) fundefs;
  Printf.fprintf oc ".global\tmin_caml_start\n";
  Printf.fprintf oc "min_caml_start:\n";
  (*Printf.fprintf oc "\tsave\t%%sp, -112, %%sp\n"; (* from gcc; why 112? *)*)
  stackset := M.empty;
  stackmap := [];
  g oc (NonTail("%g0"), e);
  Printf.fprintf oc "\thlt\n"
