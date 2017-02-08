open Asm

(*
先行命令列、preを引数として追加
2回目のsaveの時に、その変数がrefreshされたref変数に当たるか調べるため*)
external gethi : float -> int32 = "gethi"
(*external getlo : float -> int32 = "getlo"*)

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
let offset x = try 1 * List.hd (locate x)
               with Failure "hd" ->(Format.eprintf "%s!\n" x;1)
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

let rec is_fresh_ref pre r =(*rが再代入されたref変数に当たるか調べる*)
  match pre with
  |Ans(exp) ->is_fresh_ref' exp r
  |Let((x,t),exp,e) when x=r ->
    let (there_is_call,is_fresh) =is_fresh_ref e r in
    if(is_fresh) then (true,is_fresh)(*後ろから調べる*)
    else
      (*関数呼び出しで全てのレジスタが破壊される,caller_save*)
      if(there_is_call) then (there_is_call,false)
      else
        (match t with
         |Type.Ref _ ->(match exp with
                        |Restore _ ->(true,false)
                        |_ ->(true,true))(*expによって値が代入された*)
         |_ ->(true,false))(*rが代入されるのでis_callをtrueにする*)
  |Let(_,exp,e) ->
    let (there_is_call,is_fresh) =is_fresh_ref e r in
    if(is_fresh) then (there_is_call,is_fresh)
    else if(there_is_call) then (there_is_call,false)
    else
      is_fresh_ref' exp r
and is_fresh_ref' exp r =
  match exp with
  |IfEq(_,_,e1,e2)|IfLE(_,_,e1,e2)|IfGE(_,_,e1,e2)
   |IfFEq(_,_,e1,e2)|IfFLE(_,_,e1,e2) ->
    let (there_is_call1,t1)=is_fresh_ref e1 r in
    let (there_is_call2,t2)=is_fresh_ref e2 r in
    (if t1<>t2 then Format.eprintf "ref partially refreshed\n");
        ((there_is_call1)||(there_is_call2),t1)
  |ForLE((_,_,step),e) ->
    let (there_is_call1,t1)=is_fresh_ref step r in
    if(there_is_call1) then(there_is_call1,t1)
    else
    let (there_is_call2,t2)=is_fresh_ref e r in
    (there_is_call1||there_is_call2,t1||t2)
  |CallCls _|CallDir _ ->
    (true,false)
  |_ ->(false,false)
    
                     
      

type dest = Tail | NonTail of Id.t (* 末尾かどうかを表すデータ型 (caml2html: emit_dest) *)
let rec g oc pre = function (* 命令列のアセンブリ生成 (caml2html: emit_g) *)
  | dest, Ans(exp) -> g' oc pre (dest, exp)
  | dest, Let((x, t), exp, e) ->
     g' oc pre (NonTail(x), exp);(*xがunit型の場合、xに依存しない出力になる*)
     g oc (cons pre (Let((x,t),exp,Ans(Nop)))) (dest, e)
and g' oc pre = function (* 各命令のアセンブリ生成 (caml2html: emit_gprime) *)
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
  | NonTail(x), Or(y, z) -> Printf.fprintf oc "\tor\t%s, %s, %s\n" x y z
  | NonTail(x), SLL(y, c) -> Printf.fprintf oc "\tsll\t%s, %s, %d\n" x y c
  | NonTail(x), SRL(y, c) -> Printf.fprintf oc "\tsrl\t%s, %s, %d\n" x y c
  | NonTail(x), SRA(y, c) -> Printf.fprintf oc "\tsra\t%s, %s, %d\n" x y c
  | NonTail(x), Lw(c,y) -> Printf.fprintf oc "\tlw\t%s, %d(%s)\n" x c y
  | NonTail(x), Lui(c) -> Printf.fprintf oc "\tlui\t%s, %d\n" x c
  | NonTail(x), La(Id.L(y)) ->Printf.fprintf oc "\tla\t%s, %s\n" x y
  | NonTail(_), Sw(x,c,y) -> Printf.fprintf oc "\tsw\t%s, %d(%s)\n" x c y
  | NonTail(x), FLw(c,y) -> Printf.fprintf oc "\tlw.s\t%s, %d(%s)\n" x c y
  | NonTail(_), FSw(x,c,y) -> Printf.fprintf oc "\tsw.s\t%s, %d(%s)\n" x c y
  | NonTail(x), FAdd(y, z) -> Printf.fprintf oc "\tadd.s\t%s, %s, %s\n" x y z
  | NonTail(x), FSub(y, z) -> Printf.fprintf oc "\tsub.s\t%s, %s, %s\n" x y z
  | NonTail(x), FMul(y, z) -> Printf.fprintf oc "\tmul.s\t%s, %s, %s\n" x y z
  | NonTail(x), FDiv(y, z) -> Printf.fprintf oc "\tdiv.s\t%s, %s, %s\n" x y z
  | NonTail(x), FMov(y) -> Printf.fprintf oc "\tmov.s\t%s, %s\n" x y
  | NonTail(x), FNeg(y) -> Printf.fprintf oc "\tneg.s\t%s, %s\n" x y
  | NonTail(x), Ftoi(y) -> Printf.fprintf oc "\tftoi\t%s, %s\n" x y
  | NonTail(x), Itof(y) -> Printf.fprintf oc "\titof\t%s, %s\n" x y
  | NonTail(x), FAbs(y) -> Printf.fprintf oc "\tabs.s\t%s, %s\n" x y
  | NonTail(x), FSqrt(y) -> Printf.fprintf oc "\tsqrt.s\t%s, %s\n" x y
  | NonTail(_), Acc(acc,y) ->Printf.fprintf oc "\tacc\t%s, %s\n" acc y
  | NonTail(x), In -> Printf.fprintf oc "\tlui\t%s, 0\n\tin\t%s\n" x x
  | NonTail(_), Out(x) -> Printf.fprintf oc "\tout\t%s\n" x
  | NonTail(_), Comment(s) -> Printf.fprintf oc "\t! %s\n" s
  (* 退避の仮想命令の実装 (caml2html: emit_save) *)
  | NonTail(_), Save(x, y)  when List.mem x allregs && not (M.mem y !stackset) ->
      save y x;
      Printf.fprintf oc "\tsw\t%s, %d(%s)\n" x (offset y) reg_sp
  | NonTail(_), Save(x, y)  when List.mem x allfregs && not (M.mem y !stackset) ->
     save y x;
     Printf.fprintf oc "\tsw.s\t%s, %d(%s)\n" x (offset y) reg_sp
  | NonTail(_), Save(x, y) when List.mem x allregs->
     assert (M.mem y !stackset);
     let _,is_fresh=is_fresh_ref pre x in
  if(is_fresh) then(*ref変数が再代入されていたらsaveし直す*)
    (save y x; 
     Printf.fprintf oc "\tsw\t%s, %d(%s)\n" x (offset y) reg_sp)
     else
       ()
  | NonTail(_), Save(x, y) ->
     if not (M.mem y !stackset) then
       Format.eprintf "save(%s,%s)!!\n"  x y
     else
       let _,is_fresh=is_fresh_ref pre x in
       if(is_fresh) then
       (save y x;
       Printf.fprintf oc "\tsw.s\t%s, %d(%s)\n" x (offset y) reg_sp)
     else
       ()
  (* 復帰の仮想命令の実装 (caml2html: emit_restore) *)
  | NonTail(x), Restore(y) when List.mem x allregs ->
     Printf.fprintf oc "\tlw\t%s, %d(%s)\n" x (offset y) reg_sp
  | NonTail(x), Restore(y) ->
     assert (List.mem x allfregs);
     Printf.fprintf oc "\tlw.s\t%s, %d(%s)\n" x (offset y) reg_sp
  | NonTail(_), ForLE(((i,a'),(j',k'),step),e)->
     (*(match a' with
      |V(a) ->Printf.fprintf oc "\taddi\t%s, %s, 0\n"i a
      |C(a_i) ->Printf.fprintf oc "\taddi\t%s, %s, %d\n" i reg_zero a_i);*)
     let stack_set_back = !stackset in
     let lavel=Id.genid "loop" in
     let lavel_end=Id.genid "loop_end" in
     (if(j'=V(i)) then
       (match k' with
        |V(k) ->
          Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_sw i k;
          Printf.fprintf oc "\tbeq\t%s, %s, %s\n" reg_zero reg_sw lavel_end
        |C(k_i) ->
          Printf.fprintf oc "\tslti\t%s, %s, %d\n" reg_sw i k_i;
          Printf.fprintf oc "\tbeq\t%s, %s, %s\n" reg_zero reg_sw lavel_end)
     else if(k'=V(i)) then
       (match j' with
        |V(j) ->
          Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_sw j i;
          Printf.fprintf oc "\tbeq\t%s, %s, %s\n" reg_zero reg_sw lavel_end
        |C(j_i) ->
          Printf.fprintf oc "\tslti\t%s, %s, %d\n" reg_sw i (j_i-1);
          Printf.fprintf oc "\tbne\t%s, %s, %s\n" reg_zero reg_sw lavel_end)
     else
       assert false);
     Printf.fprintf oc "%s:\n" lavel;
     let pre' = cons pre (Ans(ForLE(((i,a'),(j',k'),step),e))) in
                     (*先行命令としてループ自信を加える*)
     g oc pre' (NonTail("%g0"),(cons e step));
     (if(j'=V(i)) then
       (match k' with
        |V(k) ->
          Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_sw i k;
          Printf.fprintf oc "\tbne\t%s, %s, %s\n" reg_zero reg_sw lavel
        |C(k_i) ->
          Printf.fprintf oc "\tslti\t%s, %s, %d\n" reg_sw i k_i;
          Printf.fprintf oc "\tbne\t%s, %s, %s\n" reg_zero reg_sw lavel)
     else if(k'=V(i)) then
       (match j' with
        |V(j) ->
          Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_sw j i;
          Printf.fprintf oc "\tbne\t%s, %s, %s\n" reg_zero reg_sw lavel
        |C(j_i) ->
          Printf.fprintf oc "\tslti\t%s, %s, %d\n" reg_sw i (j_i-1);
          Printf.fprintf oc "\tbeq\t%s, %s, %s\n" reg_zero reg_sw lavel)
     else
       assert false);
     Printf.fprintf oc "%s:\n" lavel_end;
     stackset:=stack_set_back
  |_,Ref_Get _|_,Ref_Put _ |_,Ref_FGet _|_,Ref_FPut _ ->assert false
  (* 末尾だったら計算結果を第一レジスタにセットしてret (caml2html: emit_tailret) *)
  | Tail, (Nop | Sw _ | FSw _ |Acc _| Comment _ | Save _ |Out _ |ForLE _ as exp) ->
      g' oc pre (NonTail(Id.gentmp Type.Unit), exp);
      Printf.fprintf oc "\tjr\t%s\n" reg_ra
  | Tail, ( Add _ | Sub _ |Mul _|Div _| SLL _ | SRL _| SRA _| Lw _ |La _ |Ftoi _
            |In |Lui _ |Or _ as exp) ->
      g' oc pre (NonTail(regs.(0)), exp);
      Printf.fprintf oc "\tjr\t%s\n" reg_ra
  | Tail, ( FAdd _ | FSub _ | FMul _ | FDiv _|FLw _ | FMov _|FNeg _  
            |Itof _ | FAbs _| FSqrt _ as exp) ->
     g' oc pre (NonTail(fregs.(0)), exp);
     Printf.fprintf oc "\tjr\t%s\n" reg_ra
  | Tail, (Restore(x) as exp) ->
     let r= M.find x !stackset in
     if List.mem r allregs then
       (g' oc pre (NonTail(regs.(0)),exp);
        Printf.fprintf oc "\tjr\t%s\n" reg_ra)
     else if(List.mem x allfregs) then
       (g' oc pre (NonTail(fregs.(0)),exp);
        Printf.fprintf oc "\tjr\t%s\n" reg_ra)
         
  | Tail, IfEq(x, y', e1, e2) ->
     (match y' with
      |V y ->int_tail_if oc pre x y e1 e2 "be" "bne"(*bneでe2へ分岐,beでe1へ*)
      |C i ->Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sw reg_zero i;
             int_tail_if oc pre x reg_sw e1 e2 "beq" "bne" )
  | Tail, IfLE(x, y', e1, e2) ->
     (match y' with
      |V y ->Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_sw x y;
             int_tail_if oc pre reg_sw reg_zero e1 e2 "bne" "beq"
      |C i ->Printf.fprintf oc "\tslti\t%s, %s, %d\n" reg_sw x i;
             int_tail_if oc pre reg_sw reg_zero e1 e2 "bne" "beq")
  | Tail, IfGE(x, y', e1, e2) ->
     (match y' with
      |V y ->Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_sw y x;
             int_tail_if oc pre reg_sw reg_zero e1 e2 "bne" "beq"
      |C i ->Printf.fprintf oc "\tslti\t%s, %s, %d\n" reg_sw x (i-1);
             int_tail_if oc pre reg_sw reg_zero e1 e2 "beq" "bne")
  | Tail, IfFEq(x, y, e1, e2) ->
     Printf.fprintf oc "\tc.eq.s\t%d, %s, %s\n" 0 x y;(*ccは0に決め打ち*)
     f_tail_if oc pre e1 e2 "bt.s" "bf.s" 0
  | Tail, IfFLE(x, y, e1, e2) ->
      Printf.fprintf oc "\tc.le.s\t%d, %s, %s\n" 0 x y;
      f_tail_if oc pre e1 e2 "bt.s" "bf.s" 0
  | NonTail(z), IfEq(x, y', e1, e2) ->
     (match y' with
      |V y ->int_nontail_if oc pre (NonTail(z)) x y e1 e2 "beq" "bne"(*bneでe2へ分岐,beでe1へ*)
      |C i ->Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sw reg_zero i;
             int_nontail_if oc pre (NonTail(z)) x reg_sw e1 e2 "beq" "bne" )
  | NonTail(z), IfLE(x, y', e1, e2) ->
      (match y' with
       |V y ->Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_sw x y;
              int_nontail_if oc pre  (NonTail(z)) reg_sw reg_zero e1 e2 "bne" "beq"(*bneでe1へ分岐,beqでe2へ*)
       |C i ->Printf.fprintf oc "\tslti\t%s, %s, %d\n" reg_sw x i;
              int_nontail_if oc pre (NonTail(z)) reg_sw reg_zero e1 e2 "bne" "beq" )
  | NonTail(z), IfGE(x, y', e1, e2) ->
     (match y' with
      |V y ->Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_sw y x;
             int_nontail_if oc pre (NonTail(z)) reg_sw reg_zero e1 e2 "bne" "beq"
      |C i ->Printf.fprintf oc "\tslti\t%s, %s, %d\n" reg_sw x (i-1);
             int_nontail_if oc pre (NonTail(z)) reg_sw reg_zero e1 e2 "beq" "bne")
  | NonTail(z), IfFEq(x, y, e1, e2) ->
      Printf.fprintf oc "\tc.eq.s\t%d, %s, %s\n" 0 x y;
      f_nontail_if oc pre (NonTail(z)) e1 e2 "bt.s" "bf.s" 0
  | NonTail(z), IfFLE(x, y, e1, e2) ->
      Printf.fprintf oc "\tc.le.s\t%d, %s, %s\n" 0 x y;
      f_nontail_if oc pre (NonTail(z)) e1 e2 "bt.s" "bf.s" 0  (* 関数呼び出しの仮想命令の実装 (caml2html: emit_call) *)
  | Tail, CallCls(x, ys, zs) -> (* 末尾呼び出し (caml2html: emit_tailcall) *)
     g'_args oc [(x, reg_cl)] ys zs;(*レジスタ入れ替えでxの位置が分かるように*)
      Printf.fprintf oc "\tlw\t%s, 0(%s)\n" reg_sw reg_cl;
      Printf.fprintf oc "\tjr\t%s\n" reg_sw;
  | Tail, CallDir(Id.L(x), ys, zs) -> (* 末尾呼び出し *)
      g'_args oc [] ys zs;
      Printf.fprintf oc "\tj\t%s\n" x;
  | Tail, Run_parallel(a,d,ys,zs) ->
     g'_args oc [] ys zs;
     Printf.fprintf oc "\tfork\t%s, %s" a d
  | NonTail(_), Run_parallel(a,d,ys,zs) ->
     g'_args oc [] ys zs;
      let ss = stacksize () in
      Printf.fprintf oc "\tsw\t%s, %d(%s)\n" reg_ra (ss-1) reg_sp;
      Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss;
      Printf.fprintf oc "\tfork\t%s, %s\n" a d; (* returnアドレスいらない? *)
      Printf.fprintf oc "\taddi\t%s, %s, -%d\n" reg_sp reg_sp ss;
      Printf.fprintf oc "\tlw\t%s, %d(%s)\n" reg_ra (ss - 1) reg_sp;

  | NonTail(a), CallCls(x, ys, zs) ->
      g'_args oc [(x, reg_cl)] ys zs;
      let ss = stacksize () in
      Printf.fprintf oc "\tsw\t%s, %d(%s)\n" reg_ra (ss-1) reg_sp;
      Printf.fprintf oc "\tlw\t%s, 0(%s)\n" reg_sw reg_cl;
      Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss;
      Printf.fprintf oc "\tjalr\t%s\n" reg_sw;(*reg_raをセットしてじゃんぶ*)
      Printf.fprintf oc "\taddi\t%s, %s, -%d\n" reg_sp reg_sp ss;(*即値引き算*)
      Printf.fprintf oc "\tlw\t%s, %d(%s)\n" reg_ra (ss - 1) reg_sp;
      if List.mem a allregs && a <> regs.(0) then
	Printf.fprintf oc "\taddi\t%s, %s, 0\n" a regs.(0)
      else if List.mem a allfregs && a <> fregs.(0) then
	Printf.fprintf oc "\tmov.s\t%s, %s\n" a fregs.(0)
  | NonTail(a), CallDir(Id.L(x), ys, zs) ->
      g'_args oc [] ys zs;
      let ss = stacksize () in
      Printf.fprintf oc "\tsw\t%s, %d(%s)\n" reg_ra (ss-1) reg_sp;
      Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss;
      Printf.fprintf oc "\tjal\t%s\n" x;
      Printf.fprintf oc "\taddi\t%s, %s, -%d\n" reg_sp reg_sp ss;
      Printf.fprintf oc "\tlw\t%s, %d(%s)\n" reg_ra (ss - 1) reg_sp;
      if List.mem a allregs && a <> regs.(0) then
	Printf.fprintf oc "\taddi\t%s, %s, 0\n" a regs.(0)
      else if List.mem a allfregs && a <> fregs.(0) then
	Printf.fprintf oc "\tmov.s\t%s, %s\n" a fregs.(0)
  |_,Next ->assert false     
and int_tail_if oc pre r1 r2 e1 e2 b bn =(*bn r1 r2がtrueでe1*)
  let b_else = Id.genid (b ^ "_else") in
  Printf.fprintf oc "\t%s\t%s, %s, %s\n" bn r1 r2 b_else;
  let stackset_back = !stackset in
  g oc pre (Tail, e1);
  Printf.fprintf oc "%s:\n" b_else;
  stackset := stackset_back;(*e1を展開した時の影響を除去してから*)
  g oc pre (Tail, e2)
and f_tail_if oc pre e1 e2 b bn cc =
  let b_else = Id.genid (b ^ "_else") in
  Printf.fprintf oc "\t%s\t%i, %s\n" bn cc b_else;
  let stackset_back = !stackset in
  g oc pre (Tail, e1);
  Printf.fprintf oc "%s:\n" b_else;
  stackset := stackset_back;(*e1を展開した時の影響を除去してから*)
  g oc pre (Tail, e2)
and int_nontail_if oc pre dest r1 r2 e1 e2 b bn =
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
  Printf.fprintf oc "\t%s\t%s, %s, %s\n" bn r1 r2 b_else;
  let stackset_back = !stackset in
  g oc pre (dest, e1);
  let stackset1 = !stackset in
  Printf.fprintf oc "\tj\t%s\n" b_cont;
  Printf.fprintf oc "%s:\n" b_else;
  stackset := stackset_back;
  g oc pre (dest, e2);
  Printf.fprintf oc "%s:\n" b_cont;
  let stackset2 = !stackset in
  stackset := M.filter (fun key _ -> M.mem key stackset1) stackset2;
(*stackset1と2の共通部分を取った*)
and f_nontail_if  oc pre dest e1 e2 b bn cc=
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
  Printf.fprintf oc "\t%s\t%d, %s\n" bn cc b_else;
  let stackset_back = !stackset in
  g oc pre (dest, e1);
  let stackset1 = !stackset in
  Printf.fprintf oc "\tj\t%s\n" b_cont;
  Printf.fprintf oc "%s:\n" b_else;
  stackset := stackset_back;
  g oc pre (dest, e2);
  Printf.fprintf oc "%s:\n" b_cont;
  let stackset2 = !stackset in
  stackset := M.filter (fun key _ -> M.mem key stackset1) stackset2;
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
  (List.iter
    (fun (z, fr) ->
      Printf.fprintf oc "\tmov.s\t%s, %s\n" fr z)
    (shuffle reg_fsw zfrs))
        

let h oc { name = Id.L(x); args = _; fargs = _; body = e; ret = _ } =
  Printf.fprintf oc "%s:\n" x;(*ラベル*)
  stackset := M.empty;
  stackmap := [];
  g oc (Ans(Nop)) (Tail, e)

let print_parallel oc = function
  |Some {pargs=_;
         pfargs=_;
         index=(i,(j',k'));
         pbody=e} ->
         
     let lavel=Id.genid "loop" in
     let lavel_end=Id.genid "loop_end" in
     Printf.fprintf oc "\tnext\t%s\n" i;
     (if(j'=V(i)) then
       (match k' with
        |V(k) ->
          Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_sw i k;
          Printf.fprintf oc "\tbeq\t%s, %s, %s\n" reg_zero reg_sw lavel_end
        |C(k_i) ->
          Printf.fprintf oc "\tslti\t%s, %s, %d\n" reg_sw i k_i;
          Printf.fprintf oc "\tbeq\t%s, %s, %s\n" reg_zero reg_sw lavel_end)
     else if(k'=V(i)) then
       (match j' with
        |V(j) ->
          Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_sw j i;
          Printf.fprintf oc "\tbeq\t%s, %s, %s\n" reg_zero reg_sw lavel_end
        |C(j_i) ->
          Printf.fprintf oc "\tslti\t%s, %s, %d\n" reg_sw i (j_i-1);
          Printf.fprintf oc "\tbne\t%s, %s, %s\n" reg_zero reg_sw lavel_end)
     else
       assert false);
     Printf.fprintf oc "%s:\n" lavel;

     g oc (Ans(Nop)) (NonTail("%g0"), e);
     (if(j'=V(i)) then
       (match k' with
        |V(k) ->
          Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_sw i k;
          Printf.fprintf oc "\tbne\t%s, %s, %s\n" reg_zero reg_sw lavel
        |C(k_i) ->
          Printf.fprintf oc "\tslti\t%s, %s, %d\n" reg_sw i k_i;
          Printf.fprintf oc "\tbne\t%s, %s, %s\n" reg_zero reg_sw lavel)
     else if(k'=V(i)) then
       (match j' with
        |V(j) ->
          Printf.fprintf oc "\tslt\t%s, %s, %s\n" reg_sw j i;
          Printf.fprintf oc "\tbne\t%s, %s, %s\n" reg_zero reg_sw lavel
        |C(j_i) ->
          Printf.fprintf oc "\tslti\t%s, %s, %d\n" reg_sw i (j_i-1);
          Printf.fprintf oc "\tbeq\t%s, %s, %s\n" reg_zero reg_sw lavel)
     else
       assert false);
     Printf.fprintf oc "%s:\n" lavel_end;
     Printf.fprintf oc "\tend\n"

  |None-> ()
    


let print_const oc (e:HpAlloc.t)=
  match e with
  |HpAlloc.Unit ->()
  |HpAlloc.Int(i) ->Printf.fprintf oc "\t0x%x\n" i
  |HpAlloc.Float(d) ->Printf.fprintf oc "\t0x%lx\n" (gethi d)
  |HpAlloc.ConstTuple(Id.L(x))|HpAlloc.ConstArray(Id.L(x))
   ->Printf.fprintf oc "\t%s\n" x
  |_ ->assert false(*eは定数でないといけない*)

    
let print_array oc {HpAlloc.name=(Id.L(x),t);HpAlloc.size=i;HpAlloc.initv=e}=
  Printf.fprintf oc "%s:\t! array\n" x;
  let rec print_elements n=
    if(n=0) then () else
      (print_const oc e;
       print_elements (n-1)) in
  print_elements i

let print_tuple oc {HpAlloc.name=(Id.L(x),t);HpAlloc.body=es}=
  Printf.fprintf oc "%s:\t! tuple\n" x;
  List.iter
    (print_const oc)
    es


    
let f oc oc_childe (Prog(data, fundefs,parallel, e)) =
  Format.eprintf "generating assembly...@.";
  Printf.fprintf oc  ".section\t\".rodata\"\n";
  Printf.fprintf oc ".align\t8\n";
  List.iter
    (fun (Id.L(x), d) ->
      Printf.fprintf oc "%s:\t! %f\n" x d;
      Printf.fprintf oc "\t0x%lx\n" (gethi d);)
    data;
  List.iter(*静的な組*)
    (print_tuple oc)
    !HpAlloc.tuples;
  List.iter(*静的な配列*)
    (print_array oc)
    !HpAlloc.arrays;
  Printf.fprintf oc ".section\t\".text\"\n";
  Printf.fprintf oc ".global\tmin_caml_start\n";
  Printf.fprintf oc "min_caml_start:\n";
  stackset := M.empty;
  stackmap := [];
  g oc (Ans(Nop)) (NonTail(regs.(0)), e);
  Printf.fprintf oc "\tin\t%%r1\n";
  Printf.fprintf oc "\tj\tmin_caml_start\n";
  List.iter (fun fundef -> h oc fundef) fundefs;

  (* 以下子コア用のコード *)
  Printf.fprintf oc_childe  ".section\t\".rodata\"\n";
  Printf.fprintf oc_childe ".align\t8\n";
  List.iter
    (fun (Id.L(x), d) ->
      Printf.fprintf oc_childe "%s:\t! %f\n" x d;
      Printf.fprintf oc_childe "\t0x%lx\n" (gethi d);)
    data;
  List.iter(*静的な組*)
    (print_tuple oc_childe)
    !HpAlloc.tuples;
  List.iter(*静的な配列*)
    (print_array oc_childe)
    !HpAlloc.arrays;
  Printf.fprintf oc_childe ".section\t\".text\"\n";
  Printf.fprintf oc_childe ".global\tmin_caml_start\n";
  Printf.fprintf oc_childe "min_caml_start:\n";
  stackset := M.empty;
  stackmap := [];
  print_parallel oc_childe parallel;
  List.iter (fun fundef -> h oc_childe fundef) fundefs
