
type id_or_imm = V of Id.t | C of int
let to_id_imm =function
  |Id.V(x) ->V(x)
  |Id.C(i) ->C(i)
type t = (* 命令の列 (caml2html: sparcasm_t) *)
  | Ans of exp
  | Let of (Id.t * Type.t) * exp * t
 and exp = (* 一つ一つの命令に対応する式 論理演算なし//比較や分岐は後//addiとaddを分けるのも後 *)
   | Nop
   | Mov of Id.t
   | Movi of int
   | Add of Id.t * id_or_imm
   | Sub of Id.t * Id.t
   | Mul of Id.t * Id.t
   | Div of Id.t * Id.t
   | SLL of Id.t * int          (* sl2へはemitで変換 *)
   | SRL of Id.t * int
   | SRA of Id.t * int

   | FAdd of Id.t * Id.t
   | FSub of Id.t * Id.t
   | FMul of Id.t * Id.t
   | FDiv of Id.t * Id.t
   | FMov of Id.t
   | FNeg of Id.t
   | FAbs of Id.t 
   | FSqrt of Id.t
   (* メモリアクセス *)
   | Lw of int * Id.t
   | Lwi of int * Id.l
   | FLw of  int * Id.t
   | FLwi of int*Id.l
   | Sw of Id.t *int * Id.t 
   | Swi of Id.t *int* Id.l
   | FSw of Id.t * int * Id.t
   | FSwi of Id.t *int* Id.l

   | La of Id.l                 (* constarrayを値として表現するため（潰せるはず） *)
                      
   | Ftoi of Id.t
   | Itof of Id.t
   | In
   | FIn
   | Out of Id.t
   | Comment of string
   (* virtual instructions *)
   | IfEq of Id.t * id_or_imm * t * t
   | IfLE of Id.t * id_or_imm * t * t (* ifge消去*)

   | IfFZ of  Id.t * t * t      (* 0との比較 *)
   | IfFLE of Id.t * Id.t * t * t
   (* closure address, integer arguments, and float arguments *)
   | CallCls of Id.t * Id.t list * Id.t list
   | CallDir of Id.l * Id.t list * Id.t list
   | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 (caml2html: sparcasm_save) *)
   | Restore of Id.t (* スタック変数から値を復元 (caml2html: sparcasm_restore) *)
   |ForLE of ((Id.t* id_or_imm) * (id_or_imm * id_or_imm) * t) *t
   |Ref_Get of Id.t
   |Ref_Put of Id.t * Id.t
   |Ref_FGet of Id.t
   |Ref_FPut of Id.t * Id.t
   |Run_parallel of Id.t*Id.t*Id.t list *Id.t list
   |Next
   |Acc of Id.t*Id.t


type parallel={pargs :Id.t  list;
               pfargs:Id.t list;
               index:(Id.t*(id_or_imm*id_or_imm)) ;
               pbody : t ;
              }

type fundef = { name : Id.l; args : Id.t list; fargs : Id.t list; body : t; ret : Type.t }
(* プログラム全体 = 浮動小数点数テーブル + トップレベル関数 + メインの式 (caml2html: sparcasm_prog) *)
type prog = Prog of (Id.l * float) list * fundef list *parallel option * t

let fletd(x, e1, e2) = Let((x, Type.Float), e1, e2)
let seq(e1, e2) = Let((Id.gentmp Type.Unit, Type.Unit), e1, e2)

let regs =  Array.init 29 (fun i -> Printf.sprintf "%%r%d" i) 
  (*[| "%i2"; "%i3"; "%i4"; "%i5";
     "%l0"; "%l1"; "%l2"; "%l3"; "%l4"; "%l5"; "%l6"; "%l7";
     "%o0"; "%o1"; "%o2"; "%o3"; "%o4"; "%o5" |]*)
let fregs = Array.init 29 (fun i -> Printf.sprintf "%%f%d" i)
let allregs = Array.to_list regs
let allfregs = Array.to_list fregs
let acc1 = "%f29"
let acc2 = "%f30"
let acc3 = "%f31"
let allaccs = [acc1;acc2;acc3]
             
let reg_cl = regs.(Array.length regs - 1)(* closure address (caml2html: sparcasm_regcl) *)
let reg_sw = "%r29"
let reg_fsw = fregs.(Array.length fregs - 1) (* temporary for swap *)
let reg_sp = "%r30" (* stack pointer *)
let reg_hp = "%r31" (* heap pointer *)
let is_reg x = (x.[0] = '%')


(*浮動小数は32ビットなのでいらない。*)
(*let co_freg_table =
  let ht = Hashtbl.create 16 in
  for i = 0 to 15 do
    Hashtbl.add
      ht
      (Printf.sprintf "%%f%d" (i * 2))
      (Printf.sprintf "%%f%d" (i * 2 + 1))
  done;
  ht
let co_freg freg = Hashtbl.find co_freg_table freg (* "companion" freg *)
 *)
                 
(* super-tenuki *)
let rec remove_and_uniq xs = function
  | [] -> []
  | x :: ys when S.mem x xs -> remove_and_uniq xs ys
  | x :: ys -> x :: remove_and_uniq (S.add x xs) ys

(* free variables in the order of use (for spilling) (caml2html: sparcasm_fv) *)
let fv_id_or_imm = function V(x) -> [x] | _ -> []
let rec fv_exp = function
  | Nop ->[]
  | Mov(x) -> [x]
  | Movi _ ->[]
  | Add(x,y') ->x::fv_id_or_imm y'
  | Sub(x,y) ->[x;y]
  | Mul(x,y) ->[x;y]
  | Div(x,y) ->[x;y]
  | SLL(x,_) ->[x]
  | SRL(x,_) ->[x]
  | SRA(x,_) ->[x]

   | FAdd(x,y) ->[x;y]
   | FSub(x,y) ->[x;y]                   
   | FMul(x,y) ->[x;y]
   | FDiv(x,y) ->[x;y]
   | FMov(x) ->[x]
   | FNeg(x) ->[x]
   | FAbs(x) ->[x]
   | FSqrt(x) ->[x]                 
   (* メモリアクセス *)
   | Lw(_,x) ->[x]
   | Lwi _ ->[]
   | FLw(_,x) ->[x]
   | FLwi _ ->[]
   | Sw(x,_,y) ->[x;y]
   | Swi(x,_,_) ->[x]
   | FSw(x,_,y) ->[x;y]
   | FSwi(x,_,_) ->[x]

   | La _ ->[]
                      
   | Ftoi(x) ->[x]
   | Itof(y) ->[y]
   | In ->[]
   | FIn ->[]
   | Out(x) ->[x]
   | Comment _ ->[]
   (* virtual instructions *)
   | IfEq(x,y',e1,e2)|IfLE(x,y',e1,e2) ->
      x::fv_id_or_imm y' @remove_and_uniq S.empty (fv e1 @ fv e2)
   | IfFZ(x,e1,e2)->
      x:: remove_and_uniq S.empty (fv e1 @ fv e2)
   | IfFLE(x,y,e1,e2) ->
      x::(y::remove_and_uniq S.empty (fv e1 @ fv e2))
   (* closure address, integer arguments, and float arguments *)
   | CallCls(x,ys,zs) ->x :: ys@zs
   | CallDir(_,ys,zs) ->ys@zs
   | Save(x,_) ->[x]
   | Restore _ ->[]
   | ForLE(((i,a'),(j',k'),step),e1)->
      remove_and_uniq
        S.empty
        ((fv_id_or_imm j')@((fv_id_or_imm k')@((fv step)@(fv e1))))
   |Ref_Get(x)|Ref_FGet(x) ->[x]
   |Ref_Put(x,y)|Ref_FPut(x,y) ->[x;y]
   |Run_parallel(a,d,xs,ys) ->a::(d::(xs@ys))                                   
   |Next ->[]
   |Acc(x,y) ->[x;y]
                             
and fv = function
  | Ans(exp) -> fv_exp exp
  | Let((x, t), exp, e) ->
     fv_exp exp @ remove_and_uniq (S.singleton x) (fv e)
(*let fv e = remove_and_uniq S.empty (fv e)*) (*<-what this??*)

let rec concat e1 xt e2 =(*e1の結果をxtに束縛して、e2をつなげる*)
  match e1 with
  | Ans(exp) -> Let(xt, exp, e2)
  | Let(yt, exp, e1') -> Let(yt, exp, concat e1' xt e2)

let rec cons e1 e2 =(*e1はunit*)
  match e1 with
  |Ans(Nop) ->e2
  |Let(xt,exp,e) ->Let(xt,exp,cons e e2)
  |Ans(exp) ->let tmp = Id.genid "unit" in
              Let((tmp,Type.Unit),exp,e2)
let rec before_ans exp =function
  |Ans(exp2) ->let tmp =Id.genid "unit" in
               Let((tmp,Type.Unit),exp,Ans(exp2))
  |Let(xt,exp2,e) ->Let(xt,exp2,before_ans exp e)

let rec remove_exp exp = function(*expの最初の出現を削除する*)
  |Let(xt,exp2,e) ->
    if(exp2=exp) then e,true
    else
      let exp2',removed=remove_exp' exp exp2 in
      if(removed)then Let(xt,exp2',e),true
      else
        let e',removed =remove_exp exp  e in
        Let(xt,exp2,e'),removed
  |Ans(exp2) ->
    if exp=exp2 then (Ans(Nop)),true
    else
      let exp2',removed=remove_exp' exp exp2 in
      Ans(exp2'),removed
and remove_exp' exp = function
  |IfEq(i,j,e1,e2) ->
    let e1',removed1=remove_exp exp e1 in
    let e2',removed2=remove_exp exp e2 in
    (IfEq(i,j,e1',e2'),removed1||removed2)
  |IfLE(i,j,e1,e2) ->
    let e1',removed1=remove_exp exp e1 in
    let e2',removed2=remove_exp exp e2 in
    (IfLE(i,j,e1',e2'),removed1||removed2)
  |IfFZ(i,e1,e2) ->
    let e1',removed1=remove_exp exp e1 in
    let e2',removed2=remove_exp exp e2 in
    (IfFZ(i,e1',e2'),removed1||removed2)
  |IfFLE(i,j,e1,e2) ->
    let e1',removed1=remove_exp exp e1 in
    let e2',removed2=remove_exp exp e2 in
    (IfFLE(i,j,e1',e2'),removed1||removed2)
  |ForLE((a,b,step),e) ->
    let e',removed1=remove_exp exp e in
    let step',removed2=if(not removed1) then
                         remove_exp exp step 
                      else
                        step,removed1 in
    (if removed1||removed2 then
       (Format.eprintf "exp in for removed\n") else ());
    ForLE((a,b,step'),e'),(removed1||removed2)
  |exp2->(exp2,false)

let rec remove_allexp exp = function(*expの全ての出現を削除する*)
  |Let(xt,exp2,e) ->
    if(exp2=exp) then remove_allexp exp e
    else
      Let(xt,(remove_allexp' exp exp2),remove_allexp exp e)
  |Ans(exp2) ->
    if exp=exp2 then (Ans(Nop))
    else
      Ans(remove_allexp' exp exp2)
and remove_allexp' exp = function
  |IfEq(i,j,e1,e2) ->
    let e1'=remove_allexp exp e1 in
    let e2'=remove_allexp exp e2 in
    IfEq(i,j,e1',e2')
  |IfLE(i,j,e1,e2) ->
    let e1'=remove_allexp exp e1 in
    let e2'=remove_allexp exp e2 in
    IfLE(i,j,e1',e2')
  |IfFZ(i,e1,e2) ->
    let e1'=remove_allexp exp e1 in
    let e2'=remove_allexp exp e2 in
    IfFZ(i,e1',e2')
  |IfFLE(i,j,e1,e2) ->
    let e1'=remove_allexp exp e1 in
    let e2'=remove_allexp exp e2 in
    IfFLE(i,j,e1',e2')
  |ForLE((a,b,step),e) ->
    let step'=remove_allexp exp step in
    let e'=remove_allexp exp e in
    ForLE((a,b,step'),e')
  |exp2->exp2

let rec there_is_call = function
  |Ans(exp) ->there_is_call' exp
  |Let(_,exp,e) ->
    if there_is_call' exp then true
    else
      there_is_call e
and there_is_call' = function
  |Run_parallel _|CallCls _|CallDir _|ForLE _ ->true
  |IfEq(_,_,e1,e2)|IfLE(_,_,e1,e2)|IfFZ(_,e1,e2)|IfFLE(_,_,e1,e2)
   ->(there_is_call e1)||(there_is_call e2)
  |_ ->false
  



let align i = (if i mod 8 = 0 then i else i + 4)
