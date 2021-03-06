
type id_or_imm = V of Id.t | C of int
val to_id_imm:Id.vc ->id_or_imm
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
   | Lwi of int*Id.l
   | FLw of  int * Id.t
   | FLwi of int*Id.l
   | Sw of Id.t *int * Id.t 
   | Swi of Id.t *int* Id.l
   | FSw of Id.t * int * Id.t
   | FSwi of Id.t *int* Id.l

   |La of Id.l
                      
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
               pbody : t 
              }
                 
                 
type fundef = { name : Id.l; args : Id.t list; fargs : Id.t list; body : t; ret : Type.t }
(* プログラム全体 = 浮動小数点数テーブル + トップレベル関数 + メインの式 (caml2html: sparcasm_prog) *)
type prog = Prog of (Id.l * float) list * fundef list *parallel option*t

val fletd : Id.t * exp * t -> t (* shorthand of Let for float *)
val seq : exp * t -> t (* shorthand of Let for unit *)

val regs : Id.t array
val fregs : Id.t array
val allregs : Id.t list
val allfregs : Id.t list
                    
val acc1 :Id.t
val acc2 :Id.t
val acc3 :Id.t
val allaccs:Id.t list
val reg_cl : Id.t
val reg_sw : Id.t
val reg_fsw : Id.t
val reg_hp : Id.t
val reg_sp : Id.t
val is_reg : Id.t -> bool
(*val co_freg : Id.t -> Id.t*)
val fv_exp : exp ->S.elt list
val fv : t -> Id.t list
val concat : t -> Id.t * Type.t -> t -> t
val cons :t ->t->t
val before_ans:exp ->t ->t
val align : int -> int
val remove_exp:exp ->t ->t*bool
val remove_allexp:exp ->t->t
val there_is_call : t->bool
val fv_before_call : t -> Id.t list
val remove_and_uniq : S.t ->S.elt list ->S.elt list
