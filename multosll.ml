open Asm

let rec is_pow2 n =
  if n=0 then false
  else if n=1 || n= -1 then true
  else if n mod 2 <>0 then false
  else is_pow2 (n/2)

let  log2_int n =
  let rec inner n i =
    if n<=0 then assert false
    else if n=1 then i
    else inner (n/2) (i+1)
  in
  inner n 0
  
               
let rec multosll env  = function (* mul,div to sll,slr *)
  | Ans(exp) -> multosll' env exp
  | Let((x, Type.Ref t) as xt,exp,e) ->(*xがref型の時は定数でも登録しない*)
     concat (multosll' env exp) xt (multosll env e)
  | Let((x, t), Add(zero,C(i)), e) when (is_pow2 i) && (zero=reg_zero) ->
     (*Printf.printf "found! %s=%d\n" x i;*)
     let e' = multosll (M.add x i env) e in
      if List.mem x (fv e') then Let((x, t), Add(reg_zero,C(i)), e') else
      ((* Format.eprintf "erased redundant Set to %s@." x; *)
       e')
  | Let(xt, exp, e) ->concat (multosll' env exp) xt (multosll env e)
and multosll' env = function
  |Mul(x,y) when M.mem y env ->let i= M.find y env in
                               if (i>0) then
                                 Ans(SLL(x,log2_int i))
                               else
                                 Let((reg_sw,Type.Int),SLL(x,log2_int (-i)),
                                     Ans(Sub(reg_zero,V(reg_sw))))(*-reg_sw*)
  |Mul(x,y) when M.mem x env ->let i= M.find x env in
                               if (i>0) then
                                 Ans(SLL(y,log2_int i))
                               else
                                 Let((reg_sw,Type.Int),SLL(y,log2_int (-i)),
                                     Ans(Sub(reg_zero,V(reg_sw))))(*-reg_sw*)
  |Div(x,y) when M.mem y env ->let i = M.find y env in
                               if(i=2)then
                                 (*let s=Id.genid "s" in
                                 Let((s,Type.Int),SRA(x,31),
                                     Let((reg_sw,Type.Int),Add(x,V(s)),
                                         Ans(SRL(reg_sw,1))))*)
                                 Ans(SRL(x,1))
                               else
                                 Ans(Div(x,y))(*mirtだとi=2のみ*)
  | IfEq(x, y', e1, e2) -> Ans(IfEq(x, y', multosll env e1, multosll env e2))
  | IfLE(x, y', e1, e2) -> Ans(IfLE(x, y', multosll env e1, multosll env e2))
  | IfGE(x, y', e1, e2) -> Ans(IfGE(x, y', multosll env e1, multosll env e2))
  | IfFEq(x, y, e1, e2) -> Ans(IfFEq(x, y, multosll env e1, multosll env e2))
  | IfFLE(x, y, e1, e2) -> Ans(IfFLE(x, y, multosll env e1, multosll env e2))
  | ForLE(cs,e) ->Ans(ForLE(cs,multosll env e))
  |e ->Ans(e)
                               
let h { name = l; args = xs; fargs = ys; body = e; ret = t } = 
  { name = l; args = xs; fargs = ys; body = multosll M.empty e; ret = t }

let f (Prog(data, fundefs, e)) =
  Prog(data,List.map h fundefs, multosll M.empty e)
