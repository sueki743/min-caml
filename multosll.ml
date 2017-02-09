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
  | Let((x, t), Movi(i), e) when (is_pow2 i) ->
     (*Printf.printf "found! %s=%d\n" x i;*)
     let e' = multosll (M.add x i env) e in
      if List.mem x (fv e') then Let((x, t),Movi(i), e') else
      ((* Format.eprintf "erased redundant Set to %s@." x; *)
       e')
  | Let(xt, exp, e) ->concat (multosll' env exp) xt (multosll env e)
and multosll' env = function
  |Mul(x,y) when M.mem y env ->let i= M.find y env in
                               if (i>0) then
                                 Ans(SLL(x,log2_int i))
                               else
                                 Ans(Mul(x,y))
  |Mul(x,y) when M.mem x env ->let i= M.find x env in
                               if (i>0) then
                                 Ans(SLL(y,log2_int i))
                               else
                                 Ans(Mul(x,y))
  |Div(x,y) when M.mem y env ->let i = M.find y env in
                               if(i=2)then
                                 Ans(SRL(x,1))
                               else
                                 Ans(Div(x,y))(*mirtだとi=2のみ*)
  | IfEq(x, y', e1, e2) -> Ans(IfEq(x, y', multosll env e1, multosll env e2))
  | IfLE(x, y', e1, e2) -> Ans(IfLE(x, y', multosll env e1, multosll env e2))
  | IfFZ(x, e1, e2) -> Ans(IfFZ(x, multosll env e1, multosll env e2))
  | IfFLE(x, y, e1, e2) -> Ans(IfFLE(x, y, multosll env e1, multosll env e2))
  | ForLE(cs,e) ->Ans(ForLE(cs,multosll env e))
  |e ->Ans(e)
                               
let h { name = l; args = xs; fargs = ys; body = e; ret = t } = 
  { name = l; args = xs; fargs = ys; body = multosll M.empty e; ret = t }

let i =function
  |Some {pargs=xs;
         pfargs=ys;
         index=(i,(j',k'));
         pbody=e
        } ->
    Some {pargs=xs;
          pfargs=ys;
          index=(i,(j',k'));
          pbody=multosll M.empty e}

  |None ->None


let f (Prog(data, fundefs,parallel, e)) =
  Prog(data,List.map h fundefs, i parallel,multosll M.empty e)
