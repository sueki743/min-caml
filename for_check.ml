open KNormal



(*

*for分の変換

ForLE(((i,a),(j,k),step),e)構文をknormal.tに加えた
for(i=a;j<=k;step){
       e
  }
の意味(j,kのどちらかはi)
上のi=aで、aはiの実際の初期値と同じ値となるので実際にここで初期化され直すことはない
（プログラムにとっては今の所ただの飾りになってる）

再帰関数で

末尾が
if(i<j)
 e1
else
 e2

となっているものに着目する.
・iがjが帰納的変数で、もう片方が再帰で不動の変数
・e1かe2が末尾再帰になっている

->for分に変換


*再代入可能変数

再代入可能変数を表す為に、ref型を新たにtypeに加え
Ref_Get,Ref_Put,Let_Ref構文をknormal.tに加えた
ref型変数は、1要素配列と同等だが、レジスタに割り当てられる



*)

exception CANNOT_CONVERT;;
  
     
let rec cons defs1 defs2 =
  match defs1 with
  |Let(xt,e1,e2) ->Let(xt,e1,cons e2 defs2)
  |LetRec(fundef,e2)->LetRec(fundef,cons e2 defs2)
  |LetTuple(xs,y,e2) ->LetTuple(xs,y,cons e2 defs2)
  |Let_Ref(xt,e1,e2) ->Let_Ref(xt,e1,cons e2 defs2)
  |Unit ->defs2
  |e ->let dummy =Id.genid "unit" in
       Let((dummy,Type.Unit),e,defs2)
       
let serch_unchanged_arg {name = (x,t);args = yts;body=e}=(*末尾呼び出しで不変な引数*)
  let ys = List.map fst yts in
  let rec  unchanged_arg =function
    |IfEq(_,_,e1,e2)|IfLE(_,_,e1,e2) ->List.filter
                      (fun arg ->List.mem arg (unchanged_arg e1))
                      (unchanged_arg e2)
    |Let(_,_,e1)|LetTuple(_,_,e1)|LetRec(_,e1)->unchanged_arg e1
    |App(f,arglist) when f=x ->(*再帰呼び出し*)
      List.fold_left2(*arglistのうちysと一致するもの返す*)
        (fun unchanged arg arg' ->if(arg=arg') then arg::unchanged
                                    else unchanged)
        []
        ys
        arglist
    |_ ->ys
  in
  unchanged_arg e
      
let search_unchanged_var unchanged_args {name = (x,_);args = yts;body=e} =
  let rec search unchanged_vars= function

    |Let((a,t),e1,e2)->
      (match e1 with
      |Unit|Int _|Float _->
        let (unchanged_vars2,defs2)=search (a::unchanged_vars) e2 in
        (unchanged_vars2,Let((a,t),e1,defs2))
      |Neg(b)|FNeg(b)|Var(b)|Ftoi(b)|Itof(b)|FAbs(b)|FSqrt(b)
           when List.mem b unchanged_args ->
        let (unchanged_vars2,defs2)=search (a::unchanged_vars) e2 in
        (unchanged_vars2,Let((a,t),e1,defs2))
      |Add(b,c)|Sub(b,c)|Mul(b,c)|Div(b,c)|FAdd(b,c)|FSub(b,c)|FMul(b,c)|FDiv(b,c)
           when (List.mem b unchanged_args)&&(List.mem c unchanged_args)->
        let (unchanged_vars2,defs2)=search (a::unchanged_vars) e2 in
        (unchanged_vars2,Let((a,t),e1,defs2))
      |Tuple bs when List.for_all (fun b ->(List.mem b unchanged_args)) bs ->
        let (unchanged_vars2,defs2)=search (a::unchanged_vars) e2 in
        (unchanged_vars2,Let((a,t),e1,defs2))
      |_ ->
        search unchanged_vars e2)

    |LetTuple(ats,b,e2) when List.mem b unchanged_vars ->
      let a_list = List.map fst ats in
      let (unchanged_vars2,defs2)=search (a_list@unchanged_vars) e2 in
      (unchanged_vars2,LetTuple(ats,b,defs2))
    |LetTuple(ats,b,e2) ->search unchanged_vars e2
    |LetRec({name =(a,_);args = ats;body =e1} as fundef,e2)->
      let a_s = List.map fst ats in
      if S.for_all (fun b ->(List.mem b unchanged_args)||(List.mem b a_s))
                      (fv e1 )
      then
        let (unchanged_vars2,defs2)=search (a::unchanged_vars) e2 in
        (unchanged_vars2,LetRec(fundef,defs2))
      else
        search unchanged_vars e2
    |IfEq(_,_,e1,e2)|IfLE(_,_,e1,e2) ->
      let (vars1,defs1)=search unchanged_vars e1 in
      let (vars2,defs2)=search unchanged_vars e2 in
      (vars1@vars2,cons defs1 defs2)

    |Let_Ref(xt,e1,e2) ->search unchanged_vars e2

    |_ ->(unchanged_vars,Unit)
  in
  search unchanged_args e

let rec list_where i list =
  match list with
  |e::es when e=i ->0
  |e::es ->1 + (list_where i es)
  |[] ->raise Not_found

          
let rec search_def j =function (*変数jの定義を探してくる*)
  |Let((a,t),e1,e2) when a=j ->
    e1
  |Let(_,e1,e2)|IfEq(_,_,e1,e2)|IfLE(_,_,e1,e2) ->
    (try search_def j e1 with Not_found ->search_def j e2)
  |LetRec({name = (a,_);args =_;body=_} as fundef,e2)->
    if a=j then LetRec(fundef,Unit) else
      search_def j e2
  |LetTuple(xts,y,e2) ->
    if(List.mem j (List.map fst xts)) then
      LetTuple(xts,y,Unit)
    else
      search_def j e2
  |Let_Ref((a,t),e1,e2) when a=j ->
    Let_Ref((a,t),e1,Unit)
  |Let_Ref(xt,e1,e2) ->search_def j e2
  |_ ->raise Not_found
                                 

let rec is_same i j e=(*変数i,jがeに置いて等しいか確認*)
  if (i=j) then true(*α変換後*)
  else
    if (not (S.mem i (fv e)))&&(not (S.mem j (fv e))) then(*i,jがeで定義されている*)
      match(search_def i e,search_def j e)with
      |Var(a),Var(b) -> is_same a b e
      |Var(i'),_ ->is_same i' j e
      |_,Var(j') ->is_same i j' e
      |Int(a),Int(b) ->a=b
      |Float(a),Float(b) ->a=b
      |Unit,Unit ->true
      |Add(a,b),Add(c,d)|Sub(a,b),Sub(c,d)|Mul(a,b),Mul(c,d)|Div(a,b),Div(c,d)|FAdd(a,b),FAdd(c,d)|FSub(a,b),FSub(c,d)|FMul(a,b),FMul(c,d)|FDiv(a,b),FDiv(c,d)
       ->
        ((is_same a c e)&&(is_same b d e))||((is_same a d e)&&(is_same b c e))
      |Neg(a),Neg(b)|FNeg(a),FNeg(b)|Ftoi(a),Itof(b)|FAbs(a),FAbs(b)|FSqrt(a),FSqrt(b) ->is_same a b e
      |LetRec({name =(a,_);args=a_yts;body=a_e1},a_unit),
       LetRec({name =(b,_);args=b_yts;body=b_e1},b_unit) ->
        if a<>i||b<>j then assert false
        else
          (a_yts=b_yts&&a_e1=b_e1)
      |Let_Ref((a,_),a_e1,a_unit),Let_Ref((b,_),b_e1,b_unit) ->
        if a<>i||b<>j then assert false
        else
          (a_e1=b_e1)
              
      |_,_ ->false
    else if (not (S.mem i (fv e)))&&(S.mem j (fv e)) then(*jが自由変数*)
      match search_def i e with
      |Var(a) ->is_same a j e
      |_ ->false
    else if (S.mem i (fv e))&&(not (S.mem j (fv e))) then(*iが自由変数*)
      match search_def j e with
      |Var(a) -> is_same i a e
      |_ ->false
    else(*iもjも自由変数*)
      false(*この時点でi=jでないので*)
        
let next_arg i {name=(x,t);args=yts;body=e} =
  (*末尾再帰呼び出しで引数iに当たる,変数の定義を取ってくる*)

  let n = list_where i (List.map fst yts) in
  
  let rec next_id = function(*xの末尾再帰呼び出しでのn番目の変数を集める*)
    |IfEq(_,_,e1,e2)|IfLE(_,_,e1,e2) ->
      let list1=next_id e1 in
      let list2=next_id e2 in
      list1@(List.filter (fun x ->not (List.mem x list1)) list2)
    |Let(_,_,e2)|LetRec(_,e2)|Let_Ref(_,_,e2) ->
      next_id e2
    |LetTuple(_,_,e2) ->
      next_id e2
    |App(f,a_s) when f=x ->
      [ List.nth a_s n ]
    |_ ->[]
  in
  let nth_args = next_id e in

  if(List.for_all
       (fun def ->is_same def (List.nth nth_args 0) e)
       nth_args
    )
  then(*全要素が同一なら*)
    search_def (List.nth nth_args 0) e
  else
    raise CANNOT_CONVERT
    

let search_tail e =
  (*eを末尾の式,それ以前に分解*)
  let rec inner = function
    |Let(xt,e1,e2) ->
      let (e3,tail)=inner e2 in
      (Let(xt,e1,e3),tail)
    |LetRec(fundef,e2) ->
      let (e3,tail) =inner e2 in
      (LetRec(fundef,e3),tail)
    |LetTuple(xts,y,e2) ->
      let (e3,tail) = inner e2 in
      (LetTuple(xts,y,e3),tail)
    |Let_Ref(xt,e1,e2) ->
      let (e3,tail) = inner e2 in
      (Let_Ref(xt,e1,e3),tail)
    |e ->(Unit,e)
  in
  inner e


let rec tailrec_to_put args ref_env f e =(*末尾再帰をputに変換*)
  let argN_ref = List.map
                   (fun ((arg,_),ref_arg) ->((list_where arg args),ref_arg))
                   ref_env
  in
  let rec inner e =
    match search_tail e with
    |pre_exp,e ->
      (match e with
       |IfEq(i,j,e1,e2)->
       cons pre_exp (IfEq(i,j,(inner e1),(inner e2)) )
       |IfLE(i,j,e1,e2)->
       cons pre_exp (IfLE(i,j,(inner e1),(inner e2)))
       |Let((x,t),e1,e2) ->
         cons pre_exp (Let((x,t),e1,(inner e2)))
       |LetRec(fundef,e2) ->
         cons pre_exp (LetRec(fundef,(inner e2)))
       |LetTuple(xts,y,e2) ->
         cons pre_exp (LetTuple(xts,y,(inner e2)))
       |Let_Ref(xt,e1,e2) ->
         cons pre_exp (Let_Ref(xt,e1,(inner e2)))
       |App(f',arg_list) when f' = f ->
         let put_exp =
           List.fold_left
             (fun put_exp (argN,ref_argN)->
               let argN_v = List.nth arg_list argN in
               let dummy = Id.genid "unit" in
               Let((dummy,Type.Unit),Ref_Put(ref_argN,argN_v),put_exp))
             Unit
             argN_ref
         in
         cons pre_exp put_exp
       |e' ->cons pre_exp e')
  in
  inner e
      
       
let to_refGet refenv e =
  let(substs,get_exp) = List.fold_left
                          (fun (substs,get_exp) ((x,t),ref_x) ->
                            let x' = Id.genid x in
                            (M.add x x' substs,Let((x',t),Ref_Get(ref_x),get_exp)))
                          (M.empty,Unit)
                          (List.filter (fun ((x,_),_) -> (S.mem x (fv e))) refenv)
  in
  cons get_exp (Alpha.subst substs e)

let rec  rm_def vars =function
  |Let((x,_),e1,e2) when List.mem x vars ->
    rm_def vars e2
  |Let_Ref((x,_),e1,e2) when List.mem x vars ->
    rm_def vars e2
  |LetRec({name=(x,_);args=_;body=_},e2) when List.mem x vars ->
    rm_def vars e2
  |LetTuple(xts,y,e2) when List.for_all
                             (fun x ->List.mem x vars)
                             (List.map fst xts) ->
    rm_def vars e2
  |Let(xt,e1,e2) ->Let(xt,e1,rm_def vars e2)
  |Let_Ref(xt,e1,e2) ->Let_Ref(xt,e1,rm_def vars e2)
  |LetRec(fundef,e2) ->LetRec(fundef,rm_def vars e2)
  |LetTuple(xts,y,e2) ->LetTuple(xts,y,rm_def vars e2)
  |IfEq(i,j,e1,e2) ->IfEq(i,j,rm_def vars e1,rm_def vars e2)
  |IfLE(i,j,e1,e2) ->IfLE(i,j,rm_def vars e1,rm_def vars e2)
  |e ->e                 
           
let rec is_tailrec f = function
  |Let(_,_,e2)|LetRec(_,e2)|LetTuple(_,_,e2)|Let_Ref(_,_,e2) ->is_tailrec f e2
  |IfEq(_,_,e1,e2)|IfLE(_,_,e1,e2) ->(is_tailrec f e1)&&(is_tailrec f e2)
  |App(x,_) when x=f ->true
  |_ ->false
     
         
let for_check  ({name = (x,t);args = yts;body=e} as fundef) =(*for分に変換できれば変換する*)
  try
    let ys = List.map fst yts in
    let unchanged_args =serch_unchanged_arg fundef in(*再帰で値が変わらない引数*)
    let (unchanged_vars,unchanged_defs) = search_unchanged_var unchanged_args fundef in
    let e'= rm_def unchanged_vars e in
    (*再帰を通して値が変わらない変数と、その定義*)
    (match search_tail e' with(*(末尾以外,末尾の式)を返す*)
       
     | pre_exp,(IfLE(i,j,
                     e1,
                     e2))->
        
        
        let rec convert2for index_var step e_continue e_return =
          let ref_index = Id.genid "index_var" in(*ref_ == 再代入可能変数,まず帰納的変数の再代入可能変数を用意*)
          let changed_arg_t = List.filter (fun (x,_)->not (List.mem x unchanged_args))
                                                   
                                          yts
          in
          (assert (List.mem_assoc index_var changed_arg_t));
          let (ref_defs,refenv)=List.fold_left
                                  (fun (defs,env) (x,t)->
                                    if x<> index_var then
                                      let ref_x = Id.genid x in
                                      (Let_Ref((ref_x,Type.Ref t),Var(x),defs),(((x,t),ref_x)::env))
                                    else
                                      (Let_Ref((ref_index,Type.Ref (Type.Int)),Var(x),defs),((index_var,t),ref_index)::env))
                                  (Unit,[])
                                  changed_arg_t in
          
          let inside_for_exp=cons pre_exp e_continue in
          let inside_for_exp' = tailrec_to_put ys (List.remove_assoc (index_var,Type.Int) refenv)  x inside_for_exp in
          let inside_for_exp'' = to_refGet refenv inside_for_exp' in
          assert(not (S.mem index_var (fv inside_for_exp'')));
          let outside_for_exp = cons pre_exp e_return in
          let outside_for_exp' = to_refGet refenv outside_for_exp in
          assert(not (S.mem index_var (fv outside_for_exp')));
          let step' = to_refGet refenv step in
          let for_exp =
            if(i=index_var&&e1=e_continue) then
              ForLE(((ref_index,i) ,(ref_index,j), step'),
                     inside_for_exp'')
                 
            else if(i=index_var&&e2=e_continue) then
              let j'= Id.genid j in
              let one = Id.genid "one" in
              Let((one,Type.Int),Int(1),
                  Let((j',Type.Int),Add(j,one),
                      ForLE(((ref_index,i),(j',ref_index),step'),
                            inside_for_exp'')))
            else if (j = index_var&&e1=e_continue) then
              ForLE(((ref_index,j) ,(i,ref_index), step'),
                    inside_for_exp'')
                                              
            else if (j = index_var&&e2=e_continue) then
              let i'= Id.genid i in
              let one = Id.genid "one" in
              Let((one,Type.Int),Int(1),
                  Let((i',Type.Int),Sub(i,one),
                      ForLE(((ref_index,j),(ref_index,i'),step'),
                            inside_for_exp'')))
              
            else(*index_var=i or j && e_continue= e1 or e2*)
              assert false
          in
          let new_e=
            cons (cons ref_defs
                       unchanged_defs)
                 (rm_def unchanged_vars
                         (cons for_exp
                               outside_for_exp'))
          in
           {name = (x,t);args = yts;body=new_e}
          
                                   
        in
        
        
        (if(List.mem i ys)&&(List.mem j unchanged_vars) then(*iが引数,jが再帰で不変*)
          if is_tailrec x e2 then(*e2で必ず末尾再帰*)
            (match next_arg i fundef with(*再帰呼び出しでの、iに当たる引数*)
             |Add(i',d) when  is_same i' i e&&List.mem d unchanged_vars ->
               convert2for i (Add(i,d)) e2 e1 
             |Add(d,i') when  is_same i' i e&&List.mem d unchanged_vars ->
               convert2for i (Add(i,d)) e2 e1
            |Sub(i',d) when  is_same i' i e && List.mem d unchanged_vars ->
              convert2for i (Sub(i,d)) e2 e1
            |e ->raise CANNOT_CONVERT)
         else if is_tailrec x e1 then
           (match next_arg i fundef with(*再帰呼び出しでの、iに当たる引数*)
            |Add(i',d) when  is_same i' i e&&List.mem d unchanged_vars ->
              convert2for i (Add(i,d)) e1 e2
            |Add(d,i') when  is_same i' i e&&List.mem d unchanged_vars ->
              convert2for i (Add(i,d)) e1 e2
            |Sub(i',d) when  is_same i' i e && List.mem d unchanged_vars ->
              convert2for i (Sub(i,d)) e1 e2
            |e ->raise CANNOT_CONVERT)
         else
           raise CANNOT_CONVERT
                         
       else if(List.mem i unchanged_vars)&&(List.mem j ys) then(*iが再帰不変,jが引数*)
         (if is_tailrec x e2 then
           (match next_arg j fundef with(*再帰呼び出しでの、jに当たる引数*)
            |Add(j',d) when is_same j' j e&&List.mem d unchanged_vars ->
              convert2for j (Add(j,d)) e2 e1
            |Add(d,j') when is_same j' j e&&List.mem d unchanged_vars ->
              convert2for j (Add(j,d)) e2 e1
            |Sub(j',d) when is_same j' j e&& List.mem d unchanged_vars ->
              (Printf.printf "index:%s\tstep:-%s" j d;convert2for j (Sub(j,d)) e2 e1)
            |e ->raise CANNOT_CONVERT)
         else if is_tailrec x e1 then
           (match next_arg j fundef with(*再帰呼び出しでの、jに当たる引数*)
            |Add(j',d) when is_same j' j e&&List.mem d unchanged_vars ->
              convert2for j (Add(j,d)) e1 e2
            |Add(d,j') when is_same j' j e&&List.mem d unchanged_vars ->
              convert2for j (Add(j,d)) e1 e2
            |Sub(j',d) when is_same j' j e&& List.mem d unchanged_vars ->
              convert2for j (Sub(j,d)) e1 e2
            |e ->raise CANNOT_CONVERT)
         else
           raise CANNOT_CONVERT)
       else 
        raise CANNOT_CONVERT)
    

                         
     |_ -> raise CANNOT_CONVERT)
     with
    CANNOT_CONVERT ->raise CANNOT_CONVERT
    
let rec f = function
  |LetRec({name=(x,t);args=yts;body=e1},e2) ->
    let fundef = {name=(x,t);args=yts;body=f e1} in
    let fundef' =
      (try let a=for_check fundef in (Format.eprintf "convert function to forloop -> %s@." x;a) with
         CANNOT_CONVERT ->fundef) in
    LetRec(fundef',f e2)
  |Let(xt,e1,e2) ->Let(xt,f e1,f e2)
  |LetTuple(xts,y,e2) ->LetTuple(xts,y,f e2)
  |Let_Ref(xt,e1,e2) ->Let_Ref(xt,f e1,f e2)
  |IfEq(x,y,e1,e2) ->IfEq(x,y,f e1,f e2)
  |IfLE(x,y,e1,e2) ->IfLE(x,y,f e1,f e2)
  |e ->e



                           


    
