open KNormal

type ans=
  |Acc                          (* accに当たる変数 *)

  |Arraytree_var of Id.t
  |Other

exception Not_simple

let fun_name = ref "dummy"
let fundef_env= ref M.empty


(* accumの配列は深さ1に限定 
 array_treeにはaに当たる変数のみを登録*)

(* a.(i)<-a.(i)+cの形でしかa.(i)が参照されないこと、再帰関数では参照されないことを確かめる
その上で、a.(i)を参照する箇所を展開（関数呼び出し内なら）し、accum(a,i,c)に潰す*)
let rec  g intenv (a,i) array_tree accs accadds accu_exist e =

  match e with
  |Get(a,n) ->
    let a' = Array_tree.find a array_tree in
    if(Array_tree.mem a' array_tree)then (* aはacc_parent *)
      if(M.mem n intenv)then
        let n_i=M.find n intenv in
        if(i=n_i)then
          (Unit,Acc,true)
        else
          (Get(a,n),Other,accu_exist)
      else
        raise Not_simple
    else
      (Get(a,n),Other,accu_exist)
  |Let((x,t),FAdd(y,z),e2) when S.mem y accs ->
    if S.mem z accs||M.mem z accadds then
      raise Not_simple
    else
      let (e2',ans,accu_exist')=
        g intenv (a,i) array_tree accs (M.add x z accadds) true e2 in
      (e2',ans,accu_exist')                       (* xの定義は消す *)

  |Let((x,t),FAdd(y,z),e2) when S.mem z accs ->
    if S.mem y accs||M.mem y accadds then
      raise Not_simple
    else
      let (e2',ans,accu_exist')=
        g intenv (a,i) array_tree accs (M.add x y accadds) true e2 in
      (e2',ans,accu_exist')                       (* xの定義は消す *)

  |Let((x,t),e1,e2) ->

    let (e1',ans,accu_exist') =
      g intenv (a,i) array_tree accs accadds accu_exist e1 in
    let intenv'=
      (match e1' with
         Int(i) ->M.add x i intenv|_ ->intenv)
    in
    (match ans with
     |Acc ->
       let accs'=S.add x accs in
       let (e2',ans2,exist2)=
         g intenv' (a,i) array_tree accs' accadds true e2 in
       (Let((x,Type.Unit),e1',e2'),ans2,exist2)
       
     (* |Acc_add -> *)
     (*   let (e2',ans2,exist2)=  *)
     (*     g intenv' (a,i) array_tree accs (S.add x accadds) accu_exist' e2 in *)
     (*   (Let((x,t),e1',e2'),ans2,exist2) *)
     |Arraytree_var(y) ->
       let array_tree'=Array_tree.add_env x y array_tree in
       let (e2',ans2,exist2)= 
         g intenv' (a,i) array_tree' accs accadds accu_exist' e2 in
       (Let((x,t),e1',e2'),ans2,exist2)
       
     |Other ->
       let (e2',ans2,exist2)=
       g intenv' (a,i) array_tree accs accadds accu_exist' e2 in
        (Let((x,t),e1',e2'),ans2,exist2))

  |LetTuple(xts,y,e2) ->
    let (e2',ans2,exist2)= 
      g intenv (a,i) array_tree accs accadds accu_exist e2 in
    (LetTuple(xts,y,e2'),ans2,exist2)
      

  |Let_Ref((x,t),e1,e2) ->
    
    let (e1',ans,accu_exist') =
      g intenv (a,i) array_tree accs accadds accu_exist e1 in
    
    let (e2',ans2,accu_exist2) =
      g intenv (a,i) array_tree accs accadds accu_exist' e2 in

    (Let_Ref((x,t),e1',e2'),ans2,accu_exist2)

  |LetRec(fundef,e2) ->
    let (e2',ans2,exist2)=
      g intenv (a,i) array_tree accs accadds accu_exist e2 in
    (LetRec(fundef,e2'),ans2,exist2)
    
  (* |FAdd(x,y) when S.mem x accs -> (\* int型なのでxはaccu *\) *)
  (*   if S.mem y accs||S.mem y accadds then *)
  (*     raise Not_simple *)
  (*   else *)
  (*     (Var(y),Acc_add,true)     (\* accのxは潰す *\) *)
  (* |FAdd(x,y) when S.mem y accs -> (\* int型なのでxはaccu *\) *)
  (*   if S.mem x accs||S.mem x accadds then *)
  (*     raise Not_simple *)
  (*   else *)
  (*     (Var(x),Acc_add,true)     (\* accのyは潰す *\) *)
  |Put(b,n,x) ->
    let b' = Array_tree.find b array_tree in
    if (Array_tree.mem b' array_tree)then
      if(M.mem n intenv)then
        let n_i = M.find n intenv in
        if(n_i=i)then        (* (b,n)がaccu *)
          if(M.mem x accadds)then
            (
              Format.eprintf "convert2accum:%s.(%d)@." b n_i;
            (Accum(a,n,(M.find x accadds)),Other,true))
          else
            raise Not_simple
                  
        else
          (Put(b,n,x),Other,accu_exist)
      else
        assert false            (*b要素がaccuの候補でunknownに書き込んでる *)
    else
      (Put(b,n,x),Other,accu_exist)
        
        
  |App (f,xs) ->
    if(f<> !fun_name)then
      (assert (M.mem f !fundef_env);
    let {name=_;args=yts;body=e} as fundef = M.find f !fundef_env in
      let env' =
	List.fold_left2
	  (fun env' (y, t) x -> M.add y x env')
	  M.empty
	  yts
	  xs in
      let e'= Alpha.g env' e in
      let unchanged_args_ys = For_check.search_unchanged_arg fundef in
      let unchanged_args_xs = List.map
                                (fun y ->assert (M.mem y env');M.find y env')
                                unchanged_args_ys in
      let intenv_in_f =M.filter
                         (fun x i ->List.mem x unchanged_args_xs)
                         intenv in
      let back= !fun_name in
      fun_name:=f;
      let (e',ans,accu_exist')=
        g intenv_in_f (a,i) array_tree accs accadds false e' in
      fun_name:=back;
      if(accu_exist')then
        if S.mem f (fv e) then raise Not_simple (* 再帰関数の中で足されている *)
        else
          (e',ans,accu_exist||accu_exist') (* accuの操作があるので展開 *)
      else
        (App(f,xs),ans,accu_exist)
      )
    else
      (App(f,xs),Other,accu_exist)

  |IfLE(x,y,e1,e2) ->
    let (e1',ans,accu_exist1) =
      g intenv (a,i) array_tree accs accadds accu_exist e1 in
    
    let (e2',ans2,accu_exist2) =
      g intenv (a,i) array_tree accs accadds accu_exist e2 in      
    (IfLE(x,y,e1',e2'),Other,accu_exist1||accu_exist2)
  |IfEq(x,y,e1,e2) ->
    let (e1',ans,accu_exist1) =
      g intenv (a,i) array_tree accs accadds accu_exist e1 in
    
    let (e2',ans2,accu_exist2) =
      g intenv (a,i) array_tree accs accadds accu_exist e2 in      
    (IfEq(x,y,e1',e2'),Other,accu_exist1||accu_exist2)

  |ForLE(cs,e1) ->
    let (e1',ans,accu_exist1) =
      g intenv (a,i) array_tree accs accadds accu_exist e1 in
    if(accu_exist1)then
      raise Not_simple
    else
      assert(e1=e1');
    (ForLE(cs,e1'),Other,accu_exist)
  
  |Var(y) when Array_tree.mem y array_tree ->
    (Var(y),Arraytree_var(y),accu_exist)
  |e ->
    if (S.exists
         (fun x ->(S.mem x accs)||(M.mem x accadds))
         (fv e))
    then
      raise Not_simple
            (* acumulate以外の操作に(a,i)が使われている *)
    else 
      (e,Other,accu_exist)
         
let f constenv fundef_env' accum_path_list e =
  let intenv = M.map (fun x ->match x with Int(i) ->i|_ ->assert false)
                     (M.filter (fun x e ->match e with Int _ ->true|_ ->false)
                               constenv)
  in
  fundef_env:=fundef_env';
  List.fold_left
    (fun (e',accum') (a,poslist) ->
           match poslist with
             [i] ->
             (* Format.eprintf "accum%s.(%d)@." a i; *)
             let array_tree=Array_tree.set_root [a] Array_tree.empty in
             let (e',_,accu_exist)=
               g intenv (a,i) array_tree S.empty M.empty false e' in
             assert accu_exist;
      (e',[(a,i)]::accum')
      |_ ->raise Not_simple)
    (e,[])
    accum_path_list
        
      
      

        
      
       
      
