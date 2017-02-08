open KNormal

type ans=
  |Child of int
  |Acc                          (* accに当たる変数 *)
  |Acc_add                      (* accにaddした変数 *)
  |Other

exception Not_simple

let fun_name = ref "dummy"
let fundef_env= ref M.empty
let accu_vars = ref []
                   
let rec  g intenv (a,poslist) a_children accu_add accu_exist e =
  let whole_depth = List.length poslist in
  let is_accu x=try let depth=M.find x a_children in
                    depth=whole_depth
                with Not_found ->false
  in
  match e with
  |Get(a,n) ->
    if(M.mem n intenv&&M.mem a a_children)then
      let n_i = M.find n intenv in
      let depth = M.find a a_children in(*depth=0 <->a*)
      let n'_i = List.nth poslist depth in
      if(n'_i=n_i)then          (* depth+1のaの子に当たる *)
        if(depth+1)=whole_depth then (* accに当たる->get文消去 *)
          (accu_vars:=(a,n_i)::(!accu_vars);
          (Unit,Acc,true))
        else
          (Get(a,n),Child (depth+1),accu_exist)
      else
        (Get(a,n),Other,accu_exist)
    else
      (Get(a,n),Other,accu_exist)

  |Let((x,t),e1,e2) ->

    let (e1',ans,accu_exist') =
      g intenv (a,poslist) a_children accu_add accu_exist e1 in
    let intenv'=
      (match e1' with
         Int(i) ->M.add x i intenv|_ ->intenv)
    in
    (match ans with
     |Acc ->
       let a_children' = M.add x whole_depth a_children in
       let (e2',ans2,exist2)=
         g intenv' (a,poslist) a_children' accu_add true e2 in
       (Let((x,Type.Unit),e1',e2'),ans2,exist2)
       
     |Child depth ->
       let a_children' = M.add x depth a_children in
       let (e2',ans2,exist2)=
         g intenv' (a,poslist) a_children' accu_add accu_exist' e2 in
       (Let((x,t),e1',e2'),ans2,exist2)
     |Acc_add ->
       let (e2',ans2,exist2)= 
         g intenv' (a,poslist) a_children (x::accu_add) accu_exist' e2 in
       (Let((x,t),e1',e2'),ans2,exist2)
     |Other ->
       g intenv' (a,poslist) a_children accu_add accu_exist' e2)

  |LetTuple(xts,y,e2) ->
    if(M.mem y a_children)then
      let depth = M.find y a_children in
      let pos_i = List.nth poslist depth in
      let xs = List.map fst xts in
      let a_children' = M.add (List.nth xs pos_i) (depth+1) a_children in
      let (e2',ans2,exist2)= 
        g intenv (a,poslist) a_children' accu_add accu_exist e2 in
      (LetTuple(xts,y,e2'),ans2,exist2)
    else
      let (e2',ans2,exist2)= 
        g intenv (a,poslist) a_children accu_add accu_exist e2 in
      (LetTuple(xts,y,e2'),ans2,exist2)
      

  |Let_Ref((x,t),e1,e2) ->
    
    let (e1',ans,accu_exist') =
      g intenv (a,poslist) a_children accu_add accu_exist e1 in
    
    let (e2',ans2,accu_exist2) =
      g intenv (a,poslist) a_children accu_add accu_exist e2 in

    (Let_Ref((x,t),e1',e2'),ans2,accu_exist2)

  |LetRec(fundef,e2) ->
    let (e2',ans2,exist2)= 
      g intenv (a,poslist) a_children accu_add accu_exist e2 in
    (LetRec(fundef,e2'),ans2,exist2)
    
  |FAdd(x,y) when M.mem x a_children -> (* int型なのでxはaccu *)
    if M.mem y a_children||List.mem y accu_add then
      raise Not_simple
    else
      (Var(y),Acc_add,true)     (* accのxは潰す *)
  |FAdd(x,y) when M.mem y a_children -> (* int型なのでxはaccu *)
    if M.mem x a_children||List.mem x accu_add then
      raise Not_simple
    else
      (Var(x),Acc_add,true)     (* accのyは潰す *)
  |Put(b,n,x) when M.mem b a_children->
    
    let depth = M.find b a_children in
    if(M.find b a_children)=(whole_depth-1)then
      if(M.mem n intenv)then
        let n_i = M.find n intenv in
        let n'_i = List.nth poslist depth in
        if(n_i=n'_i)then        (* (b,n)がaccu *)

          if(List.mem x accu_add)then
            (Accum(b,n,x),Other,true)
          else
            raise Not_simple
                  
        else
          (Put(b,n,x),Other,accu_exist)
      else
        assert false            (*b要素がaccuの候補でunknownに書き込んでる *)
    else
      (Put(b,n,x),Other,accu_exist)

  |Put(b,n,x) ->
    if(is_accu x)||(List.mem x accu_add) then
      raise Not_simple          (* accuが他のところで使われている *)
    else
      (Put(b,n,x),Other,accu_exist)
        
  |App (f,xs) ->
    if(f<> !fun_name)then
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
        g intenv_in_f (a,poslist) a_children accu_add false e' in
      fun_name:=back;
      if(accu_exist')then
        if S.mem f (fv e) then raise Not_simple (* 再帰関数の中で足されている *)
        else
          (e',ans,accu_exist||accu_exist') (* accuの操作があるので展開 *)
      else
        (App(f,xs),ans,accu_exist)

    else
      (App(f,xs),Other,accu_exist)

  |IfLE(i,j,e1,e2) ->
    let (e1',ans,accu_exist1) =
      g intenv (a,poslist) a_children accu_add accu_exist e1 in
    
    let (e2',ans2,accu_exist2) =
      g intenv (a,poslist) a_children accu_add accu_exist e2 in

    (IfLE(i,j,e1',e2'),Other,accu_exist1||accu_exist2)
  |IfEq(i,j,e1,e2) ->
    let (e1',ans,accu_exist1) =
      g intenv (a,poslist) a_children accu_add accu_exist e1 in
    
    let (e2',ans2,accu_exist2) =
      g intenv (a,poslist) a_children accu_add accu_exist e2 in

    (IfEq(i,j,e1',e2'),Other,accu_exist1||accu_exist2 )
  |ForLE(cs,e1) ->
    let (e1',ans,accu_exist1) =
      g intenv (a,poslist) a_children accu_add accu_exist e1 in
    if(accu_exist1)then
      raise Not_simple
    else
      assert(e1=e1');
    (ForLE(cs,e1'),Other,accu_exist)
  

  |e ->
    if (S.exists
         (fun x ->(is_accu x)||(List.mem x accu_add))
         (fv e))
    then
      raise Not_simple
    else
      (e,Other,false)
         
let f constenv accum_path_list e =
  let intenv = M.map (fun x ->match x with Int(i) ->i|_ ->assert false)
                     (M.filter (fun x e ->match e with Int _ ->true|_ ->false)
                               constenv)
  in
  List.fold_left
    (fun (e',accum') (a,poslist) ->
      accu_vars :=[];
      let (e',_,accu_exist)=g intenv (a,poslist) (M.singleton a 0) [] false e' in
      assert accu_exist;
      (e',(!accu_vars)::accum'))
    (e,[])
    accum_path_list
        
      
      

        
      
       
      
