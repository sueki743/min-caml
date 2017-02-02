
type node = (((Id.t*VarCatego.elm_pos) list)*((VarCatego.elm_pos*Id.t) list)) 
(*(親,子)要素の情報を各nodeが持つ*)

type t = {body:node M.t ; roots : Id.t list ; eq_env:Id.t M.t}

exception Not_preserve of Id.t*Id.t
exception Not_exist of Id.t

let empty = {body=M.empty; roots=[];eq_env=M.empty}
let find a {body=_;roots=_;eq_env=env} =
  try M.find a env with Not_found ->a

let mem a {body=tree;roots=_;eq_env=env}=M.mem a tree

let size {body=tree;roots=_;eq_env=env}=
  M.fold
    (fun a (parents,children) size' ->
      size'+1+(List.length parents)+(List.length children))
    tree
    0
let num {body=tree;roots=_;eq_env=env} =M.cardinal tree
let env_num  {body=tree;roots=_;eq_env=env} =M.cardinal env
(*rootのリストを足す*)
let set_root l ({body=tree_map; roots= list ; eq_env=env} as array_tree)=
  let l=List.filter (fun x ->not (mem x array_tree)) l in
  let l_nodes = List.map (fun x ->(x,([],[]))) l in(*親も子もないnode*)
  let tree_map'=M.add_list l_nodes tree_map in
  let list'=l@list in(*rootを足す*)
  {body=tree_map' ; roots= list' ;eq_env=env}


let put (a,pos,x) {body=tree;roots=list ; eq_env=env} =
  if(M.mem x tree)then
    raise (Not_preserve(a,x))(*minrtではとりあえずこれで良い*)
  else
    {body=tree;roots=list ; eq_env=env}
(*aがarray_treeにない,posに当たる子供がいない場合はnot_found*)
let find_child (a,pos)  {body=tree_map ; roots=list ; eq_env=env} =
    
    let (_,a_children) = M.find a tree_map in
    let (_,child)=List.find (fun (pos',_) ->pos=pos') a_children in
    child
      
let add_new_child x (a,pos) {body=tree_map ; roots=list ; eq_env=env} =
  let (a_parent,a_children) = M.find a tree_map in
  let tree_map'=M.add a (a_parent,(pos,x)::a_children)
                      (M.add x ([a,pos],[]) tree_map)
  in
  {body=tree_map' ; roots=list ; eq_env=env }

let add_env x y {body=tree_map; roots=list ; eq_env=env} =
  {body=tree_map; roots=list ; eq_env=M.add x y env}

  
let add_childe x (a,pos) ({body=tree_map ; roots=list ; eq_env=env} as array_tree) =
  if(not (M.mem a tree_map)) then
    raise (Not_exist(a))
  else
    let (_,a_children)=M.find a tree_map in
    if(M.mem x tree_map) then(*元々tree_mapにxがあった.*)
      (assert(List.exists (fun (pos',x')->x=x') a_children);
       array_tree)
    else
      try
        let y=find_child (a,pos) array_tree in(*aのposにある要素*)
        (*xとyは同じ領域を表してる,envに情報を足す*)
        {body=tree_map ; roots=list ; eq_env=M.add x y env }
      with
        Not_found ->(*a,posに変数は登録されていなかった*)
        add_new_child x (a,pos) array_tree

(*新しい親を作成*)
let add_parent x pos_childs {body=tree_map;roots=rts; eq_env=env} =
  let tree_map'=
    List.fold_left
      (fun tree_map' (pos,a) ->
        if(not (M.mem a tree_map')) then
          raise (Not_exist(a))
        else
        let (a_parent,a_children)=M.find a tree_map' in
        M.add a (((x,pos)::a_parent),a_children) tree_map')
      tree_map
      pos_childs
  in
  let tree_map' = M.add x ([],pos_childs) tree_map' in
  let x_children = List.map (fun (pos,a) ->a) pos_childs in
  let rts' = List.filter (fun a ->not (List.mem a x_children)) (x::rts) in
  {body=tree_map';roots=rts';eq_env=env}

(*xからparent枝を生やす　*)
let add_parent_edge x (a,pos)  {body=tree_map;roots=rts; eq_env=env} =
  assert (M.mem x tree_map && M.mem a tree_map);
  let (x_parent,x_children)=M.find x tree_map in
  let (a_parent,a_children)=M.find a tree_map in
  let tree_map'=M.add x ((a,pos)::x_parent,x_children) tree_map in
  let tree_map'=M.add a (a_parent,(pos,x)::a_children) tree_map' in
  let rts' = List.filter (fun x' ->x<>x') rts in
  {body=tree_map';roots=rts'; eq_env=env}
    
(*tree_mapのa以下の全要素を,深さ優先でarray_treeに足しこむ*)
(*let rec add_childe_rec array_tree (tree_map,a) =
  let (_,a_children) = M.find a tree_map in
  List.fold_left
    (fun array_tree' (pos,x) ->
      let a'=find a array_tree' in(*array_treeでの変数名*)
      let array_tree'=add_child x (a',pos) array_tree' in
      add_childe_rec array_tree' (tree_map,x))
    array_tree
    a_children*)

                                               
(*tree_mapのa以下の全要素を,深さ優先でarray_treeに足しこむ.aはarray_treeにもある*)
let rec add_childe_rec array_tree (tree_map,a) pre_add=
  (*Format.eprintf "size=%d,%d,pre_addsize:%d@." (size array_tree) (M.cardinal tree_map) (List.length pre_add);*)
  let (_,a_children) = M.find a tree_map in
  if(a_children=[])then
    array_tree,pre_add
  else
    
    List.fold_left
      (fun (array_tree',pre_add') (pos,x) ->
        if(not (List.mem x pre_add')) then
          let a'=find a array_tree' in(*array_treeでの変数名*)
          let array_tree'=add_childe x (a',pos) array_tree' in
          add_childe_rec array_tree' (tree_map,x) (x::pre_add') 
        else(*xが既にaddされていた*)
          let x'=find x array_tree' in(*array_treeでの変数名*)
          let a'=find a array_tree' in(*array_treeでの変数名*)
          (add_parent_edge x' (a',pos) array_tree',pre_add'))
      (array_tree,pre_add)
      a_children
    
    
    
(*片方のarray_treeをもう片方に吸収させる形で合併*)
let union {body=tree_map1;roots=rts1;eq_env=env1}
          {body=tree_map2;roots=rts2;eq_env=env2} =
  let array_tree'=  {body=tree_map1;roots=rts1;eq_env=M.empty} in
  let array_tree'=set_root rts2 array_tree' in(*2のルートを足し,*)
  (*tree_map2のroot以下の要素全てをarray_tree'にaddする*)
  let {body=tree_map';roots=rts';eq_env=env'},pre_add=
    List.fold_left
      (fun (array_tree',pre_add') x ->
        (*Format.eprintf "union_fold_left@.";*)
        add_childe_rec array_tree' (tree_map2,x) pre_add')
      (array_tree',[])
      rts2
  in
  ({body=tree_map';roots=rts';eq_env=env1},env')


let choose_may_same (pos,x) candidate =
  List.fold_left
    (fun may_same_list (pos',y) ->
      if(x=y) then may_same_list else
        let unknown=VarCatego.Array(VarCatego.Unknown) in
        if((pos=pos')
           ||(pos=unknown||pos'=unknown)
           ||((VarCatego.is_intpos pos)&&(VarCatego.is_indexpos pos'))
           ||((VarCatego.is_intpos pos')&&(VarCatego.is_indexpos pos))
          )
        then
          y::may_same_list
        else
          may_same_list)
    []
    candidate
          
             
          
              

(*x=a[unknown],y=a[1]やx=a[i],y=a[0]などは変数名は違っても同じものを示している可能性がある.array_treeの変数に対し、同じものを示している可能性のある別の変数を対応させる *)
let mk_may_same_env {body=tree_map;roots=rts;eq_env=_}=

  let rec inner tree env a =    (* treeのa以下の範囲を調べる *)
    let (_,a_children)=M.find a tree_map in
    let may_same_a = M.find a env in
    let candidate=(*aの子のmay_sameに成りうるarray　->　aとmay_sameなarrayの子*)
      List.fold_left
        (fun candidate b ->
          let (_,b_children)=M.find b tree in
          b_children@candidate)
        a_children
        may_same_a in

      List.fold_left
        (fun env' (pos,x) ->
          let may_same_x = choose_may_same (pos,x) candidate in
          let add_x_env=M.add x may_same_x env' in
          inner tree add_x_env x)
        env
        a_children(*a_children=[]だったら,envになる*)
  in
  
  List.fold_left
  (fun env root ->
    let env'=M.add root [] env in
    inner tree_map env' root)
  M.empty
  rts
    
(*根からのpathを返す*)
let rec path_from_root  ({body=tree;roots=rts;eq_env=_} as array_tree) (a,pos)=
  if(List.mem a rts)then
    (a,[pos])
  else
    let (a_parents,a_children)=M.find a tree in
    let original_parent=(*a_parentsの末尾が元々の親*)
      let rec tail_elm =function
        |[x] ->x
        |x::xs->tail_elm xs
        |[] ->assert false
      in
      tail_elm a_parents
    in
    let (r,ps)=path_from_root array_tree original_parent in
    (r,ps@[pos])
                          
        
            
