
type node = ((Id.t*VarCatego.elm_pos list)*(VarCatego.elm_pos*Id.t list)) 
(*(親,子)要素の情報を各nodeが持つ*)

type t = {body:node M.t ; root : Id.t list ; eq_env:Id.t M.t}

exception Not_preserve

let empty = {body=M.empty; root=[];eq_env=M.empty}
let find a {body=_;roots=_;eq_env=env} =
  try M.find a env with Not_found ->a

let mem a {body=tree;roots=_;eq_env=env}=M.mem a tree

            
(*rootのリストを足す*)
let set_root l {body=tree_map; roots= list ; eq_env=env} as array_tree=
  let l=List.filter (fun x ->not (mem x array_tree)) l in
  let l_nodes = List.map (fun x ->(x,([],[]))) l in(*親も子もないnode*)
  let tree_map'=M.add_list l_nodes tree_map in
  let list'=l@list in(*rootを足す*)
  {body=tree_map' ; roots= list' eq_env=env}


let put (a,pos,x) {body=tree;roots=list ; eq_env=env} =
  if(M.mem x tree)then
    raise Not_preserve(*minrtではとりあえずこれで良い*)
  else
    {body=tree;roots=list ; eq_env=env}

let find_child (a,pos)  {body=tree_map ; roots=list ; eq_env=env} =
  if(pos=VarCatego.Array(VarCatego.Unknown)) then
    raise Not_found
  else
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

  
let add_childe x (a,pos) {body=tree_map ; roots=list ; eq_env=env} as array_tree =
  try
    let y=find_child (a,pos) array_tree in(*aのposにある要素*)
    (*xとyは同じ領域を表してる,envに情報を足す*)
    {body=tree_map ; roots=list ; eq_env=M.add x y env }
  with
    Not_found ->(*a,posに変数は登録されていなかった*)
    add_new_child x (a,pos) array_tree

let add_parent x pos_childs {body=tree_map;roots=rts; eq_env=env} as array_tree =
  let tree_map'=
    List.fold_left
      (fun tree_map' (pos,a) ->
        let (a_parent,a_children)=M.find a tree_map in
        M.add a (((x,pos)::a_parent),a_children) tree_map')
      tree_map
      pos_childs
  in
  let tree_map' = M.add x pos_childs tree_map' in
  let x_children = List.map (fun (pos,a) ->a) pos_child in
  let rts' = List.filter (fun a ->not (List.mem a x_children)) (x::rts) in
  {body=tree_map';roots=rts';eq_env=env}

(*xからparent枝を生やす　*)
let add_parent_edge x (a,pos)  {body=tree_map;roots=rts; eq_env=env} as array_tree =
  let (x_parent,x_children)=M.find x tree_map in
  let (a_parent,a_children)=M.find a tree_map in
  let tree_map'=M.add x ((a,pos)::x_parent,x_children) tree_map in
  let tree_map'=M.add a (a_parent,(pos,x)::a_children) tree_map' in
  let rts' = List.filter (fun x' ->x<>x') rts in
   {body=tree_map';roots=rts'; eq_env=env} as array_tree 
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

                                               
(*tree_mapのa以下の全要素を,深さ優先でarray_treeに足しこむ*)                         let rec add_childe_rec array_tree (tree_map,a) pre_add=
  let (_,a_children) = M.find a tree_map in
  List.fold_left
    (fun (array_tree',pre_add') (pos,x) ->
      if(not (List.mem x pre_add)) then
        let a'=find a array_tree' in(*array_treeでの変数名*)
        let array_tree'=add_child x (a',pos) array_tree' in
        let (array_tree',pre_add') =
          add_childe_rec array_tree' (tree_map,x) x::pre_add in
        (array_tree',pre_add')
      else(*xが既にaddされていた*)
        let x'=find x array_tree' in(*array_treeでの変数名*)
        let a'=find a array_tree' in(*array_treeでの変数名*)
        (add_parent_edge x' (a',pos) array_tree',pre_add)
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
        add_childe_rec array_tree' (tree_map2,x) pre_add')
      (array_tree',pre_add)
      rts2
  in
  ({body=tree_map';roots=rts';eq_env=env1},env')

              
