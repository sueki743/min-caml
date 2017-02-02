open KNormal
       
let find x var_category =
  try M.find x var_category with Not_found ->VarCatego.Unknown
                                               
let f array_tree var_category trace =function
  |Unit ->VarCatego.Unit
  |Int(i) ->VarCatego.Int(i)
  |Float(d) ->VarCatego.Float(d)
  |Tuple(xs) ->
    let xs_n,_ = List.fold_left
                   (fun (xs_n,n) x ->
                     ((x,n)::xs_n,n+1))
                   ([],0)
                   xs in
    let xs' =List.filter (fun (x,_) ->Array_tree.mem x array_tree) xs_n in
    if(xs'=[])then VarCatego.Unknown
    else
      let pos_children =
        List.map
          (fun (x,n) ->(VarCatego.Tuple(n),x))
          xs'
      in
      VarCatego.Parent(pos_children)
  |Var(x) ->
    let x' = Array_tree.find x array_tree in
    if(Array_tree.mem x' array_tree) then
      VarCatego.Arraytree_var(x')
    else
      let x_cate=find x var_category in
    (match x_cate with
     |VarCatego.Unit|VarCatego.Index _|VarCatego.Float _
      |VarCatego.Int _|VarCatego.Arraytree_var _ ->
       x_cate
     |_ ->
               VarCatego.Unknown)
  |Add(x,y)|FAdd(x,y)->
    if(M.mem x trace||M.mem y trace) then
      (
        (* Format.eprintf "tarce_add!!!!!!!!!!!!!!!!!!!!!!!!!%s+%s@." x y; *)
      VarCatego.Trace_add(x,y))
    else
      
      let x'=find x var_category in
      let y'=find y var_category in
      (match (x',y') with
       |(VarCatego.Int(i),VarCatego.Int(j)) ->VarCatego.Int(i+j)
       |(VarCatego.Index(i),VarCatego.Int(j))
        |(VarCatego.Int(i),VarCatego.Index(j))->
         VarCatego.Index(i+j)
       |_ ->VarCatego.Unknown)
  |Sub(x,y)|FSub(x,y) ->
    let x'=find x var_category in
    let y'=find y var_category in
    (match (x',y') with
     |(VarCatego.Int(i),VarCatego.Int(j)) ->VarCatego.Int(i-j)
     |(VarCatego.Index(i),VarCatego.Int(j))->
       VarCatego.Index(i-j)
     |_ ->VarCatego.Unknown)
  |_ ->VarCatego.Unknown
