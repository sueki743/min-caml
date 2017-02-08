open KNormal

let find_d env constenv index step =
  let rec inner index_elm =function
    |Let((x,t),Ref_Get(i),e2) when i=index ->
      inner (x::index_elm) e2
    |Add(x,d) when (List.mem x index_elm) ->
      (d,None,env,constenv)
    |Add(d,x) when (List.mem x index_elm) ->
      (d,None,env,constenv)
        
    |Sub(x,d) ->
      let d' = Id.genid d in
      let env' = M.add d' Type.Int env in
      if M.mem d constenv then
        let d_i = (match M.find d constenv with Int(i) ->i|_ ->assert false) in
        let constenv' = M.add d' (Int(-d_i)) constenv in
        
        (d',Some (Neg(d)),env',constenv')
      else
        (d',Some ( Neg(d)),env',constenv)
 
    |_ ->assert false
  in
  inner [] step


let find_int x constenv =
  match M.find x constenv with Int(i) ->i|_ ->assert false

let list_union l1 l2 =
  l1@(List.filter (fun x ->not (List.mem x l1)) l2)

let parallel_part = ref []
(*並列化可能ループ込みのfundefとaccumを受け取り、並列化ルーチンと、それを使ったfundefを返す*)
let f {name=(x,t);args=yts ; body=e} accum =
  (* let dv=Id.genid "dummy" in *)
  (* let dummy={pargs=[];index=((dv,dv),(V(dv),V(dv)),V(dv));accum=[];pbody=Unit} in *)
  (* let parallel_part =ref dummy in(\*並列化コードを入れる*\) *)
  let rec inner env constenv = function
    |Let((x,t),(Int _ as const),e2)|Let((x,t),(Float _ as const),e2) ->
      Let((x,t),const,inner (M.add x t env) (M.add x const constenv) e2)
    |Let((x,t),e1,e2) ->
      Let((x,t),inner env constenv e1,inner (M.add x t env) constenv e2)
    |LetRec(fundef,e2) ->
      LetRec(fundef,inner env constenv e2)
    |Let_Ref((x,t),e1,e2) ->
      Let_Ref((x,t),inner env constenv e1,inner (M.add x t env) constenv e2)
    |LetTuple(xts,y,e2) ->
      let env'=List.fold_left (fun env (x,t) ->M.add x t env) env xts in
      LetTuple(xts,y,inner env' constenv e2)
    |IfLE(i,j,e1,e2) ->
      IfLE(i,j,inner env constenv e1,inner env constenv e2)
    |IfEq(i,j,e1,e2) ->
      IfEq(i,j,inner env constenv e1,inner env constenv e2)
    |ForLE(((i,a),(j,k),step),e1) ->
      let (d,d_def,env,constenv) =find_d env constenv i step in
      let (j',k',arg_header)=if(j=i)then
                    if(M.mem k constenv)then
                      let k_i=
                        (match M.find k constenv with Int(i)->i|_ ->assert false) in
                      (Id.V(i),Id.C(k_i),[])
                    else
                      (Id.V(i),Id.V(k),[k])

                  else if (k=i)then
                    if(M.mem j constenv)then
                      let j_i=
                        (match M.find j constenv with Int(i)->i|_ ->assert false) in
                      (Id.C(j_i),Id.V(i),[])
                    else
                      (Id.V(j),Id.V(i),[j])
                  else
                    assert false
      in
            (* let arg_header=a::arg_header in *)
      let e1'=S.fold            (* 定数定義挿入  *)
                (fun x e ->
                  if M.mem x constenv then
                    let const = M.find x constenv in
                    assert (M.mem x env);
                    Let((x,M.find x env),const,e)
                  else
                    e)
                (fv e1)
                e1
                
      in
      let arg_body=S.filter (fun x ->M.mem x env) (fv e1') in
      let arg = S.elements (S.diff
                              (S.union
                                 (S.of_list arg_header)
                                 arg_body)
                              (S.of_list [i;d]))
      in
      let argt = List.map (fun x ->(x,M.find x env)) arg in
      let parallel =
        {pargs=argt;
         index=(i,(j',k'));
         accum=accum;
         pbody=e1'}
      in
      let accum' = List.map (List.hd) accum in
      let e'=(*for文は、run_parallelを呼ぶだけに潰す*)
        (match d_def with
         |Some def ->if(M.mem d constenv) then
                       Let((d,Type.Int),def,
                           Run_parallel(a,d,arg,accum'))
                     else
                       Run_parallel(a,d,arg,accum')
         |None ->Run_parallel(a,d,arg,accum'))
      in
      parallel_part:=parallel::(!parallel_part);
      e'
    |e ->e

  in
  let rec loop_exist = function
    | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2)
      | Let(_, e1, e2) | LetRec({ body = e1 }, e2)|Let_Ref(_,e1,e2) ->
       (loop_exist e1)||(loop_exist e2)
    |LetTuple(_,_,e)->loop_exist e
    |ForLE _ ->true
    |_ ->false
  in
  assert (loop_exist e);
  
  let e'=inner (M.add x t(M.add_list yts (M.empty))) M.empty e in
   assert ((List.length (!parallel_part))=1); 
  {name=(x,t);args=yts;body= e'},List.hd (!parallel_part)
      
