open Printf
open Closure

let print_id oc id depth=
  fprintf oc "%*s" depth "";
  fprintf oc "(";
  Id.print_id oc id;
  fprintf oc ")\n"
       
let rec g oc tree depth =
  fprintf oc "%*s" depth "";
  match tree with
  |Unit ->fprintf oc "UNIT"
  |Int i ->fprintf oc "Int %d\n" i
  |Float f->fprintf oc "Float %f\n" f
  |Neg t ->fprintf oc "Neg\n";
           print_id oc t (depth+1)
  |Add (t1,t2) ->fprintf oc "Add\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
  |Sub (t1,t2) ->fprintf oc "Sub\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
  |Mul (t1,t2) ->fprintf oc "Mul\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
  |Div (t1,t2) ->fprintf oc "Div\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
  |FNeg t ->fprintf oc "FNeg\n";
            print_id oc t  (depth+1)
  |FAdd (t1,t2) ->fprintf oc "FAdd\n";
                  print_id oc t1 (depth+1);
                  print_id oc t2 (depth+1)
  |FSub (t1,t2) ->fprintf oc "FSub\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
  |FMul (t1,t2) ->fprintf oc "FMul\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
  |FDiv (t1,t2) ->fprintf oc "FDiv\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
  |Ftoi (t1) ->fprintf oc "Ftoi\n";
               print_id oc t1 (depth+1);
  |Itof (t1) ->fprintf oc "Itof\n";
               print_id oc t1 (depth+1);
  |FAbs (t1) ->fprintf oc "FAbs\n";
               print_id oc t1 (depth+1);
  |FSqrt (t1) ->fprintf oc "FSqrt\n";
                print_id oc t1 (depth+1);
  |Read_int(t1) ->fprintf oc "Read_int(%s)\n" t1
  |Read_float(t1) ->fprintf oc "Read_float(%s)\n" t1
  |Print_char(t1)->fprintf oc "Print_char(%s)\n" t1
  |IfEq (t1,t2,tree1,tree2) ->fprintf oc "IfEq\n";
                              print_id oc t1 (depth+1);
                              print_id oc t2 (depth+1);
                              g oc tree1 (depth +1);
                              g oc tree2 (depth +1)
  |IfLE (t1,t2,tree1,tree2) ->fprintf oc "IfLE\n";
                              print_id oc t1 (depth+1);
                              print_id oc t2 (depth+1);
                              g oc tree1 (depth +1);
                              g oc tree2 (depth +1)
  |Let ((id1,ty1),t2,t3) ->fprintf oc "Let\n";
                           print_id oc id1 (depth+1);
                           g oc t2 (depth+1);
                           g oc t3 (depth);
  |Let_Ref((x,t),e1,e2) ->fprintf oc "Let_Ref\n";
                          print_id oc x (depth+1);
                          g oc e1 (depth+1);
                          g oc e2 (depth)
  |Var v ->fprintf oc "((";Id.print_id oc v;fprintf oc "))\n"
  |MakeCls ((id1,ty1),cl,tree) ->fprintf oc "MakeCls\n";
                                 print_id oc id1 (depth+1);
                                 fprintf oc "%*s" (depth+1) "";
                                 let {entry=en1;actual_fv=fvs}=cl in
                                 fprintf oc "<< ";
                                 Id.print_l oc en1;
                                 fprintf oc " | ";
                                 ignore (List.map (fun id->Id.print_id oc id;fprintf oc " ") fvs);
                                 fprintf oc ">>\n";
                                 g oc tree (depth)
  |AppCls (t1,ts) -> fprintf oc "AppCls\n";
                  ignore (List.map (fun x ->print_id oc x (depth +1)) (t1::ts));
                  ()
  |AppDir (t1,ts) ->fprintf oc "AppDir\n";
                    fprintf oc "%*s" (depth+1) "";Id.print_l oc t1;
                    fprintf oc "\n";
                    ignore (List.map (fun x ->print_id oc x (depth +1)) ts);
                    () 
  |Tuple ts ->fprintf oc "Tuple\n";
              (match ts with
               |[] -> fprintf oc "\n";
               |_ ->ignore (List.map (fun x ->print_id oc x (depth +1)) ts);
                    ())
  |ConstTuple (Id.L(x))->fprintf oc "ConstTuple %s\n" x;
  |LetTuple (ids1,t2,tree3)->fprintf oc "LetTuple\n";
                          fprintf oc "%*s" (depth+1) "";
                          ignore (List.map (fun (id,ty)->Id.print_id oc id;fprintf oc " ") ids1);
                          fprintf oc "\n";
                          print_id oc t2 (depth+1);
                          g oc tree3 (depth)
  |Get (t1,t2) ->fprintf oc "Get\n";
                 print_id oc t1 (depth+1);
                 print_id oc t2 (depth+1);
  |Put (t1,t2,t3)->fprintf oc "Put\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
               print_id oc t3 (depth+1)
  |ConstArray (Id.L(x))->fprintf oc "ConstArray %s\n" x
  |ExtArray t ->fprintf oc "ExtArray\n";
                fprintf oc "%*s" (depth+1) "";
                Id.print_l oc t;fprintf oc "\n"
  |ForLE(((i,a),(j,k),step),e)->
    fprintf oc "ForLE{%s=%s|%s<=%s|\n" i a j k;
    g oc step (depth+7);
    fprintf oc "|\n";
    g oc e (depth + 1);
    fprintf oc "%*s" depth "";fprintf oc "endforLE\n"
  |Ref_Get(t) ->fprintf oc "Ref_Get(%s)\n" t
  |Ref_Put(t1,t2) ->fprintf oc "Ref_Put(%s<-%s)\n" t1 t2
  |Run_parallel(a,d,xs,ys) ->fprintf oc "run_prallel(%s,%s)\n" a d;
                      List.iter (fun x ->print_id oc x (depth+1)) xs
  |Accum(a,n,x) ->fprintf oc "Accum(%s.(%s)  %s" a n x
                                        


let print_fundef oc fundef =
  let {name=(n1,ty1);args=arglist;formal_fv=fvlist;body=funbody}=fundef in
  fprintf oc "<< ";
  Id.print_l oc n1;
  fprintf oc " | ";
  ignore (List.map (fun (id,ty)->Id.print_id oc id;fprintf oc " ") arglist);
  fprintf oc "| ";
  ignore  (List.map (fun (id,ty)->Id.print_id oc id;fprintf oc " ") fvlist);
  fprintf oc "|\n\n";
  g oc funbody 1;
  fprintf oc "\n>>\n"

          

let f oc p = match p with
  |Prog (fundefl,parallel,tree)->
    if fundefl = [] then fprintf oc "no fundef\n"
    else ignore (List.map (print_fundef oc) fundefl);
                        fprintf oc "\n";
                        g oc tree 0;
                        p
