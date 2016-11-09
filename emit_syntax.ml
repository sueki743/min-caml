open Printf
open Syntax

     


       
let rec  print_type oc ty =
  match ty with
  |Type.Unit  ->fprintf oc "()"
  |Type.Bool ->fprintf oc "bool"
  |Type.Int ->fprintf oc "int"
  |Type.Float ->fprintf oc "float"
  |Type.Fun ([t1],body)->print_type oc t1;
                    fprintf oc " -> ";
                    print_type oc body;
                    fprintf oc " = <fun>"
  |Type.Fun ((t1::other),body)->print_type oc t1;
                           fprintf oc " -> ";
                           print_type oc (Fun (other,body))
  |Type.Tuple (t::other) ->fprintf oc "(";
                      print_type oc t;
                      List.map (fun x ->fprintf oc " * ";print_type oc x) other;
                      fprintf oc ")"
  |Type.Array t ->print_type oc t;
             fprintf oc " array"
  |Type.Var r ->(match !r with
           |None ->fprintf oc "none"
           |Some t ->print_type oc t)
                                
let rec g oc tree depth =
  fprintf oc "%*s" depth "";
  match tree with
  |Unit _->fprintf oc "UNI\n"
  |Bool (b,_)  ->fprintf oc "Bool %B\n" b
  |Int (i,_) ->fprintf oc "Int %d\n" i
  |Float (f,_)->fprintf oc "Float %f\n" f
  |Not t ->fprintf oc "Not\n";
           g oc t (depth +1)
  |Neg t ->fprintf oc "Neg\n";
           g oc t (depth +1)
  |Add (t1,t2) ->fprintf oc "Add\n";
               g oc t1 (depth +1);
               g oc t2 (depth +1)
  |Sub (t1,t2) ->fprintf oc "Sub\n";
               g oc t1 (depth +1);
               g oc t2 (depth +1)
  |Mul (t1,t2) ->fprintf oc "Mul\n";
                 g oc t1 (depth +1);
                 g oc t2 (depth +1)
  |Div (t1,t2) ->fprintf oc "Div\b";
                 g oc t1 (depth+1);
                 g oc t2 (depth+1)
  |FNeg t ->fprintf oc "FNeg\n";
            g oc t (depth +1)
  |FAdd (t1,t2) ->fprintf oc "FAdd\n";
               g oc t1 (depth +1);
               g oc t2 (depth +1)
  |FSub (t1,t2) ->fprintf oc "FSub\n";
               g oc t1 (depth +1);
               g oc t2 (depth +1)
  |FMul (t1,t2) ->fprintf oc "FMul\n";
               g oc t1 (depth +1);
               g oc t2 (depth +1)
  |FDiv (t1,t2) ->fprintf oc "FDiv\n";
               g oc t1 (depth +1);
               g oc t2 (depth +1)
  |Eq (t1,t2) ->fprintf oc "Eq\n";
               g oc t1 (depth +1);
               g oc t2 (depth +1)
  |LE (t1,t2) ->fprintf oc "LE\n";
               g oc t1 (depth +1);
               g oc t2 (depth +1)
  |If (t1,t2,t3) ->fprintf oc "If\n";
                 g oc t1 (depth +1);
                 g oc t2 (depth +1);
                 g oc t3 (depth +1);
  |Let ((id1,ty1),t2,t3) ->fprintf oc "Let\n";
                          fprintf oc "%*s%s\n" (depth+1) "" id1;
                          g oc t2 (depth+1);
                          g oc t3 (depth+1);
  |Var (v,_) ->fprintf oc "(%s)\n" v;
  |LetRec (fundef,t1)->fprintf oc "LetRec\n";
                       fprintf oc "%*s" (depth+1) "";
                       let {name=(n1,ty1),_;args=arglist;body=funbody}=fundef in
                       fprintf oc "<<";
                       fprintf oc " %s | " n1;
                       List.map (fun (id,ty)->fprintf oc "%s " id) arglist;
                       fprintf oc "|\n\n";
                       g oc funbody (depth+2);
                       fprintf oc "\n%*s>>\n" (depth+1) "";
                       g oc t1 (depth+1)
  |App (t1,ts) -> fprintf oc "App\n";
                  List.map (fun x ->g oc x (depth +1)) (t1::ts);
                  ()
  |Tuple ts ->fprintf oc "Tuple\n";
              (match ts with
               |[] -> fprintf oc "\n";
               |_ ->List.map (fun x ->g oc x (depth +1)) ts;
                    ())
  |LetTuple (ids1,t2,t3)->fprintf oc "LetTuple\n";
                          fprintf oc "%*s" (depth+1) "";
                          List.map (fun (id,ty)->fprintf oc "%s " id) ids1;
                          fprintf oc "\n";
                          g oc t2 (depth+1);
                          g oc t3 (depth+2)
  |Array (t1,t2) ->fprintf oc "Array\n";
                   g oc t1 (depth+1);
                   g oc t2 (depth+2);
  |Get (t1,t2) ->fprintf oc "Get\n";
                 g oc t1 (depth+1);
                 g oc t2 (depth+1)
  |Put (t1,t2,t3)->fprintf oc "Put\n";
                   g oc t1 (depth+1);
                   g oc t2 (depth+1);
                   g oc t3 (depth+1)
                     
                               
let f oc tree =g oc tree 0;
               tree
                        
                       
