let limit = ref 1000

let rec iter n e = (* 最適化処理をくりかえす (caml2html: main_iter) *)
  Format.eprintf "iteration %d@." n;
  if n = 0 then e else
    let e'=Elim.f (ConstFold.f (Inline.f (Assoc.f (Beta.f e))))
    in
  if e = e' then e else
  iter (n - 1) e'


let rec iter_nonrec n e =       (* 非再帰関数を無条件に展開 *)
  Format.eprintf "iteration_norec %d@." n;
  if n = 0 then e else
    let e'=Elim.f (ConstFold.f (Inline_nonrec.f (Assoc.f (Beta.f e))))
    in
  if e = e' then e else
  iter_nonrec (n - 1) e'

       
let lexbuf outchan oc_childe outchan2 outchan3 outchan4 l glb_l= (* バッファをコンパイルしてチャンネルへ出力する (caml2html: main_lexbuf) *)
  Id.counter := 0;
  Typing.extenv := M.empty;
  Emit.f outchan
         oc_childe
         (RegAlloc.f
            (Multosll.f
            (Simm.f
	  (Virtual.f
             (Emit_closure.f
                outchan4
	        (Closure.f
                   (HpAlloc.f
                      (Emit_knormal.f
                         outchan3
		         (iter !limit
                               (iter_nonrec !limit
                                (Parallelize.f
                               (Emit_knormal.f
                                  outchan3
                                  (Unique_constdef.f
                               (For_check.f
                                  (Assoc.f
		                  (Alpha.f
                                  
                                    
		                     (KNormal.f
                                        (Emit_syntax.f
                                           outchan2 
			                   (Typing.f
                                              (Joinglb.f
			                         (Parser.exp Lexer.token l)
                                                 (Parser.exp Lexer.token glb_l)))))))))))))))))))))

         
let string s glbchan = lexbuf stdout stdout stdout stdout stdout (Lexing.from_string s) (Lexing.from_channel glbchan) (* 文字列をコンパイルして標準出力に表示する (caml2html: main_string) *)

let file f = (* ファイルをコンパイルしてファイルに出力する (caml2html: main_file) *)

  let catin = open_in (f ^ ".ml") in
  let catout = open_out (f ^ ".mlo") in
  let libin = open_in ("./mylib.ml") in
	(let rec lib_sub () =
	output_char catout (input_char libin);
	lib_sub ()
  in
	(try lib_sub () with End_of_file -> ()));
	(let rec cat_sub () =
	output_char catout (input_char catin);
	cat_sub ()
  in
	(try cat_sub () with End_of_file -> close_in catin; close_out catout));
  

  let inchan = open_in (f ^ ".mlo") in
  let glbchan = open_in ("globals.ml") in
  let outchan = open_out (f ^ ".s") in
  let oc_child = open_out (f^"child.s") in
  let outchan2 = open_out (f ^ "_syn.txt") in
  let outchan3 = open_out (f^"_k1.txt") in
  let outchan4 = open_out (f^"_closure.txt") in
  try
    lexbuf outchan oc_child outchan2 outchan3 outchan4 (Lexing.from_channel inchan) (Lexing.from_channel glbchan);
    close_in inchan;
    close_out outchan;
    close_out oc_child;
    close_out outchan2;
    close_out outchan3;
    close_out outchan4;
  with
  |Typing.Error (t1,t2,pos)-> close_in inchan;
                              close_out outchan;
                              close_out outchan2;
                              close_out outchan3;
                              close_out outchan4;
                              let line = pos.Syntax.line in
                              let charnum= pos.Syntax.characters in
                              Printf.printf "line %d, from character %d~\n" line charnum;
                              Printf.printf "this expression has  type\n";
                              Emit_syntax.print_type stdout t2;
                              Printf.printf "\nbut an expression was expected of type\n";
                              Emit_syntax.print_type stdout t1;
  |Typing.Occur (t1,t2,pos)-> close_in inchan;
                              close_out outchan;
                              close_out outchan2;
                              close_out outchan3;
                              close_out outchan4;
                              let line = pos.Syntax.line in
                              let charnum= pos.Syntax.characters in
                              Printf.printf "line %d, from character %d~\n" line charnum;
                              Printf.printf "this expression has  type\n";
                              Emit_syntax.print_type stdout t2;
                              Printf.printf "\nbut an expression was expected of type\n";
                              Emit_syntax.print_type stdout t1;
                              Printf.printf "\n this is occurcheck error"

  |e -> (close_in inchan; close_out outchan; raise e)

let () = (* ここからコンパイラの実行が開始される (caml2html: main_entry) *)
  let files = ref [] in
  Arg.parse
    [("-inline", Arg.Int(fun i -> Inline.threshold := i), "maximum size of functions inlined");
     ("-iter", Arg.Int(fun i -> limit := i), "maximum number of optimizations iterated")]
    (fun s -> files := !files @ [s])
    ("Mitou Min-Caml Compiler (C) Eijiro Sumii\n" ^
     Printf.sprintf "usage: %s [-inline m] [-iter n] ...filenames without \".ml\"..." Sys.argv.(0));
  List.iter
    (fun f -> ignore (file f))
    !files (*filesにあるファイルを先頭からコンパイル*)
