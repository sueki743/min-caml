type t =(*mk_rw_graph,notW_hypoで式全体の値として返す型*)
  |Int of int
  |Index of int
  |Float of float
  |Element of Id.t * Var_loop.elm_pos
  |Unknown
