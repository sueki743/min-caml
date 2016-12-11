let rec fless x y = x < y in
let rec fispos x = x > 0.0 in
let rec fisneg x = x < 0.0 in
let rec fiszero x = (x = 0.0) in
let rec fhalf x = x *. 0.5 in
let rec fsqr x = x *. x in
let rec cos x =
	1.0 -. x *. x /. 2.0 +. x *. x *. x *. x /. 24.0
in
let rec sin x =
	x -. x *. x *. x /. 6.0 +. x *. x *. x *. x *. x /. 120.0
in
let rec atan x =
	x -. x *. x *. x /. 3.0 +. x *. x *. x *. x *. x /. 5.0
in
let rec floor x =
	float_of_int (int_of_float (x -. 0.5))
in


