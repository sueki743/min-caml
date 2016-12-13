let rec fless x y = x < y in
let rec fispos x = x > 0.0 in
let rec fisneg x = x < 0.0 in
let rec fiszero x = (x = 0.0) in
let rec fhalf x = x *. 0.5 in
let rec fsqr x = x *. x in
let rec taylor_cos x =
	let x2 = x *. x in
		1.0 -. x2 *. (0.5 -. x2 *. (0.04166368 -. x2 *. 0.0013695068))
in
let rec taylor_sin x =
	let x2 = x *. x in
		x *. (1.0 -. x2 *. (0.16666668 -. x2 *. (0.008332824 -. x2 *. 0.00019587841)))
in
(* 0付近の値のみ使うように最適化して、打ち切り誤差を減らす *)
let rec cos x =
	if x >= 0.0 then
		if x >  6.28318548202514 then
			cos (x -.  6.28318548202514)
		else
			if x < 3.1415927410 then
				if x < 1.5707963705 then
					if x < 0.785398185 then
						taylor_cos x
					else
						taylor_sin (1.5707963705 -. x)
				else
					if x < 2.35619455 then
						0.0 -. taylor_sin (x -. 1.5707963705)
					else
						0.0 -. taylor_cos (3.1415927410 -. x)
			else
				let y = x -. 3.1415927410 in
					if y < 1.5707963705 then
						if y < 0.785398185 then
							0.0 -. taylor_sin y
						else
							0.0 -. taylor_cos (1.5707963705 -. y)
					else
						if y < 2.35619455 then
							taylor_sin (y -. 1.5707963705)
						else
							taylor_cos (3.1415927410 -. y)
	else
		cos (0.0 -. x)
in
let rec sin x =
    if x >= 0.0 then
        if x >  6.28318548202514 then
            sin (x -.  6.28318548202514)
        else
            if x < 3.1415927410 then
                if x < 1.5707963705 then
                    if x < 0.785398185 then
                        taylor_sin x
                    else
                        taylor_cos (1.5707963705 -. x)
                else
                    if x < 2.35619455 then
                        taylor_cos (x -. 1.5707963705)
                    else
                        taylor_sin (3.1415927410 -. x)
            else
                let y = x -. 3.1415927410 in
                    if y < 1.5707963705 then
                        if y < 0.785398185 then
                            0.0 -. taylor_sin y
                        else
                            0.0 -. taylor_cos (1.5707963705 -. y)
                    else
                        if y < 2.35619455 then
                            0.0 -. taylor_cos (y -. 1.5707963705)
                        else
                            0.0 -. taylor_sin (3.1415927410 -. y)
    else
        0.0 -. sin (0.0 -. x)
in
let rec taylor_atan x =
    let x2 = x *. x in
        x *. (1.0 -. x2 *. (0.3333333 -. x2 *. (0.2 -. x2 *. (0.142857142 -. x2 *. (0.111111104 -. x2 *. (0.08976446 -. 0.060035485 *. x2))))))
in
let rec atan x =
	if x > 0.0 then
		if x < 0.4375 then
			taylor_atan x
		else
			if x < 2.4375 then
				0.78539818 +. taylor_atan ((x -. 1.0) /. (x +. 1.0))
			else
				1.57079637 -. taylor_atan (1.0 /. x)
		else
			let y = 0.0 -. x in
				if y < 0.4375 then
					0.0 -. (0.78539818 +. taylor_atan ((y -. 1.0) /. (y +. 1.0)))
				else
					0.0 -. (1.57079637 -. taylor_atan (1.0 /. y))
in
let rec floor x =
	float_of_int (int_of_float (x -. 0.5))
in


