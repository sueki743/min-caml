min_caml_create_array:	
	ori	%r3, %r1, 0
	ori	%r1, %r29, 0
create_array_loop:
	bne	%r3, %r0, create_array_cont
	jr	%r31
create_array_cont:
	sw	%r2, 0(%r29)
	addi  	%r3, %r3, -1
	addi	%r29, %r29, 1
	j	create_array_loop
min_caml_create_float_array:
	ori	%r2, %r1, 0
	ori	%r1, %r29, 0
create_float_array_loop:
	bne	%r2, %r0, create_float_array_cont
	jr	%r31
create_float_array_cont:
	sw.s	%f0, 0(%r29)
	addi	%r2, %r2, -1
	addi	%r29, %r29, 1
	j	create_float_array_loop
