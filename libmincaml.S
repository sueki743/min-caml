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
min_caml_fneg:
	neg.s	%f0, %f0
	jr	%r31
min_caml_read_int:
	lui	%r1, 0
	in	%r1
	lui	%r2, 0
	in	%r2
	sll	%r2, %r2, 8
	or	%r1, %r1, %r2
	lui	%r2, 0
	in	%r2
	sll	%r2, %r2, 16
	or	%r1, %r1, %r2
	lui	%r2, 0
	in	%r2
	sll	%r2, %r2, 24
	or	%r1, %r1, %r2
	jr	%r31
min_caml_read_float:
	lui	%r1, 0
	in	%r1
	lui	%r2, 0
	in	%r2
	sll	%r2, %r2, 8
	or	%r1, %r1, %r2
	lui	%r2, 0
	in	%r2
	sll	%r2, %r2, 16
	or	%r1, %r1, %r2
	lui	%r2, 0
	in	%r2
	sll	%r2, %r2, 24
	or	%r1, %r1, %r2
	sw	%r1, 0(%r30)
	lw.s	%f0, 0(%r30)
	jr	%r31
min_caml_print_char:
	out	%r1
	jr	%r31
