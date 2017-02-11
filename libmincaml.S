min_caml_create_array:	
	mov	%r2, %r0
	mov	%r0, %r31
create_array_loop:
	bei	%r2, 0, create_array_return
	sw	%r1, 0(%r31)
	addi  	%r2, %r2, -1
	addi	%r31, %r31, 1
	j	create_array_loop
min_caml_create_float_array:
	mov	%r2, %r0
	mov	%r0, %r31
create_float_array_loop:
	bei	%r2, 0, create_array_return
	fsw	%f0, 0(%r31)
	addi	%r2, %r2, -1
	addi	%r31, %r31, 1
	j	create_float_array_loop
create_array_return:
	jr
