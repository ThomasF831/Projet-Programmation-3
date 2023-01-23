	.text
	.globl	main
main:
	call F_main
	xorq %rax, %rax
	ret
F_main:
	pushq %rbp
	movq %rsp, %rbp
	movq $5, %rdi
	pushq %rdi
	movq $9, %rdi
	pushq %rdi
	movq -8(%rbp), %rdi
	call print_int
	movq -16(%rbp), %rdi
	call print_int
	movq -16(%rbp), %rdi
	pushq %rdi
	movq -8(%rbp), %rdi
	pushq %rdi
	popq %rdi
	movq %rdi, -16(%rbp)
	popq %rdi
	movq %rdi, -8(%rbp)
	movq -8(%rbp), %rdi
	call print_int
	movq -16(%rbp), %rdi
	call print_int
	popq %rdx
	popq %rdx
	popq %rbp
	ret

print_int:
        movq    %rdi, %rsi
        movq    $S_int, %rdi
        xorq    %rax, %rax
        call    printf
        ret
print_string:
        movq $0, %rax
        call printf
        ret
print_bool:
        testq %rdi, %rdi
        jne print_true
        je print_false
        ret
print_true:
        movq $true, %rdi
        call print_string
        ret
print_false:
        movq $false, %rdi
        call print_string
        ret
	.data
true:
	.string "true\n"
false:
	.string "false\n"
S_int:
	.string "%ld\n"
