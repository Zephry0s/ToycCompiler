.text

  .globl main
main:
  addi sp, sp, -32
  sw ra, 28(sp)
  li a0, 15
  j .main_ret
.main_ret:
  lw ra, 28(sp)
  addi sp, sp, 32
  li a7, 10
  ecall
