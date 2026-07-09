.text

  .globl main
main:
  addi sp, sp, -32
  sw ra, 28(sp)
  li t0, 1
  li t1, 2
  add t0, t0, t1
  li t1, 3
  add t0, t0, t1
  li t1, 4
  add t0, t0, t1
  li t1, 5
  add t0, t0, t1
  mv a0, t0
  j .main_ret
.main_ret:
  lw ra, 28(sp)
  addi sp, sp, 32
  li a7, 10
  ecall
