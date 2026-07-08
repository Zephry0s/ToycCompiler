.text

  .globl main
main:
  addi sp, sp, -64
  sw ra, 60(sp)
  li t0, 1
  sw t0, 20(sp)
  li t0, 2
  sw t0, 24(sp)
  lw t0, 20(sp)
  lw t1, 24(sp)
  add t0, t0, t1
  sw t0, 28(sp)
  li t0, 3
  sw t0, 32(sp)
  lw t0, 28(sp)
  lw t1, 32(sp)
  add t0, t0, t1
  sw t0, 36(sp)
  li t0, 4
  sw t0, 40(sp)
  lw t0, 36(sp)
  lw t1, 40(sp)
  add t0, t0, t1
  sw t0, 44(sp)
  li t0, 5
  sw t0, 48(sp)
  lw t0, 44(sp)
  lw t1, 48(sp)
  add t0, t0, t1
  sw t0, 52(sp)
  lw a0, 52(sp)
  j .main_ret
.main_ret:
  lw ra, 60(sp)
  addi sp, sp, 64
  li a7, 10
  ecall
