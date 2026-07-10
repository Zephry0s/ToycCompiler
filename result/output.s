.text

  .globl main
main:
  addi sp, sp, -32
  sw ra, 28(sp)
  li t0, 0
  sw t0, 4(sp)
.while0:
  lw t0, 4(sp)
  li t1, 3
  slt t0, t0, t1
  beqz t0, .while_end1
  lw t0, 4(sp)
  li t1, 1
  sub t0, t0, t1
  seqz t0, t0
  beqz t0, .if_else2
  lw t0, 4(sp)
  li t1, 1
  add t0, t0, t1
  sw t0, 4(sp)
  j .while0
.if_else2:
.if_end3:
  lw t0, 4(sp)
  li t1, 2
  sub t0, t0, t1
  seqz t0, t0
  beqz t0, .if_else4
  j .while_end1
.if_else4:
.if_end5:
  lw t0, 4(sp)
  li t1, 1
  add t0, t0, t1
  sw t0, 4(sp)
  j .while0
.while_end1:
  lw t0, 4(sp)
  mv a0, t0
  j .main_ret
.main_ret:
  lw ra, 28(sp)
  addi sp, sp, 32
  li a7, 10
  ecall
