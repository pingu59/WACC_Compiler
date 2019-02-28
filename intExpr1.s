.data
msg_4:
   .word 82
   .ascii "OverflowError: the result is too small/large to store in a 4-byte signed-integer.\n"
msg_3:
   .word 5
   .ascii "%.*s\NUL"
msg_2:
   .word 1
   .ascii "\NUL"
msg_1:
   .word 5
   .ascii "Wrong"
msg_0:
   .word 7
   .ascii "Correct"
.text
.global main
main:
    PUSH {lr}
    SUB sp, sp, #4
    MOV r4, sp
    LDR r2, =10
    LDR r1, =1
    SMULL r0, r0, r2, r1
    CMP r0, rtemp 21, ASR #31
    BLNE p_throw_overflow_error
    MOV r1, r0
    LDR r3, =10
    LDR r2, =1
    SMULL r1, r0, r3, r2
    CMP r0, rtemp 25, ASR #31
    BLNE p_throw_overflow_error
    LDR r0, =15
    ADD r1, r1, r0, LSL #1
    STR r1, [r4]
    LDR r0, [sp]
    CMP r0, #40
    BEQ label_0
label_1:
    LDR r1, =msg_1
    MOV r0, r1
    BL p_print_string
    BL p_print_ln
label_2:
    ADD sp, sp, #4
    MOV r0, #0
    POP {pc}
done:
label_0:
    LDR r1, =msg_0
    MOV r0, r1
    BL p_print_string
    BL p_print_ln
    B label_2
p_print_ln:
    PUSH {lr}
    LDR r0, =msg_2
    ADD r0, r0, #4
    BL puts
    MOV r0, #0
    BL fflush
    POP {pc}
p_print_string:
    PUSH {lr}
    LDR r1, [r0]
    ADD r2, r0, #4
    LDR r0, =msg_3
    ADD r0, r0, #4
    BL printf
    MOV r0, #0
    BL fflush
    POP {pc}
p_throw_runtime_error:
    BL p_print_string
    MOV r0, #-1
    BL exit
p_throw_overflow_error:
    LDR r0, =msg_4
    BL BL p_throw_runtime_error
