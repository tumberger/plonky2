// Load a single BLS value, consisting of two terms, from KernelGeneral
%macro mload_bls
    // stack:            offset
    DUP1
    %add_const(1)
    // stack: offset_hi, offset_lo
    %mload_kernel(@SEGMENT_KERNEL_GENERAL)
    // stack: val_hi, offset_lo
    SWAP1
    // stack: offset_lo, val_hi
    %mload_kernel(@SEGMENT_KERNEL_GENERAL)
    // stack: val_lo, val_hi
%endmacro

// Store a single BLS value, consisting of two terms, to KernelGeneral
%macro mstore_bls
    // stack:            offset, val_lo, val_hi
    SWAP1
    // stack:            val_lo, offset, val_hi
    DUP2
    // stack: offset_lo, val_lo, offset, val_hi
    %mstore_kernel(@SEGMENT_KERNEL_GENERAL)
    // stack:                    offset, val_hi
    %add_const(1)
    // stack:                 offset_hi, val_hi
    %mstore_kernel(@SEGMENT_KERNEL_GENERAL)
%endmacro


%macro add_fp381
    // stack:         x0, x1, y0, y1
    PROVER_INPUT(sf::bls381_base::add_hi)
    // stack:     z1, x0, x1, y0, y1
    SWAP4
    // stack:     y1, x0, x1, y0, z1
    PROVER_INPUT(sf::bls381_base::add_lo)
    // stack: z0, y1, x0, x1, y0, z1
    SWAP4
    // stack: y0, y1, x0, x1, z0, z1
    %pop4
    // stack:                 z0, z1
%endmacro

%macro mul_fp381
    // stack:         x0, x1, y0, y1
    PROVER_INPUT(sf::bls381_base::mul_hi)
    // stack:     z1, x0, x1, y0, y1
    SWAP4
    // stack:     y1, x0, x1, y0, z1
    PROVER_INPUT(sf::bls381_base::mul_lo)
    // stack: z0, y1, x0, x1, y0, z1
    SWAP4
    // stack: y0, y1, x0, x1, z0, z1
    %pop4
    // stack:                 z0, z1
%endmacro

%macro sub_fp381
    // stack:         x0, x1, y0, y1
    PROVER_INPUT(sf::bls381_base::sub_hi)
    // stack:     z1, x0, x1, y0, y1
    SWAP4
    // stack:     y1, x0, x1, y0, z1
    PROVER_INPUT(sf::bls381_base::sub_lo)
    // stack: z0, y1, x0, x1, y0, z1
    SWAP4
    // stack: y0, y1, x0, x1, z0, z1
    %pop4
    // stack:                 z0, z1
%endmacro

global test_add_fp381:
    %add_fp381
    %jump(0xdeadbeef)

global test_mul_fp381:
    %mul_fp381
    %jump(0xdeadbeef)

global test_sub_fp381:
    %sub_fp381
    %jump(0xdeadbeef)


global add_fp381_2:
    // stack: x_re, x_im, y_re, y_im, jumpdest
    %stack (x_re: 2, x_im: 2, y_re: 2, y_im: 2) -> (y_im, x_im, y_re, x_re)
    // stack: y_im, x_im, y_re, x_re, jumpdest
    %add_fp381
    // stack:       z_im, y_re, x_re, jumpdest
    %stack (z_im: 2, y_re: 2, x_re: 2) -> (x_re, y_re, z_im)
    // stack:       x_re, y_re, z_im, jumpdest
    %add_fp381
    // stack:             z_re, z_im, jumpdest
    %stack (z_re: 2, z_im: 2, jumpdest) -> (jumpdest, z_re, z_im)
    JUMP

global mul_fp381_2:
    // stack:                          x_re, x_im, y_re, y_im, jumpdest
    DUP4
    DUP4
    // stack:                    x_im, x_re, x_im, y_re, y_im, jumpdest
    DUP8
    DUP8
    // stack:              y_re, x_im, x_re, x_im, y_re, y_im, jumpdest
    DUP12
    DUP12
    // stack:        y_im, y_re, x_im, x_re, x_im, y_re, y_im, jumpdest
    DUP8
    DUP8
    // stack: x_re , y_im, y_re, x_im, x_re, x_im, y_re, y_im, jumpdest
    %mul_fp381
    // stack: x_re * y_im, y_re, x_im, x_re, x_im, y_re, y_im, jumpdest
    %stack (v: 2, y_re: 2, x_im: 2) ->  (x_im, y_re, v)
    // stack:  x_im , y_re, x_re*y_im, x_re, x_im, y_re, y_im, jumpdest
    %mul_fp381
    // stack:  x_im * y_re, x_re*y_im, x_re, x_im, y_re, y_im, jumpdest
    %add_fp381
    // stack:                    z_im, x_re, x_im, y_re, y_im, jumpdest
    %stack (z_im: 2, x_re: 2, x_im: 2, y_re: 2, y_im: 2) -> (x_im, y_im, y_re, x_re, z_im)
    // stack:                   x_im , y_im, y_re, x_re, z_im, jumpdest
    %mul_fp381
    // stack:                   x_im * y_im, y_re, x_re, z_im, jumpdest
    %stack (v: 2, y_re: 2, x_re: 2) -> (x_re, y_re, v)
    // stack:                    x_re , y_re, x_im*y_im, z_im, jumpdest
    %mul_fp381
    // stack:                    x_re * y_re, x_im*y_im, z_im, jumpdest
    %sub_fp381
    // stack:                                      z_re, z_im, jumpdest
    %stack (z_re: 2, z_im: 2, jumpdest) -> (jumpdest, z_re, z_im)
    JUMP

global sub_fp381_2:
    // stack: x_re, x_im, y_re, y_im, jumpdest
    %stack (x_re: 2, x_im: 2, y_re: 2, y_im: 2) -> (x_im, y_im, y_re, x_re)
    // stack: x_im, y_im, y_re, x_re, jumpdest
    %sub_fp381
    // stack:       z_im, y_re, x_re, jumpdest
    %stack (z_im: 2, y_re: 2, x_re: 2) -> (x_re, y_re, z_im)
    // stack:       x_re, y_re, z_im, jumpdest
    %sub_fp381
    // stack:             z_re, z_im, jumpdest
    %stack (z_re: 2, z_im: 2, jumpdest) -> (jumpdest, z_re, z_im)
    JUMP

global add_fp381_6:
    // stack:           inA, inB, out, jumpdest
    DUP2
    // stack:     inB0, inA, inB, out, jumpdest
    %mload_bls
    // stack:       B0, inA, inB, out, jumpdest
    DUP3
    // stack: inA0, B0, inA, inB, out, jumpdest
    %mload_bls
    // stack:   A0, B0, inA, inB, out, jumpdest
    %add_fp381
    // stack:       C0, inA, inB, out, jumpdest
    DUP5
    // stack: out0, C0, inA, inB, out, jumpdest
    %mstore_bls

    // stack:           inA, inB, out, jumpdest
    DUP2
    %add_const(2)
    // stack:     inB1, inA, inB, out, jumpdest
    %mload_bls
    // stack:       B1, inA, inB, out, jumpdest
    DUP3
    %add_const(2)
    // stack: inA1, B1, inA, inB, out, jumpdest
    %mload_bls
    // stack:   A1, B1, inA, inB, out, jumpdest
    %add_fp381
    // stack:       C1, inA, inB, out, jumpdest
    DUP5
    %add_const(2)
    // stack: out1, C1, inA, inB, out, jumpdest
    %mstore_bls

    // stack:           inA, inB, out, jumpdest
    DUP2
    %add_const(4)
    // stack:     inB2, inA, inB, out, jumpdest
    %mload_bls
    // stack:       B2, inA, inB, out, jumpdest
    DUP3
    %add_const(4)
    // stack: inA2, B2, inA, inB, out, jumpdest
    %mload_bls
    // stack:   A2, B2, inA, inB, out, jumpdest
    %add_fp381
    // stack:       C2, inA, inB, out, jumpdest
    DUP5
    %add_const(4)
    // stack: out2, C2, inA, inB, out, jumpdest
    %mstore_bls

    // stack:           inA, inB, out, jumpdest
    DUP2
    %add_const(6)
    // stack:     inB3, inA, inB, out, jumpdest
    %mload_bls
    // stack:       B3, inA, inB, out, jumpdest
    DUP3
    %add_const(6)
    // stack: inA3, B3, inA, inB, out, jumpdest
    %mload_bls
    // stack:   A3, B3, inA, inB, out, jumpdest
    %add_fp381
    // stack:       C3, inA, inB, out, jumpdest
    DUP5
    %add_const(6)
    // stack: out3, C3, inA, inB, out, jumpdest
    %mstore_bls

    // stack:           inA, inB, out, jumpdest
    DUP2
    %add_const(8)
    // stack:     inB4, inA, inB, out, jumpdest
    %mload_bls
    // stack:       B4, inA, inB, out, jumpdest
    DUP3
    %add_const(8)
    // stack: inA4, B4, inA, inB, out, jumpdest
    %mload_bls
    // stack:   A4, B4, inA, inB, out, jumpdest
    %add_fp381
    // stack:       C4, inA, inB, out, jumpdest
    DUP5
    %add_const(8)
    // stack: out4, C4, inA, inB, out, jumpdest
    %mstore_bls
    
    // stack:           inA, inB, out, jumpdest
    DUP2
    %add_const(10)
    // stack:     inB5, inA, inB, out, jumpdest
    %mload_bls
    // stack:       B5, inA, inB, out, jumpdest
    DUP3
    %add_const(10)
    // stack: inA5, B5, inA, inB, out, jumpdest
    %mload_bls
    // stack:   A5, B5, inA, inB, out, jumpdest
    %add_fp381
    // stack:       C5, inA, inB, out, jumpdest
    DUP5
    %add_const(10)
    // stack: out5, C5, inA, inB, out, jumpdest
    %mstore_bls
    
    // stack:           inA, inB, out, jumpdest
    %pop3
    JUMP
