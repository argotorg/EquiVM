// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/// @title Ripemd160
/// @notice Pure Solidity implementation of RIPEMD-160.
/// @dev Assembly-optimized. Two parallel computation paths with 80 rounds each.
///      Paths are computed sequentially to avoid stack-too-deep.
library Ripemd160 {
    /// @notice Computes the RIPEMD-160 hash of the input data.
    /// @param data The input data to hash.
    /// @return result The 20-byte RIPEMD-160 digest.
    function hash(bytes memory data) internal pure returns (bytes20 result) {
        assembly {
            let MASK32 := 0xffffffff

            // ── RIPEMD-160 boolean functions ─────────────────────
            function f0(x, y, z) -> r { r := xor(xor(x, y), z) }
            function f1(x, y, z) -> r { r := or(and(x, y), and(not(x), z)) }
            function f2(x, y, z) -> r { r := xor(or(x, not(y)), z) }
            function f3(x, y, z) -> r { r := or(and(x, z), and(y, not(z))) }
            function f4(x, y, z) -> r { r := xor(x, or(y, not(z))) }

            // ── rotl32 ──────────────────────────────────────────
            function rotl32(x, n) -> r {
                r := and(or(shl(n, x), shr(sub(32, n), x)), 0xffffffff)
            }

            // ── Left round: computes one step, reads/writes state from memory
            // stPtr points to 5 words: a, b, c, d, e (32-byte stride)
            function leftRound(stPtr, xPtr, j) {
                let M32 := 0xffffffff
                let a := mload(stPtr)
                let b := mload(add(stPtr, 0x20))
                let c := mload(add(stPtr, 0x40))
                let d := mload(add(stPtr, 0x60))
                let e := mload(add(stPtr, 0x80))

                let group := div(j, 16)
                let fVal
                let kl
                switch group
                case 0 { fVal := xor(xor(b, c), d) kl := 0x00000000 }
                case 1 { fVal := or(and(b, c), and(not(b), d)) kl := 0x5a827999 }
                case 2 { fVal := xor(or(b, not(c)), d) kl := 0x6ed9eba1 }
                case 3 { fVal := or(and(b, d), and(c, not(d))) kl := 0x8f1bbcdc }
                case 4 { fVal := xor(b, or(c, not(d))) kl := 0xa953fd4e }

                // word selection rL
                let ri
                if lt(j, 16) { ri := j }
                if and(gt(j, 15), lt(j, 32)) {
                    // rL[16..31]
                    let idx := sub(j, 16)
                    // 7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8
                    switch idx
                    case  0 { ri :=  7 } case  1 { ri :=  4 } case  2 { ri := 13 } case  3 { ri :=  1 }
                    case  4 { ri := 10 } case  5 { ri :=  6 } case  6 { ri := 15 } case  7 { ri :=  3 }
                    case  8 { ri := 12 } case  9 { ri :=  0 } case 10 { ri :=  9 } case 11 { ri :=  5 }
                    case 12 { ri :=  2 } case 13 { ri := 14 } case 14 { ri := 11 } case 15 { ri :=  8 }
                }
                if and(gt(j, 31), lt(j, 48)) {
                    let idx := sub(j, 32)
                    switch idx
                    case  0 { ri :=  3 } case  1 { ri := 10 } case  2 { ri := 14 } case  3 { ri :=  4 }
                    case  4 { ri :=  9 } case  5 { ri := 15 } case  6 { ri :=  8 } case  7 { ri :=  1 }
                    case  8 { ri :=  2 } case  9 { ri :=  7 } case 10 { ri :=  0 } case 11 { ri :=  6 }
                    case 12 { ri := 13 } case 13 { ri := 11 } case 14 { ri :=  5 } case 15 { ri := 12 }
                }
                if and(gt(j, 47), lt(j, 64)) {
                    let idx := sub(j, 48)
                    switch idx
                    case  0 { ri :=  1 } case  1 { ri :=  9 } case  2 { ri := 11 } case  3 { ri := 10 }
                    case  4 { ri :=  0 } case  5 { ri :=  8 } case  6 { ri := 12 } case  7 { ri :=  4 }
                    case  8 { ri := 13 } case  9 { ri :=  3 } case 10 { ri :=  7 } case 11 { ri := 15 }
                    case 12 { ri := 14 } case 13 { ri :=  5 } case 14 { ri :=  6 } case 15 { ri :=  2 }
                }
                if gt(j, 63) {
                    let idx := sub(j, 64)
                    switch idx
                    case  0 { ri :=  4 } case  1 { ri :=  0 } case  2 { ri :=  5 } case  3 { ri :=  9 }
                    case  4 { ri :=  7 } case  5 { ri := 12 } case  6 { ri :=  2 } case  7 { ri := 10 }
                    case  8 { ri := 14 } case  9 { ri :=  1 } case 10 { ri :=  3 } case 11 { ri :=  8 }
                    case 12 { ri := 11 } case 13 { ri :=  6 } case 14 { ri := 15 } case 15 { ri := 13 }
                }

                // rotation amounts sL
                let si
                // Encoded as packed bytes per group: 16 rotation amounts each
                switch group
                case 0 {
                    // 11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8
                    let idx := mod(j, 16)
                    switch idx
                    case  0 { si := 11 } case  1 { si := 14 } case  2 { si := 15 } case  3 { si := 12 }
                    case  4 { si :=  5 } case  5 { si :=  8 } case  6 { si :=  7 } case  7 { si :=  9 }
                    case  8 { si := 11 } case  9 { si := 13 } case 10 { si := 14 } case 11 { si := 15 }
                    case 12 { si :=  6 } case 13 { si :=  7 } case 14 { si :=  9 } case 15 { si :=  8 }
                }
                case 1 {
                    let idx := mod(j, 16)
                    switch idx
                    case  0 { si :=  7 } case  1 { si :=  6 } case  2 { si :=  8 } case  3 { si := 13 }
                    case  4 { si := 11 } case  5 { si :=  9 } case  6 { si :=  7 } case  7 { si := 15 }
                    case  8 { si :=  7 } case  9 { si := 12 } case 10 { si := 15 } case 11 { si :=  9 }
                    case 12 { si := 11 } case 13 { si :=  7 } case 14 { si := 13 } case 15 { si := 12 }
                }
                case 2 {
                    let idx := mod(j, 16)
                    switch idx
                    case  0 { si := 11 } case  1 { si := 13 } case  2 { si :=  6 } case  3 { si :=  7 }
                    case  4 { si := 14 } case  5 { si :=  9 } case  6 { si := 13 } case  7 { si := 15 }
                    case  8 { si := 14 } case  9 { si :=  8 } case 10 { si := 13 } case 11 { si :=  6 }
                    case 12 { si :=  5 } case 13 { si := 12 } case 14 { si :=  7 } case 15 { si :=  5 }
                }
                case 3 {
                    let idx := mod(j, 16)
                    switch idx
                    case  0 { si := 11 } case  1 { si := 12 } case  2 { si := 14 } case  3 { si := 15 }
                    case  4 { si := 14 } case  5 { si := 15 } case  6 { si :=  9 } case  7 { si :=  8 }
                    case  8 { si :=  9 } case  9 { si := 14 } case 10 { si :=  5 } case 11 { si :=  6 }
                    case 12 { si :=  8 } case 13 { si :=  6 } case 14 { si :=  5 } case 15 { si := 12 }
                }
                case 4 {
                    let idx := mod(j, 16)
                    switch idx
                    case  0 { si :=  9 } case  1 { si := 15 } case  2 { si :=  5 } case  3 { si := 11 }
                    case  4 { si :=  6 } case  5 { si :=  8 } case  6 { si := 13 } case  7 { si := 12 }
                    case  8 { si :=  5 } case  9 { si := 12 } case 10 { si := 13 } case 11 { si := 14 }
                    case 12 { si := 11 } case 13 { si :=  8 } case 14 { si :=  5 } case 15 { si :=  6 }
                }

                let w := mload(add(xPtr, mul(ri, 0x20)))
                let tVal := and(add(add(add(a, and(fVal, M32)), w), kl), M32)
                tVal := and(add(rotl32(tVal, si), e), M32)

                mstore(stPtr, e)                    // a = e
                mstore(add(stPtr, 0x80), d)         // e = d
                mstore(add(stPtr, 0x60), rotl32(c, 10)) // d = rotl32(c, 10)
                mstore(add(stPtr, 0x40), b)         // c = b
                mstore(add(stPtr, 0x20), tVal)      // b = tVal
            }

            // ── Right round: same structure but with right-path tables
            function rightRound(stPtr, xPtr, j) {
                let M32 := 0xffffffff
                let a := mload(stPtr)
                let b := mload(add(stPtr, 0x20))
                let c := mload(add(stPtr, 0x40))
                let d := mload(add(stPtr, 0x60))
                let e := mload(add(stPtr, 0x80))

                let group := div(j, 16)
                let fVal
                let kr
                switch group
                case 0 { fVal := xor(b, or(c, not(d))) kr := 0x50a28be6 }
                case 1 { fVal := or(and(b, d), and(c, not(d))) kr := 0x5c4dd124 }
                case 2 { fVal := xor(or(b, not(c)), d) kr := 0x6d703ef3 }
                case 3 { fVal := or(and(b, c), and(not(b), d)) kr := 0x7a6d76e9 }
                case 4 { fVal := xor(xor(b, c), d) kr := 0x00000000 }

                // word selection rR
                let ri
                switch group
                case 0 {
                    let idx := mod(j, 16)
                    switch idx
                    case  0 { ri :=  5 } case  1 { ri := 14 } case  2 { ri :=  7 } case  3 { ri :=  0 }
                    case  4 { ri :=  9 } case  5 { ri :=  2 } case  6 { ri := 11 } case  7 { ri :=  4 }
                    case  8 { ri := 13 } case  9 { ri :=  6 } case 10 { ri := 15 } case 11 { ri :=  8 }
                    case 12 { ri :=  1 } case 13 { ri := 10 } case 14 { ri :=  3 } case 15 { ri := 12 }
                }
                case 1 {
                    let idx := mod(j, 16)
                    switch idx
                    case  0 { ri :=  6 } case  1 { ri := 11 } case  2 { ri :=  3 } case  3 { ri :=  7 }
                    case  4 { ri :=  0 } case  5 { ri := 13 } case  6 { ri :=  5 } case  7 { ri := 10 }
                    case  8 { ri := 14 } case  9 { ri := 15 } case 10 { ri :=  8 } case 11 { ri := 12 }
                    case 12 { ri :=  4 } case 13 { ri :=  9 } case 14 { ri :=  1 } case 15 { ri :=  2 }
                }
                case 2 {
                    let idx := mod(j, 16)
                    switch idx
                    case  0 { ri := 15 } case  1 { ri :=  5 } case  2 { ri :=  1 } case  3 { ri :=  3 }
                    case  4 { ri :=  7 } case  5 { ri := 14 } case  6 { ri :=  6 } case  7 { ri :=  9 }
                    case  8 { ri := 11 } case  9 { ri :=  8 } case 10 { ri := 12 } case 11 { ri :=  2 }
                    case 12 { ri := 10 } case 13 { ri :=  0 } case 14 { ri :=  4 } case 15 { ri := 13 }
                }
                case 3 {
                    let idx := mod(j, 16)
                    switch idx
                    case  0 { ri :=  8 } case  1 { ri :=  6 } case  2 { ri :=  4 } case  3 { ri :=  1 }
                    case  4 { ri :=  3 } case  5 { ri := 11 } case  6 { ri := 15 } case  7 { ri :=  0 }
                    case  8 { ri :=  5 } case  9 { ri := 12 } case 10 { ri :=  2 } case 11 { ri := 13 }
                    case 12 { ri :=  9 } case 13 { ri :=  7 } case 14 { ri := 10 } case 15 { ri := 14 }
                }
                case 4 {
                    let idx := mod(j, 16)
                    switch idx
                    case  0 { ri := 12 } case  1 { ri := 15 } case  2 { ri := 10 } case  3 { ri :=  4 }
                    case  4 { ri :=  1 } case  5 { ri :=  5 } case  6 { ri :=  8 } case  7 { ri :=  7 }
                    case  8 { ri :=  6 } case  9 { ri :=  2 } case 10 { ri := 13 } case 11 { ri := 14 }
                    case 12 { ri :=  0 } case 13 { ri :=  3 } case 14 { ri :=  9 } case 15 { ri := 11 }
                }

                // rotation amounts sR
                let si
                switch group
                case 0 {
                    let idx := mod(j, 16)
                    switch idx
                    case  0 { si :=  8 } case  1 { si :=  9 } case  2 { si :=  9 } case  3 { si := 11 }
                    case  4 { si := 13 } case  5 { si := 15 } case  6 { si := 15 } case  7 { si :=  5 }
                    case  8 { si :=  7 } case  9 { si :=  7 } case 10 { si :=  8 } case 11 { si := 11 }
                    case 12 { si := 14 } case 13 { si := 14 } case 14 { si := 12 } case 15 { si :=  6 }
                }
                case 1 {
                    let idx := mod(j, 16)
                    switch idx
                    case  0 { si :=  9 } case  1 { si := 13 } case  2 { si := 15 } case  3 { si :=  7 }
                    case  4 { si := 12 } case  5 { si :=  8 } case  6 { si :=  9 } case  7 { si := 11 }
                    case  8 { si :=  7 } case  9 { si :=  7 } case 10 { si := 12 } case 11 { si :=  7 }
                    case 12 { si :=  6 } case 13 { si := 15 } case 14 { si := 13 } case 15 { si := 11 }
                }
                case 2 {
                    let idx := mod(j, 16)
                    switch idx
                    case  0 { si :=  9 } case  1 { si :=  7 } case  2 { si := 15 } case  3 { si := 11 }
                    case  4 { si :=  8 } case  5 { si :=  6 } case  6 { si :=  6 } case  7 { si := 14 }
                    case  8 { si := 12 } case  9 { si := 13 } case 10 { si :=  5 } case 11 { si := 14 }
                    case 12 { si := 13 } case 13 { si := 13 } case 14 { si :=  7 } case 15 { si :=  5 }
                }
                case 3 {
                    let idx := mod(j, 16)
                    switch idx
                    case  0 { si := 15 } case  1 { si :=  5 } case  2 { si :=  8 } case  3 { si := 11 }
                    case  4 { si := 14 } case  5 { si := 14 } case  6 { si :=  6 } case  7 { si := 14 }
                    case  8 { si :=  6 } case  9 { si :=  9 } case 10 { si := 12 } case 11 { si :=  9 }
                    case 12 { si := 12 } case 13 { si :=  5 } case 14 { si := 15 } case 15 { si :=  8 }
                }
                case 4 {
                    let idx := mod(j, 16)
                    switch idx
                    case  0 { si :=  8 } case  1 { si :=  5 } case  2 { si := 12 } case  3 { si :=  9 }
                    case  4 { si := 12 } case  5 { si :=  5 } case  6 { si := 14 } case  7 { si :=  6 }
                    case  8 { si :=  8 } case  9 { si := 13 } case 10 { si :=  6 } case 11 { si :=  5 }
                    case 12 { si := 15 } case 13 { si := 13 } case 14 { si := 11 } case 15 { si := 11 }
                }

                let w := mload(add(xPtr, mul(ri, 0x20)))
                let tVal := and(add(add(add(a, and(fVal, M32)), w), kr), M32)
                tVal := and(add(rotl32(tVal, si), e), M32)

                mstore(stPtr, e)
                mstore(add(stPtr, 0x80), d)
                mstore(add(stPtr, 0x60), rotl32(c, 10))
                mstore(add(stPtr, 0x40), b)
                mstore(add(stPtr, 0x20), tVal)
            }

            // ── Padding (same as MD but little-endian length) ───
            let dataLen := mload(data)
            let dataPtr := add(data, 0x20)
            let bitLen := mul(dataLen, 8)
            let paddedLen := and(add(add(dataLen, 9), 63), not(63))

            let padBuf := mload(0x40)
            mstore(0x40, add(padBuf, paddedLen))

            // Copy data
            let i := 0
            for {} lt(i, dataLen) { i := add(i, 0x20) } {
                mstore(add(padBuf, i), mload(add(dataPtr, i)))
            }
            // Zero the rest
            for { let j := i } lt(j, paddedLen) { j := add(j, 0x20) } {
                mstore(add(padBuf, j), 0)
            }
            // 0x80 byte
            mstore8(add(padBuf, dataLen), 0x80)

            // Little-endian 64-bit bit length at end
            let bitLenLo := and(bitLen, MASK32)
            let bitLenHi := shr(32, bitLen)
            mstore8(add(padBuf, sub(paddedLen, 8)), and(bitLenLo, 0xff))
            mstore8(add(padBuf, sub(paddedLen, 7)), and(shr(8, bitLenLo), 0xff))
            mstore8(add(padBuf, sub(paddedLen, 6)), and(shr(16, bitLenLo), 0xff))
            mstore8(add(padBuf, sub(paddedLen, 5)), and(shr(24, bitLenLo), 0xff))
            mstore8(add(padBuf, sub(paddedLen, 4)), and(bitLenHi, 0xff))
            mstore8(add(padBuf, sub(paddedLen, 3)), and(shr(8, bitLenHi), 0xff))
            mstore8(add(padBuf, sub(paddedLen, 2)), and(shr(16, bitLenHi), 0xff))
            mstore8(add(padBuf, sub(paddedLen, 1)), and(shr(24, bitLenHi), 0xff))

            // ── Initialize hash values ──────────────────────────
            let h0 := 0x67452301
            let h1 := 0xefcdab89
            let h2 := 0x98badcfe
            let h3 := 0x10325476
            let h4 := 0xc3d2e1f0

            // ── Allocate word buffer X[0..15] and state buffers ─
            let xPtr := mload(0x40)
            let leftSt := add(xPtr, 512)   // 5 words for left path state
            let rightSt := add(leftSt, 160) // 5 words for right path state
            mstore(0x40, add(rightSt, 160))

            // ── Process each 64-byte block ──────────────────────
            let numBlocks := div(paddedLen, 64)
            for { let blk := 0 } lt(blk, numBlocks) { blk := add(blk, 1) } {
                let blockPtr := add(padBuf, mul(blk, 64))

                // Parse 16 little-endian 32-bit words
                for { let t := 0 } lt(t, 16) { t := add(t, 1) } {
                    let off := add(blockPtr, mul(t, 4))
                    let w := or(
                        or(byte(0, mload(off)),
                           shl(8, byte(0, mload(add(off, 1))))),
                        or(shl(16, byte(0, mload(add(off, 2)))),
                           shl(24, byte(0, mload(add(off, 3)))))
                    )
                    mstore(add(xPtr, mul(t, 0x20)), w)
                }

                // Initialize left path state
                mstore(leftSt, h0)
                mstore(add(leftSt, 0x20), h1)
                mstore(add(leftSt, 0x40), h2)
                mstore(add(leftSt, 0x60), h3)
                mstore(add(leftSt, 0x80), h4)

                // Left path: 80 rounds
                for { let j := 0 } lt(j, 80) { j := add(j, 1) } {
                    leftRound(leftSt, xPtr, j)
                }

                // Initialize right path state
                mstore(rightSt, h0)
                mstore(add(rightSt, 0x20), h1)
                mstore(add(rightSt, 0x40), h2)
                mstore(add(rightSt, 0x60), h3)
                mstore(add(rightSt, 0x80), h4)

                // Right path: 80 rounds
                for { let j := 0 } lt(j, 80) { j := add(j, 1) } {
                    rightRound(rightSt, xPtr, j)
                }

                // Read final states
                let al := mload(leftSt)
                let bl := mload(add(leftSt, 0x20))
                let cl := mload(add(leftSt, 0x40))
                let dl := mload(add(leftSt, 0x60))
                let el := mload(add(leftSt, 0x80))

                let ar := mload(rightSt)
                let br := mload(add(rightSt, 0x20))
                let cr := mload(add(rightSt, 0x40))
                let dr := mload(add(rightSt, 0x60))
                let er := mload(add(rightSt, 0x80))

                // Final addition (cyclic)
                let t0 := and(add(add(h1, cl), dr), MASK32)
                h1 := and(add(add(h2, dl), er), MASK32)
                h2 := and(add(add(h3, el), ar), MASK32)
                h3 := and(add(add(h4, al), br), MASK32)
                h4 := and(add(add(h0, bl), cr), MASK32)
                h0 := t0
            }

            // ── Produce 20-byte result (bytes20 is left-aligned) ─
            // RIPEMD-160 output is 5 little-endian 32-bit words
            // bytes20 packs them big-endian, so byte-swap each word
            function swap32(x) -> r {
                r := or(
                    or(shl(24, and(x, 0xff)), shl(16, and(shr(8, x), 0xff))),
                    or(shl(8, and(shr(16, x), 0xff)), and(shr(24, x), 0xff))
                )
            }

            let r0 := swap32(h0)
            let r1 := swap32(h1)
            let r2 := swap32(h2)
            let r3 := swap32(h3)
            let r4 := swap32(h4)

            // Pack into bytes20 (left-aligned in bytes32): shift left by 96 bits
            result := shl(96, or(shl(128, r0), or(shl(96, r1), or(shl(64, r2), or(shl(32, r3), r4)))))
        }
    }
}
