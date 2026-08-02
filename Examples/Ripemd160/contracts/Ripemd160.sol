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

            // ── Packed lookup tables ────────────────────────────────
            // Each row: 16 nibbles packed MSB-first into a uint64.
            // Extract: value = (row >> (60 - idx*4)) & 0xf

            // Left word selection (rL) per group
            function wordRowL(g) -> r {
                switch g
                case 0 { r := 0x0123456789abcdef }
                case 1 { r := 0x74d1a6f3c0952eb8 }
                case 2 { r := 0x3ae49f812706db5c }
                case 3 { r := 0x19ba08c4d37fe562 }
                case 4 { r := 0x40597c2ae138b6fd }
            }
            // Left rotation amounts (sL) per group
            function rotRowL(g) -> r {
                switch g
                case 0 { r := 0xbefc5879bdef6798 }
                case 1 { r := 0x768db97f7cf9b7dc }
                case 2 { r := 0xbd67e9dfe8d65c75 }
                case 3 { r := 0xbcefef989e56865c }
                case 4 { r := 0x9f5b68dc5cdeb856 }
            }
            // Right word selection (rR) per group
            function wordRowR(g) -> r {
                switch g
                case 0 { r := 0x5e7092b4d6f81a3c }
                case 1 { r := 0x6b370d5aef8c4912 }
                case 2 { r := 0xf5137e69b8c2a04d }
                case 3 { r := 0x86413bf05c2d97ae }
                case 4 { r := 0xcfa4158762de039b }
            }
            // Right rotation amounts (sR) per group
            function rotRowR(g) -> r {
                switch g
                case 0 { r := 0x899bdff5778beec6 }
                case 1 { r := 0x9df7c89b77c76fdb }
                case 2 { r := 0x97fb866ecd5edd75 }
                case 3 { r := 0xf58bee6e69c9c5f8 }
                case 4 { r := 0x85c9c5e68d65fdbb }
            }

            // Extract nibble at position idx (0-15) from packed row
            function nibble(row, idx) -> v {
                v := and(shr(sub(60, mul(idx, 4)), row), 0xf)
            }

            // ── Unified round function ────────────────────────────
            function rmdRound(stPtr, xPtr, j, wordRow, rotRow, fVal, kk) {
                let M32 := 0xffffffff
                let a := mload(stPtr)
                let b := mload(add(stPtr, 0x20))
                let c := mload(add(stPtr, 0x40))
                let d := mload(add(stPtr, 0x60))
                let e := mload(add(stPtr, 0x80))

                let idx := mod(j, 16)
                let ri := nibble(wordRow, idx)
                let si := nibble(rotRow, idx)

                let w := mload(add(xPtr, mul(ri, 0x20)))
                let tVal := and(add(add(add(a, and(fVal, M32)), w), kk), M32)
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
            mcopy(padBuf, dataPtr, dataLen)
            let i := dataLen
            // Zero the rest
            for { let j := i } lt(j, paddedLen) { j := add(j, 0x20) } {
                mstore(add(padBuf, j), 0)
            }
            // 0x80 byte
            mstore8(add(padBuf, dataLen), 0x80)

            // Little-endian 64-bit bit length at end
            // Byte-swap the 64-bit value to little-endian and write
            function swap64le(x) -> r {
                x := or(shl(8, and(x, 0x00FF00FF00FF00FF)), shr(8, and(x, 0xFF00FF00FF00FF00)))
                x := or(shl(16, and(x, 0x0000FFFF0000FFFF)), shr(16, and(x, 0xFFFF0000FFFF0000)))
                r := or(shl(32, and(x, 0x00000000FFFFFFFF)), shr(32, and(x, 0xFFFFFFFF00000000)))
            }
            mstore(add(padBuf, sub(paddedLen, 8)), shl(192, swap64le(bitLen)))

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

                // Left path: 80 rounds (5 groups of 16)
                for { let g := 0 } lt(g, 5) { g := add(g, 1) } {
                    let wRow := wordRowL(g)
                    let rRow := rotRowL(g)
                    // k constants per group
                    let kk := 0x00000000
                    switch g
                    case 1 { kk := 0x5a827999 }
                    case 2 { kk := 0x6ed9eba1 }
                    case 3 { kk := 0x8f1bbcdc }
                    case 4 { kk := 0xa953fd4e }

                    for { let j := 0 } lt(j, 16) { j := add(j, 1) } {
                        let b := mload(add(leftSt, 0x20))
                        let c := mload(add(leftSt, 0x40))
                        let dd := mload(add(leftSt, 0x60))
                        let fVal
                        switch g
                        case 0 { fVal := f0(b, c, dd) }
                        case 1 { fVal := f1(b, c, dd) }
                        case 2 { fVal := f2(b, c, dd) }
                        case 3 { fVal := f3(b, c, dd) }
                        case 4 { fVal := f4(b, c, dd) }
                        rmdRound(leftSt, xPtr, j, wRow, rRow, fVal, kk)
                    }
                }

                // Initialize right path state
                mstore(rightSt, h0)
                mstore(add(rightSt, 0x20), h1)
                mstore(add(rightSt, 0x40), h2)
                mstore(add(rightSt, 0x60), h3)
                mstore(add(rightSt, 0x80), h4)

                // Right path: 80 rounds (5 groups of 16, f reversed)
                for { let g := 0 } lt(g, 5) { g := add(g, 1) } {
                    let wRow := wordRowR(g)
                    let rRow := rotRowR(g)
                    // k constants per group (right path)
                    let kk := 0x50a28be6
                    switch g
                    case 1 { kk := 0x5c4dd124 }
                    case 2 { kk := 0x6d703ef3 }
                    case 3 { kk := 0x7a6d76e9 }
                    case 4 { kk := 0x00000000 }

                    for { let j := 0 } lt(j, 16) { j := add(j, 1) } {
                        let b := mload(add(rightSt, 0x20))
                        let c := mload(add(rightSt, 0x40))
                        let dd := mload(add(rightSt, 0x60))
                        let fVal
                        switch g
                        case 0 { fVal := f4(b, c, dd) }
                        case 1 { fVal := f3(b, c, dd) }
                        case 2 { fVal := f2(b, c, dd) }
                        case 3 { fVal := f1(b, c, dd) }
                        case 4 { fVal := f0(b, c, dd) }
                        rmdRound(rightSt, xPtr, j, wRow, rRow, fVal, kk)
                    }
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
