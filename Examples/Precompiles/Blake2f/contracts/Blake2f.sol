// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/// @title Blake2f
/// @notice Pure Solidity implementation of the BLAKE2b F compression function (EIP-152).
/// @dev Assembly-optimized. Working vector uses 32-byte stride matching Solidity array layout.
///
/// Experiment source note:
/// Copied from `/home/lefteris/evmification/src/blake2f/Blake2f.sol`.
/// The raw `compress(bytes)` entrypoint has been tightened to match the trusted
/// EIP-152 model in `/home/lefteris/evm-semantics/EvmSemantics/EVM/Precompile.lean`:
/// the final-block flag byte must be exactly 0 or 1. The upstream copy accepted
/// any nonzero byte as `true`, which does not match `runBlake2f`.
library Blake2f {
    /// @notice Computes the BLAKE2b F compression function.
    /// @param rounds Number of rounds (0..2^32-1).
    /// @param h State vector (8 uint64 values).
    /// @param m Message block (16 uint64 values).
    /// @param t Offset counters (2 uint64 values).
    /// @param finalBlock True if this is the final block.
    /// @return result The updated state vector (8 uint64 values).
    function compress(
        uint32 rounds,
        uint64[8] memory h,
        uint64[16] memory m,
        uint64[2] memory t,
        bool finalBlock
    ) internal pure returns (uint64[8] memory result) {
        assembly {
            let MASK64 := 0xffffffffffffffff

            // ── IV constants ──────────────────────────────
            // BLAKE2b initialization vectors
            let iv0 := 0x6a09e667f3bcc908
            let iv1 := 0xbb67ae8584caa73b
            let iv2 := 0x3c6ef372fe94f82b
            let iv3 := 0xa54ff53a5f1d36f1
            let iv4 := 0x510e527fade682d1
            let iv5 := 0x9b05688c2b3e6c1f
            let iv6 := 0x1f83d9abfb41bd6b
            let iv7 := 0x5be0cd19137e2179

            // ── Sigma table (10 rows, packed as uint64: 16 nibbles each) ──
            // Each row encodes 16 indices (0-15) as 4-bit nibbles, MSB first.
            // sigma[r][j] = (sigmaRow >> (60 - j*4)) & 0xf
            function sigmaRow(r) -> s {
                switch r
                case 0 { s := 0x0123456789abcdef }
                case 1 { s := 0xea489fd61c02b753 }
                case 2 { s := 0xb8c052fdae367194 }
                case 3 { s := 0x7931dcbe265a40f8 }
                case 4 { s := 0x905724afe1bc683d }
                case 5 { s := 0x2c6a0b834d75fe19 }
                case 6 { s := 0xc51fed4a0763928b }
                case 7 { s := 0xdb7ec13950f4862a }
                case 8 { s := 0x6fe9b308c2d714a5 }
                case 9 { s := 0xa2847615fb9e3cd0 }
                default { revert(0, 0) }
            }

            // ── Allocate working vector v[0..15] in memory (32-byte stride) ──
            let vPtr := mload(0x40)
            mstore(0x40, add(vPtr, 512)) // 16 * 32 bytes

            // v[0..7] = h[0..7]
            for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                mstore(add(vPtr, mul(i, 0x20)), and(mload(add(h, mul(i, 0x20))), MASK64))
            }

            // v[8..15] = IV[0..7]
            mstore(add(vPtr, mul(8, 0x20)), iv0)
            mstore(add(vPtr, mul(9, 0x20)), iv1)
            mstore(add(vPtr, mul(10, 0x20)), iv2)
            mstore(add(vPtr, mul(11, 0x20)), iv3)
            mstore(add(vPtr, mul(12, 0x20)), iv4)
            mstore(add(vPtr, mul(13, 0x20)), iv5)
            mstore(add(vPtr, mul(14, 0x20)), iv6)
            mstore(add(vPtr, mul(15, 0x20)), iv7)

            // v[12] ^= t[0], v[13] ^= t[1]
            let t0 := and(mload(t), MASK64)
            let t1 := and(mload(add(t, 0x20)), MASK64)
            mstore(add(vPtr, mul(12, 0x20)), xor(mload(add(vPtr, mul(12, 0x20))), t0))
            mstore(add(vPtr, mul(13, 0x20)), xor(mload(add(vPtr, mul(13, 0x20))), t1))

            // if finalBlock: v[14] ^= 0xFFFFFFFFFFFFFFFF
            if finalBlock {
                mstore(add(vPtr, mul(14, 0x20)), xor(mload(add(vPtr, mul(14, 0x20))), MASK64))
            }

            // ── G mixing function ──────────────────────
            function G(aOff, bOff, cOff, dOff, x, y) {
                let M := 0xffffffffffffffff
                let va := mload(aOff)
                let vb := mload(bOff)
                let vc := mload(cOff)
                let vd := mload(dOff)
                va := and(add(add(va, vb), x), M)
                vd := xor(vd, va)
                vd := and(or(shr(32, vd), shl(32, vd)), M)
                vc := and(add(vc, vd), M)
                vb := xor(vb, vc)
                vb := and(or(shr(24, vb), shl(40, vb)), M)
                va := and(add(add(va, vb), y), M)
                vd := xor(vd, va)
                vd := and(or(shr(16, vd), shl(48, vd)), M)
                vc := and(add(vc, vd), M)
                vb := xor(vb, vc)
                vb := and(or(shr(63, vb), shl(1, vb)), M)
                mstore(aOff, va) mstore(bOff, vb) mstore(cOff, vc) mstore(dOff, vd)
            }

            // Helper: load message word from sigma index
            function msg(mPtr, sr, hi, lo) -> x, y {
                x := and(mload(add(mPtr, mul(and(shr(hi, sr), 0xf), 0x20))), 0xffffffffffffffff)
                y := and(mload(add(mPtr, mul(and(shr(lo, sr), 0xf), 0x20))), 0xffffffffffffffff)
            }

            // ── Rounds ──────────────────────────────────
            for { let r := 0 } lt(r, rounds) { r := add(r, 1) } {
                let sr := sigmaRow(mod(r, 10))

                // Column step
                let x, y
                x, y := msg(m, sr, 60, 56)
                G(vPtr,                    add(vPtr, mul(4, 0x20)),  add(vPtr, mul(8, 0x20)),  add(vPtr, mul(12, 0x20)), x, y)
                x, y := msg(m, sr, 52, 48)
                G(add(vPtr, mul(1, 0x20)), add(vPtr, mul(5, 0x20)),  add(vPtr, mul(9, 0x20)),  add(vPtr, mul(13, 0x20)), x, y)
                x, y := msg(m, sr, 44, 40)
                G(add(vPtr, mul(2, 0x20)), add(vPtr, mul(6, 0x20)),  add(vPtr, mul(10, 0x20)), add(vPtr, mul(14, 0x20)), x, y)
                x, y := msg(m, sr, 36, 32)
                G(add(vPtr, mul(3, 0x20)), add(vPtr, mul(7, 0x20)),  add(vPtr, mul(11, 0x20)), add(vPtr, mul(15, 0x20)), x, y)

                // Diagonal step
                x, y := msg(m, sr, 28, 24)
                G(vPtr,                    add(vPtr, mul(5, 0x20)),  add(vPtr, mul(10, 0x20)), add(vPtr, mul(15, 0x20)), x, y)
                x, y := msg(m, sr, 20, 16)
                G(add(vPtr, mul(1, 0x20)), add(vPtr, mul(6, 0x20)),  add(vPtr, mul(11, 0x20)), add(vPtr, mul(12, 0x20)), x, y)
                x, y := msg(m, sr, 12, 8)
                G(add(vPtr, mul(2, 0x20)), add(vPtr, mul(7, 0x20)),  add(vPtr, mul(8, 0x20)),  add(vPtr, mul(13, 0x20)), x, y)
                x, y := msg(m, sr, 4, 0)
                G(add(vPtr, mul(3, 0x20)), add(vPtr, mul(4, 0x20)),  add(vPtr, mul(9, 0x20)),  add(vPtr, mul(14, 0x20)), x, y)
            }

            // Finalize: result[i] = h[i] ^ v[i] ^ v[i+8]
            for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                let hi := and(mload(add(h, mul(i, 0x20))), MASK64)
                let vi := mload(add(vPtr, mul(i, 0x20)))
                let vi8 := mload(add(vPtr, mul(add(i, 8), 0x20)))
                mstore(add(result, mul(i, 0x20)), and(xor(xor(hi, vi), vi8), MASK64))
            }
        }
    }

    /// @notice Computes the BLAKE2b F compression function from raw 213-byte EIP-152 input.
    /// @param input 213 bytes in EIP-152 format.
    /// @return output 64 bytes of output.
    function compress(bytes memory input) internal pure returns (bytes memory output) {
        require(input.length == 213, "Blake2f: invalid input length");

        uint32 rounds;
        uint64[8] memory h;
        uint64[16] memory m;
        uint64[2] memory t;
        uint8 finalFlag;
        bool finalBlock;

        assembly {
            function swap64(x) -> r {
                x := and(x, 0xffffffffffffffff)
                x := or(shl(8, and(x, 0x00FF00FF00FF00FF)), shr(8, and(x, 0xFF00FF00FF00FF00)))
                x := or(shl(16, and(x, 0x0000FFFF0000FFFF)), shr(16, and(x, 0xFFFF0000FFFF0000)))
                r := or(shl(32, and(x, 0x00000000FFFFFFFF)), shr(32, and(x, 0xFFFFFFFF00000000)))
            }

            let ptr := add(input, 0x20)

            // Parse rounds (4 bytes big-endian)
            rounds := shr(224, mload(ptr))

            // Parse h[0..7] (8 little-endian uint64s starting at offset 4)
            for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                let off := add(ptr, add(4, mul(i, 8)))
                mstore(add(h, mul(i, 0x20)), swap64(shr(192, mload(off))))
            }

            // Parse m[0..15] (16 little-endian uint64s starting at offset 68)
            for { let i := 0 } lt(i, 16) { i := add(i, 1) } {
                let off := add(ptr, add(68, mul(i, 8)))
                mstore(add(m, mul(i, 0x20)), swap64(shr(192, mload(off))))
            }

            // Parse t[0..1] (2 little-endian uint64s starting at offset 196)
            for { let i := 0 } lt(i, 2) { i := add(i, 1) } {
                let off := add(ptr, add(196, mul(i, 8)))
                mstore(add(t, mul(i, 0x20)), swap64(shr(192, mload(off))))
            }

            // Parse final-block flag (1 byte at offset 212).  EIP-152 accepts
            // only 0 or 1; other values are hard call failures in the native
            // precompile and in the trusted Lean model.
            finalFlag := shr(248, mload(add(ptr, 212)))
        }
        require(finalFlag <= 1, "Blake2f: invalid final flag");
        finalBlock = finalFlag == 1;

        uint64[8] memory res = compress(rounds, h, m, t, finalBlock);

        // Encode output as 64 bytes (8 little-endian uint64s)
        output = new bytes(64);
        assembly {
            function swap64(x) -> r {
                x := and(x, 0xffffffffffffffff)
                x := or(shl(8, and(x, 0x00FF00FF00FF00FF)), shr(8, and(x, 0xFF00FF00FF00FF00)))
                x := or(shl(16, and(x, 0x0000FFFF0000FFFF)), shr(16, and(x, 0xFFFF0000FFFF0000)))
                r := or(shl(32, and(x, 0x00000000FFFFFFFF)), shr(32, and(x, 0xFFFFFFFF00000000)))
            }

            let outPtr := add(output, 0x20)
            for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                mstore(add(outPtr, mul(i, 8)), shl(192, swap64(mload(add(res, mul(i, 0x20))))))
            }
        }
    }
}
