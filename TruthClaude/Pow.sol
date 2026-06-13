// SPDX-License-Identifier: MIT
// pragma must match how `truthBytecode` was produced (PUSH0 ⇒ Shanghai+; optimizer OFF).
pragma solidity ^0.8.20;

contract Pow {
    // Computes 2^n.
    //
    // `require(n < 256)` is deliberate, not incidental: the Act model's arithmetic is
    // *unbounded* `Int` (it does not wrap mod 2^256), so an `unchecked` `2^n` that wraps in the
    // EVM would diverge from the spec for n >= 256 (and the ABI encoder would reject the
    // out-of-range spec value). Guarding n < 256 keeps `2^n < 2^256`, so EVM-wrapping and
    // Act-unbounded arithmetic agree exactly; for n >= 256 *both* revert. `unchecked` then keeps
    // the loop body free of overflow-check branches (safe, since the require rules overflow out).
    //
    // `public pure` ⇒ solc emits the non-payable guard (CALLVALUE; ISZERO; …) we already handle.
    function pow2(uint256 n) public pure returns (uint256) {
        require(n < 256);
        uint256 r = 1;
        uint256 i = 0;
        while (i < n) {
            unchecked {
                r *= 2;
                i += 1;
            }
        }
        return r;
    }
}
