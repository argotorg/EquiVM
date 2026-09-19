// SPDX-License-Identifier: MIT
// Compiled with the OPTIMIZER ON (this is the realistic target):
//   solc --optimize --evm-version shanghai --bin-runtime C.sol
// `f` is a public function (external ABI entry) that is ALSO called internally by `g`.  solc emits
// `f`'s body once as a shared internal routine (tag_8), reached from both the external dispatch and
// `g`'s internal `JUMP` — confirmed shared even at --optimize-runs 1000000.  This is the
// "public-and-internally-called" reuse scenario: prove the body routine once, apply it at both the
// external-entry refinement and the internal-call refinement.
pragma solidity ^0.8.20;

contract C {
    uint256 s;

    // External entry AND internal call target.
    function f(uint256 v) public pure returns (uint256) {
        return v * 2 + 1;
    }

    function g(uint256 v) external {
        s = f(v); // internal JUMP into f's shared body routine (no CALL)
    }
}
