// SPDX-License-Identifier: MIT
// pragma must match how powBytecode was produced (PUSH0 ⇒ Shanghai+; optimizer OFF).
pragma solidity ^0.8.20;

interface IPow {
    function pow2(uint256 n) external returns (uint256);
}

contract Caller {
    uint256 stored; // slot 0

    // Calls an external Pow contract's pow2(n) and caches the result in storage.
    // `external` (not payable) ⇒ solc emits the CALLVALUE; ISZERO; … non-payable guard.
    function run(address t, uint256 n) external {
        stored = IPow(t).pow2(n);
    }
}
