// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

// Conditionals whose two branches have different types (or are both literals), used as an operand.
// solc gives the conditional the common type of the branches; the spec language has no static
// types and uses the type of the branch taken.  Kept apart from the fuzzed fixtures.

contract Cond {
  function ternArith(bool c, uint8 a, uint256 b) external pure returns (uint256) { return (c ? a : b) + 1; }
  function condTwoLits(bool c) external pure returns (uint256) { return (c ? 200 : 100) * 2; }
}
