// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

// Memory allocation with a caller-chosen length: solc refuses more than 2^64 - 1 elements with
// Panic(0x41).  Kept apart from the fuzzed fixtures (large lengths are slow to interpret).

contract Alloc {
  function newWords(uint256 n) external pure returns (uint256) { uint256[] memory a = new uint256[](n); return a.length; }
  function newBytes(uint256 n) external pure returns (uint256) { bytes memory b = new bytes(n); return b.length; }
}
