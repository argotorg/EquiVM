// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

// ecrecover: precompile 1; an invalid signature yields address(0).
contract Ec {
  address public last;

  function rec(bytes32 h, uint8 v, bytes32 r, bytes32 s) external pure returns (address) {
    return ecrecover(h, v, r, s);
  }

  function recStore(bytes32 h, uint8 v, bytes32 r, bytes32 s) external {
    last = ecrecover(h, v, r, s);
  }

  function recNonZero(bytes32 h, uint8 v, bytes32 r, bytes32 s) external pure returns (address) {
    address a = ecrecover(h, v, r, s);
    require(a != address(0), "bad sig");
    return a;
  }
}
