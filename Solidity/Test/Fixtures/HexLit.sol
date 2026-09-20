// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

// Number literals converting to bytesN: zero always, hex literals only with exactly 2N digits.
contract HexLit {
  bytes2 public a;
  bytes32 public b;
  bytes1 public c;

  function set() external returns (bytes2, bytes32, bytes1) {
    a = 0x1234;
    b = 0x00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff;
    c = 0;
    return (a, b, c);
  }

  function cmp(bytes2 v) external pure returns (bool) {
    return v == 0x1234;
  }

  function conv() external pure returns (bytes2) {
    return bytes2(0x5678);
  }

  function pass() external pure returns (bytes2) {
    return g(0x0012);
  }

  function g(bytes2 v) internal pure returns (bytes2) {
    return v;
  }

  function zero() external pure returns (bytes4) {
    return 0;
  }
}
