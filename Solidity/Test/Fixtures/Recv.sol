// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

// receive and fallback: which one runs for empty calldata, short calldata and unknown selectors,
// with and without value; a fallback that takes the calldata and returns bytes.

contract RecvFb {
  uint256 public got;
  uint256 public fb;
  bytes public data;
  receive() external payable { got += msg.value + 1; }
  fallback() external payable { fb += msg.value + 1; data = msg.data; }
  function f(uint256 x) external pure returns (uint256) { return x + 1; }
}

contract FbOnly {
  uint256 public fb;
  fallback() external { fb += 1; }
  function f() external pure returns (uint256) { return 7; }
}

contract FbData {
  uint256 public n;
  fallback(bytes calldata input) external payable returns (bytes memory) {
    n += 1;
    return abi.encodePacked(input, uint8(n));
  }
}

contract RecvOnly {
  uint256 public got;
  receive() external payable { got += 1; }
  function g(uint256 x) external payable returns (uint256) { return x; }
}

contract NoFb {
  function g(uint256 x) external pure returns (uint256) { return x; }
}
