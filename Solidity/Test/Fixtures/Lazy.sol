// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;
struct D { uint256 a; bytes b; }
// Calldata arrays and structs with dynamic content (`bytes[]`, `string[]`, `uint8[][]`, `D[]` for a
// struct `D` with a `bytes` field, `bytes[2]`, such a `D`): solc checks an element's offset and
// length when the element is used, copies to memory through its decoder (`Panic(0x41)` for an
// absurd length) and encodes through the element access.  The legacy pipeline cannot copy such an
// object to storage.
contract Lazy {
  event Ev(bytes[] d);
  function bLen(bytes[] calldata d) external pure returns (uint256) { return d.length; }
  function bAtLen(bytes[] calldata d, uint256 i) external pure returns (uint256) { return d[i].length; }
  function bAtByte(bytes[] calldata d, uint256 i, uint256 j) external pure returns (bytes1) { return d[i][j]; }
  function bCopy(bytes[] calldata d) external pure returns (uint256) { bytes[] memory m = d; return m.length; }
  function bCopyAt(bytes[] calldata d, uint256 i) external pure returns (uint256) { bytes[] memory m = d; return m[i].length; }
  function bEnc(bytes[] calldata d) external pure returns (bytes memory) { return abi.encode(d); }
  function bEmit(bytes[] calldata d) external { emit Ev(d); }
  function bFwd(bytes[] calldata d) external view returns (uint256) { return this.bLen(d); }
  function bPass(bytes[] calldata d) external pure returns (bytes[] memory) { return d; }
  function bInner(bytes[] calldata d, uint256 i) external pure returns (bytes memory) { return d[i]; }
  function bKeccak(bytes[] calldata d, uint256 i) external pure returns (bytes32) { return keccak256(d[i]); }
  function bInnerLocal(bytes[] calldata d, uint256 i) external pure returns (uint256) { bytes calldata x = d[i]; return x.length; }
  function sLen(string[] calldata d) external pure returns (uint256) { return d.length; }
  function sAt(string[] calldata d, uint256 i) external pure returns (uint256) { return bytes(d[i]).length; }
  function sCopy(string[] calldata d) external pure returns (uint256) { string[] memory m = d; return m.length; }
  function dLen(D[] calldata d) external pure returns (uint256) { return d.length; }
  function dA(D[] calldata d, uint256 i) external pure returns (uint256) { return d[i].a; }
  function dB(D[] calldata d, uint256 i) external pure returns (uint256) { return d[i].b.length; }
  function dCopy(D[] calldata d) external pure returns (uint256) { D[] memory m = d; return m.length; }
  function dEnc(D[] calldata d) external pure returns (bytes memory) { return abi.encode(d); }
  function d1A(D calldata s) external pure returns (uint256) { return s.a; }
  function d1B(D calldata s) external pure returns (uint256) { return s.b.length; }
  function d1Copy(D calldata s) external pure returns (uint256) { D memory t = s; return t.b.length; }
  function d1Enc(D calldata s) external pure returns (bytes memory) { return abi.encode(s); }
  function nLen(uint8[][] calldata x) external pure returns (uint256) { return x.length; }
  function nAt(uint8[][] calldata x, uint256 i) external pure returns (uint256) { return x[i].length; }
  function nAtAt(uint8[][] calldata x, uint256 i, uint256 j) external pure returns (uint8) { return x[i][j]; }
  function nCopy(uint8[][] calldata x) external pure returns (uint256) { uint8[][] memory m = x; return m.length; }
  function nCopyAt(uint8[][] calldata x, uint256 i) external pure returns (uint256) { uint8[][] memory m = x; return m[i].length; }
  function nEnc(uint8[][] calldata x) external pure returns (bytes memory) { return abi.encode(x); }
  function bbLen(bytes[][] calldata x) external pure returns (uint256) { return x.length; }
  function bbAt(bytes[][] calldata x, uint256 i) external pure returns (uint256) { return x[i].length; }
  function bbAtAt(bytes[][] calldata x, uint256 i, uint256 j) external pure returns (uint256) { return x[i][j].length; }
  function fbAt(bytes[2] calldata x, uint256 i) external pure returns (uint256) { return x[i].length; }
  function fbCopy(bytes[2] calldata x) external pure returns (uint256) { bytes[2] memory m = x; return m[1].length; }
}
