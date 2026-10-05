// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

// Calldata arrays and structs whose words are not canonical: solc validates a word when it is
// read, when the object is ABI-encoded (`abi.encode`, an external call, an event, an error, a
// calldata-typed return) and when a struct or a nested array is copied to memory; an array of
// value-type words is copied to memory with cleanup (mask, sign extension, `bool` non-zero).
// `Attach`: a library function attached to an interface type with `using`.  `Known`: the shapes
// the spec deviates on (see the scenario).

interface IT { function total() external view returns (uint256); }

library Lib {
  function twice(IT t) internal view returns (uint256) { return 2 * t.total(); }
  function plus(uint256 a, uint256 b) internal pure returns (uint256) { return a + b; }
}

contract Tok is IT { function total() external pure returns (uint256) { return 5; } }

contract Attach {
  using Lib for IT;
  using Lib for uint256;
  function viaMember(IT t) external view returns (uint256) { return t.twice(); }
  function viaLib(IT t) external view returns (uint256) { return Lib.twice(t); }
  function own(IT t) external view returns (uint256) { return t.total(); }
  function num(uint256 x) external pure returns (uint256) { return x.plus(1); }
}

struct S { uint8 x; uint256 y; }
enum E { A, B, C }
type P is uint128;

contract Copies {
  uint16[] public store;
  event Arr(uint16[] xs);
  error Bad(uint16[] xs);

  function pass(uint128[] calldata xs) external pure returns (uint128[] memory) { return xs; }
  function enc(uint16[] calldata xs) external pure returns (bytes memory) { return abi.encode(xs); }
  function packed(uint16[] calldata xs) external pure returns (bytes memory) { return abi.encodePacked(xs); }
  function hashIt(uint16[] calldata xs) external pure returns (bytes32) { return keccak256(abi.encode(xs)); }
  function copyLen(uint16[] calldata xs) external pure returns (uint256) { uint16[] memory m = xs; return m.length; }
  function copyAdd(uint16[] calldata xs) external pure returns (uint16) { uint16[] memory m = xs; return m[1] + 1; }
  function copyEnc(uint16[] calldata xs) external pure returns (bytes memory) { uint16[] memory m = xs; return abi.encode(m); }
  function copyEq(uint16[] calldata xs) external pure returns (bool) { uint16[] memory m = xs; return m[1] == 0; }
  function copyBool(bool[] calldata bs) external pure returns (bool) { bool[] memory m = bs; return m[1]; }
  function toStore(uint16[] calldata xs) external returns (uint256) { store = xs; return store.length; }
  function fwd(uint16[] calldata xs) external view returns (uint256) { return this.len(xs); }
  function len(uint16[] calldata xs) external pure returns (uint256) { return xs.length; }
  function first(uint16[] calldata xs) external pure returns (uint16) { return xs[0]; }
  function memLen(uint16[] memory xs) external pure returns (uint256) { return xs.length; }
  function emitArr(uint16[] calldata xs) external { emit Arr(xs); }
  function revertArr(uint16[] calldata xs) external pure { revert Bad(xs); }
  function fieldY(S calldata s) external pure returns (uint256) { return s.y; }
  function fieldX(S calldata s) external pure returns (uint8) { return s.x; }
  function structCopy(S calldata s) external pure returns (uint8) { S memory t = s; return t.x; }
  function structEnc(S calldata s) external pure returns (bytes memory) { return abi.encode(s); }
  function ssY(S[] calldata ss, uint256 i) external pure returns (uint256) { return ss[i].y; }
  function ssX(S[] calldata ss, uint256 i) external pure returns (uint8) { return ss[i].x; }
  function ssCopy(S[] calldata ss) external pure returns (uint256) { S[] memory m = ss; return m.length; }
  function fixedOuter(uint8[2][] calldata xss, uint256 i) external pure returns (uint256) { return xss[i].length; }
  function fixedOuterCopy(uint8[2][] calldata xss) external pure returns (uint8) { uint8[2][] memory m = xss; return m[0][1]; }
  function fixedCopy(uint16[2] calldata xs) external pure returns (uint16) { uint16[2] memory m = xs; return m[1]; }
  function addrAt(address[] calldata xs, uint256 i) external pure returns (address) { return xs[i]; }
  function addrCopy(address[] calldata xs) external pure returns (address) { address[] memory m = xs; return m[0]; }
  function bytesAt(bytes4[] calldata xs, uint256 i) external pure returns (bytes4) { return xs[i]; }
  function bytesCopy(bytes4[] calldata xs) external pure returns (bytes4) { bytes4[] memory m = xs; return m[0]; }
  function intAt(int64[] calldata xs, uint256 i) external pure returns (int64) { return xs[i]; }
  function intCopy(int64[] calldata xs) external pure returns (int64) { int64[] memory m = xs; return m[0]; }
  function enumAt(E[] calldata es, uint256 i) external pure returns (E) { return es[i]; }
  function enumCopy(E[] calldata es) external pure returns (E) { E[] memory m = es; return m[0]; }
  function priceAt(P[] calldata ps, uint256 i) external pure returns (uint128) { return P.unwrap(ps[i]); }
  function priceCopy(P[] calldata ps) external pure returns (uint128) { P[] memory m = ps; return P.unwrap(m[0]); }
}

contract Known {
  function retCd(uint16[] calldata xs) external pure returns (uint16[] calldata) { return xs; }
  function enumCopyLen(E[] calldata es) external pure returns (uint256) { E[] memory m = es; return m.length; }
  function nested(uint8[][] calldata xss, uint256 i, uint256 j) external pure returns (uint8) { return xss[i][j]; }
  function nestedCopy(uint8[][] calldata xss) external pure returns (uint8) { uint8[][] memory m = xss; return m[0][0]; }
}
