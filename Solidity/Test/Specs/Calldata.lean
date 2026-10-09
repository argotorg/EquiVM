import Solidity.Notation

/-! Calldata (`Solidity/Test/Fixtures/Calldata.sol`).  Harness input only. -/

namespace Calldata.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def iT : SourceUnit := sol% interface IT { function total() external view returns (uint256); }

def lib : SourceUnit := sol% library Lib {
  function twice(IT t) internal view returns (uint256) { return 2 * t.total(); }
  function plus(uint256 a, uint256 b) internal pure returns (uint256) { return a + b; }
}

def tok : SourceUnit := sol% contract Tok is IT { function total() external pure returns (uint256) { return 5; } }

def attach : SourceUnit := sol% contract Attach {
  using Lib for IT;
  using Lib for uint256;
  function viaMember(IT t) external view returns (uint256) { return t.twice(); }
  function viaLib(IT t) external view returns (uint256) { return Lib.twice(t); }
  function own(IT t) external view returns (uint256) { return t.total(); }
  function num(uint256 x) external pure returns (uint256) { return x.plus(1); }
}

def sS : SourceUnit := sol% struct S { uint8 x; uint256 y; }

def eE : SourceUnit := sol% enum E { A, B, C }

def tP : SourceUnit := sol% type P is uint128;

def copies : SourceUnit := sol% contract Copies {
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
  function nested(uint8[][] calldata xss, uint256 i, uint256 j) external pure returns (uint8) { return xss[i][j]; }
  function nestedCopy(uint8[][] calldata xss) external pure returns (uint8) { uint8[][] memory m = xss; return m[0][0]; }
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
  function retCd(uint16[] calldata xs) external pure returns (uint16[] calldata) { return xs; }
}

def enums : SourceUnit := sol% contract Enums {
  event Ev(E[] m);
  E[] s;
  function copyRead(E[] calldata es, uint256 i) external pure returns (E) { E[] memory m = es; return m[i]; }
  function copyLen(E[] calldata es) external pure returns (uint256) { E[] memory m = es; return m.length; }
  function copyEnc(E[] calldata es) external pure returns (bytes memory) { E[] memory m = es; return abi.encode(m); }
  function copyPacked(E[] calldata es) external pure returns (bytes memory) { E[] memory m = es; return abi.encodePacked(m); }
  function copyEmit(E[] calldata es) external { E[] memory m = es; emit Ev(m); }
  function copyRet(E[] calldata es) external pure returns (E[] memory) { E[] memory m = es; return m; }
  function copyExt(E[] calldata es) external view returns (uint256) { E[] memory m = es; return this.copyLen(m); }
  function copyStore(E[] calldata es) external returns (uint256) { E[] memory m = es; s = m; return s.length; }
  function copyStoreRead(E[] calldata es, uint256 i) external returns (E) { E[] memory m = es; s = m; return s[i]; }
  function copyWriteRead(E[] calldata es) external pure returns (E) { E[] memory m = es; m[0] = E.B; return m[0]; }
  function copyDelete(E[] calldata es) external pure returns (uint256) { E[] memory m = es; delete m[0]; return uint256(m[0]); }
  function g(E[] memory p, uint256 i) internal pure returns (E) { return p[i]; }
  function copyInner(E[] calldata es, uint256 i) external pure returns (E) { E[] memory m = es; return g(m, i); }
  function copyCmp(E[] calldata es) external pure returns (bool) { E[] memory m = es; return m[0] == E.A; }
  function copyConv(E[] calldata es) external pure returns (uint8) { E[] memory m = es; return uint8(m[0]); }
  function copyShare(E[] calldata es) external pure returns (E) { E[] memory m = es; E[] memory m2 = m; m2[0] = E.B; return m[0]; }
  function copyStatic(E[2] calldata es, uint256 i) external pure returns (E) { E[2] memory m = es; return m[i]; }
  function copyStaticNoRead(E[2] calldata es) external pure returns (uint256) { E[2] memory m = es; m[0] = E.A; return 1; }
  function copyNested(E[2][] calldata es, uint256 i, uint256 j) external pure returns (E) { E[2][] memory m = es; return m[i][j]; }
  function copyNestedLen(E[2][] calldata es) external pure returns (uint256) { E[2][] memory m = es; return m.length; }
  function cdEnc(E[] calldata es) external pure returns (bytes memory) { return abi.encode(es); }
  function cdStore(E[] calldata es) external returns (uint256) { s = es; return s.length; }
  function cdRead(E[] calldata es, uint256 i) external pure returns (E) { return es[i]; }
}

def program : Program := [iT, lib, tok, attach, sS, eE, tP, copies, enums]

end Calldata.SoliditySpec
