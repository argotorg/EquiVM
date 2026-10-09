import Solidity.Notation

/-! Arith (`Solidity/Test/Fixtures/Arith.sol`): arithmetic and types.  Harness input only. -/

namespace Arith.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def arith : SourceUnit := sol% contract Arith {
  enum Color { Red, Green, Blue }

  function addI8(int8 a, int8 b) external pure returns (int8) { return a + b; }
  function subI8(int8 a, int8 b) external pure returns (int8) { return a - b; }
  function mulI8(int8 a, int8 b) external pure returns (int8) { return a * b; }
  function divI8(int8 a, int8 b) external pure returns (int8) { return a / b; }
  function modI8(int8 a, int8 b) external pure returns (int8) { return a % b; }
  function negI8(int8 a) external pure returns (int8) { return -a; }
  function cmpI8(int8 a, int8 b) external pure returns (bool, bool, bool, bool, bool) {
    return (a < b, a <= b, a > b, a >= b, a == b);
  }

  function addI(int256 a, int256 b) external pure returns (int256) { return a + b; }
  function subI(int256 a, int256 b) external pure returns (int256) { return a - b; }
  function mulI(int256 a, int256 b) external pure returns (int256) { return a * b; }
  function divI(int256 a, int256 b) external pure returns (int256) { return a / b; }
  function modI(int256 a, int256 b) external pure returns (int256) { return a % b; }
  function negI(int256 a) external pure returns (int256) { return -a; }
  function cmpI(int256 a, int256 b) external pure returns (bool, bool, bool) { return (a < b, a >= b, a != b); }
  function sarI(int256 a, uint256 s) external pure returns (int256) { return a >> s; }
  function shlI(int256 a, uint256 s) external pure returns (int256) { return a << s; }
  function sarI8(int8 a, uint8 s) external pure returns (int8) { return a >> s; }

  function addU8(uint8 a, uint8 b) external pure returns (uint8) { return a + b; }
  function subU8(uint8 a, uint8 b) external pure returns (uint8) { return a - b; }
  function mulU8(uint8 a, uint8 b) external pure returns (uint8) { return a * b; }
  function divU8(uint8 a, uint8 b) external pure returns (uint8) { return a / b; }
  function modU8(uint8 a, uint8 b) external pure returns (uint8) { return a % b; }
  function mulU128(uint128 a, uint128 b) external pure returns (uint128) { return a * b; }
  function mixed(uint8 a, uint256 b) external pure returns (uint256) { return a + b; }
  function mixedI(int8 a, int256 b) external pure returns (int256) { return a * b; }
  function mulLit(uint8 a) external pure returns (uint16) { return a * 300; }

  function shlU(uint256 a, uint256 s) external pure returns (uint256) { return a << s; }
  function shrU(uint256 a, uint256 s) external pure returns (uint256) { return a >> s; }
  function shlU8(uint8 a, uint8 s) external pure returns (uint8) { return a << s; }
  function shlLit(uint8 s) external pure returns (uint256) { return 1 << s; }
  function expU(uint256 a, uint256 b) external pure returns (uint256) { return a ** b; }
  function expU8(uint8 a, uint8 b) external pure returns (uint8) { return a ** b; }
  function expI(int256 a, uint256 b) external pure returns (int256) { return a ** b; }
  function expLit(uint8 b) external pure returns (uint256) { return 2 ** b; }
  function modU(uint256 a, uint256 b) external pure returns (uint256) { return a % b; }
  function divU(uint256 a, uint256 b) external pure returns (uint256) { return a / b; }
  function addMod(uint256 a, uint256 b, uint256 m) external pure returns (uint256) { return addmod(a, b, m); }
  function mulMod(uint256 a, uint256 b, uint256 m) external pure returns (uint256) { return mulmod(a, b, m); }
  function bitsU(uint256 a, uint256 b) external pure returns (uint256, uint256, uint256, uint256) {
    return (a & b, a | b, a ^ b, ~a);
  }
  function bitsI16(int16 a, int16 b) external pure returns (int16, int16, int16, int16) {
    return (a & b, a | b, a ^ b, ~a);
  }
  function bitsB4(bytes4 a, bytes4 b) external pure returns (bytes4, bytes4, bytes4, bytes4) {
    return (a & b, a | b, a ^ b, ~a);
  }
  function shiftB4(bytes4 a, uint8 s) external pure returns (bytes4, bytes4) { return (a << s, a >> s); }
  function cmpB4(bytes4 a, bytes4 b) external pure returns (bool, bool) { return (a == b, a < b); }

  function uAddU8(uint8 a, uint8 b) external pure returns (uint8) { unchecked { return a + b; } }
  function uSubU8(uint8 a, uint8 b) external pure returns (uint8) { unchecked { return a - b; } }
  function uMulI8(int8 a, int8 b) external pure returns (int8) { unchecked { return a * b; } }
  function uSubI8(int8 a, int8 b) external pure returns (int8) { unchecked { return a - b; } }
  function uNegI(int256 a) external pure returns (int256) { unchecked { return -a; } }
  function uDivI(int256 a, int256 b) external pure returns (int256) { unchecked { return a / b; } }
  function uMulU(uint256 a, uint256 b) external pure returns (uint256) { unchecked { return a * b; } }
  function uExpU(uint256 a, uint256 b) external pure returns (uint256) { unchecked { return a ** b; } }

  function compound(uint256 a, uint256 b) external pure returns (uint256 r) {
    r = a; r *= b; r /= 3; r %= 1000; r |= 16; r &= 0xff; r ^= 5; r <<= 2; r >>= 1;
  }
  function compoundI(int256 a, int256 b) external pure returns (int256 r) {
    r = a; r -= b; r *= 2; r /= 3; r %= 7;
  }
  function incs(uint8 a) external pure returns (uint8 r) { r = a; r++; ++r; }
  function uIncs(uint8 a) external pure returns (uint8 r) { r = a; unchecked { r++; ++r; } }

  function conv(uint256 a) external pure returns (uint8, uint16, int8, bytes32, address) {
    return (uint8(a), uint16(a), int8(int256(a)), bytes32(a), address(uint160(a)));
  }
  function convI(int256 a) external pure returns (uint256, int8, int128) { return (uint256(a), int8(a), int128(a)); }
  function widen(int8 a, uint8 b) external pure returns (int256, uint256, int16) {
    return (int256(a), uint256(b), int16(a));
  }
  function signFlip(uint8 a, int8 b) external pure returns (int8, uint8) { return (int8(a), uint8(b)); }
  function convB(bytes32 a) external pure returns (bytes4, uint256, bytes1) { return (bytes4(a), uint256(a), bytes1(a)); }
  function convB4(bytes4 a) external pure returns (bytes32, uint32) { return (bytes32(a), uint32(a)); }

  function toEnum(uint8 a) external pure returns (Color) { return Color(a); }
  function fromEnum(Color c) external pure returns (uint8) { return uint8(c); }
  function cmpEnum(Color a, Color b) external pure returns (bool, bool) { return (a == b, a < b); }

  function limits() external pure returns (int8, int8, uint8, int256, int256, uint256) {
    return (type(int8).min, type(int8).max, type(uint8).max, type(int256).min, type(int256).max, type(uint256).max);
  }

  function tern(uint256 a, uint256 b) external pure returns (uint256) { return a > b ? a - b : b - a; }
  function ternMixed(bool c, uint8 a, uint256 b) external pure returns (uint256) { return c ? a : b; }

  uint256 stored;
  uint8 stored8;

  function twice(uint256 x) internal pure returns (uint256) { return 2 * x; }

  function asgNarrow() external pure returns (uint256) { uint8 x; return (x = 255) + 1; }
  function asgWide(uint8 y) external pure returns (uint256) { uint256 a; return (a = y) + 1; }
  function asgChain(uint8 y) external pure returns (uint256, uint16) { uint256 a; uint16 b; a = b = y; return (a, b); }
  function asgStore(uint8 y) external returns (uint256) { return (stored = y) + 1; }
  function asgStore8(uint256 v) external returns (uint256) { return (stored8 = uint8(v)) + 1; }
  function asgLit() external returns (uint256) { return (stored8 = 200) + 100; }

  function arrFirst(uint8 i) external pure returns (uint256) { uint8[3] memory xs = [1, 2, 3]; return xs[i] * 200; }
  function arrCommon(uint8 i) external pure returns (uint256) { uint16[2] memory xs = [1, 300]; return xs[i]; }
  function arrTyped(uint8 a, uint16 b, uint8 i) external pure returns (uint256) {
    uint16[2] memory xs = [a, b];
    return xs[i] * 300;
  }
  function arrLitTyped(uint8 a, uint8 i) external pure returns (uint256) { uint16[2] memory xs = [a, 300]; return xs[i]; }

  function condSame(bool c, uint8 a, uint8 b) external pure returns (uint256) { return (c ? a : b) + 1; }
  function condArg(bool c, uint256 a, uint256 b) external pure returns (uint256) { return twice(c ? a : b); }
  function condLit(bool c, uint256 a) external pure returns (uint256) { return (c ? a : 0) + 1; }
  function condExplicit(bool c, uint8 a, uint256 b) external pure returns (uint256) { return (c ? uint256(a) : b) + 1; }
  function condPacked(bool c, uint8 a, uint8 b) external pure returns (bytes memory) { return abi.encodePacked(c ? a : b); }
}

/-- Conditionals with differently typed branches: the documented deviation (`Cond.sol`). -/
def cond : SourceUnit := sol% contract Cond {
  function ternArith(bool c, uint8 a, uint256 b) external pure returns (uint256) { return (c ? a : b) + 1; }
  function condTwoLits(bool c) external pure returns (uint256) { return (c ? 200 : 100) * 2; }
}

def program : Program := [arith]
def condProgram : Program := [cond]

end Arith.SoliditySpec
