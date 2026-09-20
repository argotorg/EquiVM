import Solidity

/-! HexLit (`Solidity/Test/Fixtures/HexLit.sol`): number literals converting to `bytesN` (zero always,
hex literals only with exactly `2N` digits) in assignments, comparisons, explicit conversions and
argument passing.  Harness input only. -/

namespace HexLit.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def hexLit : SourceUnit := sol% contract HexLit {
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

def program : Program := [hexLit]

end HexLit.SoliditySpec
