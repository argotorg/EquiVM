import Solidity

/-! Libs (`Solidity/Test/Fixtures/Libs.sol`).  Harness input only. -/

namespace Libs.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def mathLib : SourceUnit := sol% library MathLib {
  uint256 internal constant WAD = 1e18;
  error TooBig(uint256 x, uint256 hi);
  event Used(uint256 indexed x);
  struct Acc { uint256 sum; uint256 n; }

  function wmul(uint256 a, uint256 b) internal pure returns (uint256) { return a * b / WAD; }
  function clamp(uint256 x, uint256 hi) internal pure returns (uint256) {
    if (x > hi) revert TooBig(x, hi);
    return x;
  }
  function add(Acc storage acc, uint256 v) internal { acc.sum += v; acc.n += 1; }
  function avg(Acc storage acc) internal view returns (uint256) { return acc.n == 0 ? 0 : acc.sum / acc.n; }
  function mark(uint256 x) internal { emit Used(x); }
  function sq(uint256 x) internal pure returns (uint256) { return x * x; }
  function sq(uint256 x, uint256 y) internal pure returns (uint256) { return x * y; }
}

def arrLib : SourceUnit := sol% library ArrLib {
  function sum(uint256[] memory xs) internal pure returns (uint256 s) {
    for (uint256 i = 0; i < xs.length; i++) { s += xs[i]; }
  }
  function first(uint256[] storage xs) internal view returns (uint256) { return xs[0]; }
  function bump(uint256[] memory xs) internal pure { if (xs.length > 0) { xs[0] += 1; } }
}

def libs : SourceUnit := sol% contract Libs {
  using MathLib for uint256;
  using MathLib for MathLib.Acc;
  using ArrLib for uint256[];

  MathLib.Acc acc;
  uint256[] store;

  function wmul(uint256 a, uint256 b) external pure returns (uint256) { return MathLib.wmul(a, b); }
  function wmulU(uint256 a, uint256 b) external pure returns (uint256) { return a.wmul(b); }
  function clampU(uint256 x) external pure returns (uint256) { return x.clamp(100); }
  function accOps(uint256 a, uint256 b) external returns (uint256, uint256, uint256) {
    acc.add(a);
    MathLib.add(acc, b);
    return (acc.sum, acc.n, acc.avg());
  }
  function markIt(uint256 x) external { MathLib.mark(x); x.mark(); }
  function sumMem(uint256[] calldata xs) external pure returns (uint256, uint256) {
    uint256[] memory m = xs;
    m.bump();
    return (m.sum(), ArrLib.sum(m));
  }
  function firstOf(uint256 v) external returns (uint256) { store.push(v); store.push(v + 1); return store.first(); }
  function firstEmpty() external view returns (uint256) { return store.first(); }
  function chain(uint256 x) external pure returns (uint256) { return x.sq().clamp(1000).sq(2); }
  function sqs(uint256 x, uint256 y) external pure returns (uint256, uint256) { return (MathLib.sq(x), MathLib.sq(x, y)); }
  function accMem(uint256 a) external pure returns (uint256) {
    MathLib.Acc memory m;
    m.sum = a;
    m.n = 2;
    return m.sum / m.n;
  }

  uint256 constant BASE = 3;
  uint256 constant DOUBLE = BASE * 2;
  function constShadow(uint256 BASE) external pure returns (uint256) { return DOUBLE + BASE; }
}

def libsQual : SourceUnit := sol% contract LibsQual {
  function wad() external pure returns (uint256) { return MathLib.WAD; }
  function accLit(uint256 a) external pure returns (uint256) {
    MathLib.Acc memory m = MathLib.Acc(a, 2);
    return m.sum / m.n;
  }
}

def program : Program := [mathLib, arrLib, libs]
def qualProgram : Program := [mathLib, arrLib, libsQual]

/-- `LibsQual` with the qualified expressions written unqualified (GUIDE §6). -/
def libsUnqual : SourceUnit := sol% contract LibsQual {
  function wad() external pure returns (uint256) { return WAD; }
  function accLit(uint256 a) external pure returns (uint256) {
    MathLib.Acc memory m = Acc(a, 2);
    return m.sum / m.n;
  }
}

def unqualProgram : Program := [mathLib, arrLib, libsUnqual]

end Libs.SoliditySpec
