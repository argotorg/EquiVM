import Solidity

/-! A / B / C (`Solidity/Test/Fixtures/BaseCall.sol`): explicit base calls `A.f()`, `B.f()` beside
`super.f()` and the own override, with internal and reverting base functions.  Harness input only. -/

namespace BaseCall.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def a : SourceUnit := sol% contract A {
  uint public x;
  function f() public virtual returns (uint) { return 1; }
  function g(uint v) internal virtual { x = v; }
  function h(uint v) public virtual returns (uint) { require(v > 0, "zero"); return v; }
}

def b : SourceUnit := sol% contract B is A {
  function f() public virtual override returns (uint) { return 2; }
  function g(uint v) internal virtual override { x = v + 100; }
}

def c : SourceUnit := sol% contract C is B {
  function f() public override returns (uint) { return 3; }

  function callA() external returns (uint) { return A.f(); }
  function callB() external returns (uint) { return B.f(); }
  function callSuper() external returns (uint) { return super.f(); }
  function callOwn() external returns (uint) { return f(); }
  function setViaA(uint v) external { A.g(v); }
  function setViaB(uint v) external { B.g(v); }
  function checkViaA(uint v) external returns (uint) { return A.h(v); }
}

def program : Program := [a, b, c]

end BaseCall.SoliditySpec
