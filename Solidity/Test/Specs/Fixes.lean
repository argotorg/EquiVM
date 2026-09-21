import Solidity

/-! Four contracts (`Solidity/Test/Fixtures/Fixes.sol`) pinning legacy-solc behaviours: right-to-left
binary operands, block scoping, modifier-argument timing and `super` inside modifiers.  Harness input only. -/

namespace Fixes.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def evalOrder : SourceUnit := sol% contract EvalOrder {
  uint public x;
  uint public log;

  function setX(uint v) internal returns (uint) { x = v; log = log * 10 + 1; return v; }
  function readX() internal returns (uint) { log = log * 10 + 2; return x; }

  function sub() external returns (uint) { return readX() - setX(10); }
  function lt() external returns (bool) { return readX() < setX(3); }
  function addSelf() external returns (uint) { x = 5; return readX() + setX(7); }
  function shortAnd(bool c) external returns (bool) { return c && setX(1) == 1; }
  function shortOr(bool c) external returns (bool) { return c || setX(2) == 2; }
}

def blockScope : SourceUnit := sol% contract BlockScope {
  uint public x;
  uint public y;

  function f() external returns (uint) {
    { uint x = 5; x += 1; y = x; }
    x = 1;
    return x;
  }
  function g() external {
    for (uint x = 0; x < 3; x++) { y += x; }
    x = 7;
  }
  function h(uint n) external returns (uint s) {
    for (uint i = 0; i < n; i++) { uint t = i * 2; s += t; }
    { uint s2 = s; s = s2 + 1; }
  }
}

def modifierArgs : SourceUnit := sol% contract ModifierArgs {
  uint public x;
  uint[] public seen;

  modifier twice() { x = 10; _; x = 20; _; }
  modifier record(uint v) { seen.push(v); _; }
  modifier guard() { if (x == 0) return; _; }

  function bump() internal returns (uint) { x += 1; return x; }
  function f() external twice record(x) { }
  function g() external guard record(bump()) { }
  function seenLen() external view returns (uint) { return seen.length; }
}

def a : SourceUnit := sol% contract A {
  uint public x;
  function g() public virtual returns (uint) { return 1; }
}

def b : SourceUnit := sol% contract B is A {
  modifier viaSuper() { x = super.g(); _; }
  function g() public virtual override returns (uint) { return 2; }
}

def superMod : SourceUnit := sol% contract SuperMod is B {
  function g() public override returns (uint) { return 3; }
  function f() external viaSuper returns (uint) { return x; }
  function h() external returns (uint) { return super.g(); }
}

def program : Program := [evalOrder, blockScope, modifierArgs, a, b, superMod]

end Fixes.SoliditySpec
