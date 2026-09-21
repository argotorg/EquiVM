// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

// Binary operands: legacy solc evaluates the right operand first (`&&`/`||` stay left to right).
contract EvalOrder {
  uint public x;
  uint public log;

  function setX(uint v) internal returns (uint) { x = v; log = log * 10 + 1; return v; }
  function readX() internal returns (uint) { log = log * 10 + 2; return x; }

  // right first: setX(10) runs before readX(), so this is 10 - 10; left first would underflow.
  function sub() external returns (uint) { return readX() - setX(10); }
  function lt() external returns (bool) { return readX() < setX(3); }
  function addSelf() external returns (uint) { x = 5; return readX() + setX(7); }
  function shortAnd(bool c) external returns (bool) { return c && setX(1) == 1; }
  function shortOr(bool c) external returns (bool) { return c || setX(2) == 2; }
}

// Block scoping: a block-local that shadows a state variable is gone after the block.
contract BlockScope {
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

// Modifier arguments are evaluated when the modifier is entered, at the outer modifier's `_`, every time.
contract ModifierArgs {
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

// `super` inside a modifier body resolves from the modifier's contract.
contract A {
  uint public x;
  function g() public virtual returns (uint) { return 1; }
}
contract B is A {
  modifier viaSuper() { x = super.g(); _; }
  function g() public virtual override returns (uint) { return 2; }
}
contract SuperMod is B {
  function g() public override returns (uint) { return 3; }
  function f() external viaSuper returns (uint) { return x; }
  function h() external returns (uint) { return super.g(); }
}
