// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

// Inheritance: a diamond with super chains, constructor arguments, state variable initializers
// across bases, a virtual function called from a base, an overridden modifier, overloads, a getter
// that implements an interface function, an abstract function.

interface IShape {
  function area() external view returns (uint256);
  function sides() external view returns (uint256);
}

abstract contract Base {
  uint256 public a = 1;
  uint256 public log;
  constructor(uint256 x) { a += x; log = log * 10 + 1; }
  function v() public virtual returns (uint256) { log = log * 10 + 1; return 1; }
  function hook() internal virtual returns (uint256) { return 10; }
  function viaHook() public returns (uint256) { return hook() + 1; }
  function abs(uint256 x) public view virtual returns (uint256);
  modifier tag() virtual { log = log * 10 + 7; _; }
  function tagged() public tag returns (uint256) { return log; }
}

contract Left is Base {
  uint256 public l = a + 10;
  constructor(uint256 x) Base(x + 1) { l += x; log = log * 10 + 2; }
  function v() public virtual override returns (uint256) { log = log * 10 + 2; return super.v() + 10; }
  function hook() internal virtual override returns (uint256) { return 20; }
  function abs(uint256 x) public view virtual override returns (uint256) { return x + l; }
}

abstract contract Right is Base {
  uint256 public r = 5;
  constructor() { r += a; log = log * 10 + 3; }
  function v() public virtual override returns (uint256) { log = log * 10 + 3; return super.v() + 100; }
  function hook() internal virtual override returns (uint256) { return super.hook() + 30; }
  modifier tag() virtual override { log = log * 10 + 8; _; log = log * 10 + 9; }
}

contract Diamond is Left, Right, IShape {
  uint256 public override sides = 4;
  uint256 public d;
  constructor(uint256 x, uint256 y) Left(x) Right() { d = y; log = log * 10 + 4; }
  function v() public override(Left, Right) returns (uint256) { log = log * 10 + 4; return super.v() + 1000; }
  function hook() internal override(Left, Right) returns (uint256) { return super.hook() + 40; }
  modifier tag() override(Base, Right) { log = log * 10 + 6; _; log = log * 10 + 5; }
  function abs(uint256 x) public view override(Base, Left) returns (uint256) { return super.abs(x) + a + r; }
  function area() external view override returns (uint256) { return d * d; }
  function pick(uint256 x) public pure returns (uint256) { return x + 1; }
  function pick(uint256 x, uint256 y) public pure returns (uint256) { return x + y; }
  function pick(address x) public pure returns (uint256) { return uint256(uint160(x)); }
  function picks(uint256 x) external pure returns (uint256, uint256) { return (pick(x), pick(x, 2)); }
  function leftV() external returns (uint256) { return Left.v(); }
  function state() external view returns (uint256, uint256, uint256, uint256, uint256) { return (a, l, r, d, log); }
}
