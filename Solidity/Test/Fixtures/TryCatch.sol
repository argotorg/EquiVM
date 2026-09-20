// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

// try/catch: clause selection by revert data, return decoding, uncaught failures, creation.

interface ICallee {
  function ok(uint v) external returns (uint);
  function requireMsg(uint v) external pure returns (uint);
  function panicDiv(uint v) external pure returns (uint);
  function custom(uint v) external view;
  function plainRevert() external pure;
  function noReturn(uint v) external;
  function badReturn() external pure returns (uint);
}

contract Callee {
  uint public x;
  error Custom(uint code, address who);

  function ok(uint v) external returns (uint) { x = v; return v + 1; }
  function requireMsg(uint v) external pure returns (uint) { require(v > 10, "small"); return v; }
  function panicDiv(uint v) external pure returns (uint) { uint z = 0; return v / z; }
  function custom(uint v) external view { revert Custom(v, msg.sender); }
  function plainRevert() external pure { revert(); }
  function noReturn(uint v) external { x = v; }
  function badReturn() external pure returns (uint) { assembly { return(0, 1) } }
}

contract Child {
  uint public v;
  constructor(uint a) { require(a != 7, "seven"); v = a; }
}

contract TryCaller {
  uint public last;
  string public reason;
  uint public code;
  bytes public data;
  uint public tag;

  function tryOk(address c, uint v) external returns (uint) {
    try ICallee(c).ok(v) returns (uint r) { last = r; tag = 1; return r; }
    catch Error(string memory m) { reason = m; tag = 2; }
    catch Panic(uint p) { code = p; tag = 3; }
    catch (bytes memory d) { data = d; tag = 4; }
    return 0;
  }

  function tryRequire(address c, uint v) external {
    try ICallee(c).requireMsg(v) returns (uint r) { last = r; tag = 1; }
    catch Error(string memory m) { reason = m; tag = 2; }
    catch (bytes memory d) { data = d; tag = 4; }
  }

  function tryPanic(address c, uint v) external {
    try ICallee(c).panicDiv(v) returns (uint r) { last = r; tag = 1; }
    catch Panic(uint p) { code = p; tag = 3; }
  }

  function tryCustomErrorOnly(address c, uint v) external {
    try ICallee(c).custom(v) { tag = 1; }
    catch Error(string memory m) { reason = m; tag = 2; }
  }

  function tryCustomLow(address c, uint v) external {
    try ICallee(c).custom(v) { tag = 1; }
    catch (bytes memory d) { data = d; tag = 4; }
  }

  function tryPlain(address c) external {
    try ICallee(c).plainRevert() { tag = 1; }
    catch Error(string memory m) { reason = m; tag = 2; }
    catch { tag = 5; }
  }

  function tryNoReturn(address c, uint v) external {
    try ICallee(c).noReturn(v) { tag = 1; }
    catch { tag = 5; }
  }

  function tryBadReturn(address c) external {
    try ICallee(c).badReturn() returns (uint r) { last = r; tag = 1; }
    catch { tag = 5; }
  }

  function tryIgnoreReturns(address c, uint v) external {
    try ICallee(c).ok(v) { tag = 1; }
    catch { tag = 5; }
  }

  function tryIgnoreBad(address c) external {
    try ICallee(c).badReturn() { tag = 1; }
    catch { tag = 5; }
  }

  function tryArgRevert(address c) external {
    try ICallee(c).ok(failingArg()) { tag = 1; }
    catch { tag = 5; }
  }

  function failingArg() internal pure returns (uint) { revert("arg"); }

  function tryNew(uint a) external returns (address) {
    try new Child(a) returns (Child ch) { tag = 1; return address(ch); }
    catch Error(string memory m) { reason = m; tag = 2; return address(0); }
  }
}
