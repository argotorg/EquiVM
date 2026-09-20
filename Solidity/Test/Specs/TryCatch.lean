import Solidity

/-! TryCaller / ICallee / Child (`Solidity/Test/Fixtures/TryCatch.sol`): `try`/`catch` on external
calls and on `new`.  `Callee` is deployed from its solc bytecode; the spec only needs its interface.
Harness input only. -/

namespace TryCatch.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def icallee : SourceUnit := sol% interface ICallee {
  function ok(uint v) external returns (uint);
  function requireMsg(uint v) external pure returns (uint);
  function panicDiv(uint v) external pure returns (uint);
  function custom(uint v) external view;
  function plainRevert() external pure;
  function noReturn(uint v) external;
  function badReturn() external pure returns (uint);
}

def child : SourceUnit := sol% contract Child {
  uint public v;
  constructor(uint a) { require(a != 7, "seven"); v = a; }
}

def tryCaller : SourceUnit := sol% contract TryCaller {
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

def program : Program := [icallee, child, tryCaller]

end TryCatch.SoliditySpec
