import Solidity

/-! Scopes (`Solidity/Test/Fixtures/Scopes.sol`).  Harness input only. -/

namespace Scopes.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def fileK : SourceUnit := sol% uint256 constant K = 7;

def fileInfo : SourceUnit := sol% struct Info { uint256 a; }

def fileBad : SourceUnit := sol% error Bad(uint256 x);

def fileNote : SourceUnit := sol% event Note(uint256 x);

def fileMode : SourceUnit := sol% enum Mode { Zero, One, Two, Three }

def twice : SourceUnit := sol% function twice(uint256 x) pure returns (uint256) { return helper(x) * 2; }

def helper : SourceUnit := sol% function helper(uint256 x) pure returns (uint256) { return x + K; }

def la : SourceUnit := sol% library LA {
  uint256 internal constant K = 100;
  struct Info { uint128 lo; uint128 hi; }
  error Bad(address who);
  event Note(uint256 indexed x);
  enum Mode { Off, On }
  function helper(uint256 x) internal pure returns (uint256) { return x + K; }
  function run(uint256 x) internal pure returns (uint256) { return helper(x) * 3; }
  function mk(uint128 v) internal pure returns (Info memory) { return Info(v, v + 1); }
  function sum(Info memory i) internal pure returns (uint256) { return uint256(i.lo) + i.hi; }
  function fail(address w) internal pure { revert Bad(w); }
  function note(uint256 x) internal { emit Note(x); }
  function flip(Mode m) internal pure returns (Mode) { return m == Mode.Off ? Mode.On : Mode.Off; }
}

def lb : SourceUnit := sol% library LB {
  uint256 internal constant K = 1000;
  struct Info { bool flag; uint256 n; }
  function helper(uint256 x) internal pure returns (uint256) { return x + K; }
  function run(uint256 x) internal pure returns (uint256) { return helper(x) * 5; }
  function mk(uint256 v) internal pure returns (Info memory) { return Info(true, v); }
  enum Mode { A, B, C }
  function next(Mode m) internal pure returns (Mode) { return m == Mode.C ? Mode.A : Mode(uint8(m) + 1); }
  using LA for uint256;
  function viaLA(uint256 x) internal pure returns (uint256) { return x.run() + helper(x); }
}

def lm : SourceUnit := sol% library LM {
  error TooBig(uint256 x);
  modifier capped(uint256 x) { if (x > 100) revert TooBig(x); _; }
  function twiceCapped(uint256 x) internal pure capped(x) returns (uint256) { return x * 2; }
}

def scopes : SourceUnit := sol% contract Scopes {
  uint256 constant K = 3;
  LA.Info public ia;
  LB.Info public ib;
  mapping(uint256 => LA.Info) infos;
  using LA for LA.Mode;
  using LB for LB.Mode;
  LB.Mode public mb;

  function helper(uint256 x) internal pure returns (uint256) { return x + K; }

  function consts() external pure returns (uint256, uint256, uint256) { return (K, LA.K, LB.K); }
  function viaUsing(uint256 x) external pure returns (uint256) { return LB.viaLA(x); }
  modifier capped(uint256 x) { require(x < 10, "small"); _; }
  function mods(uint256 x) external pure capped(x / 100) returns (uint256) { return LM.twiceCapped(x); }
  function runs(uint256 x) external pure returns (uint256, uint256, uint256, uint256) {
    return (helper(x), LA.run(x), LB.run(x), twice(x));
  }
  function infoOps(uint128 v) external returns (uint256, bool, uint256) {
    LA.Info memory a = LA.mk(v);
    LB.Info memory b = LB.mk(v);
    Info memory f = Info(v);
    ia = a;
    ib = b;
    infos[v] = LA.Info(v, 5);
    return (LA.sum(ia) + infos[v].hi + f.a, ib.flag, ib.n);
  }
  function fails(uint8 k) external view {
    if (k == 0) LA.fail(msg.sender);
    if (k == 1) revert Bad(5);
    if (k == 2) revert LA.Bad(address(this));
  }
  function notes(uint256 x) external {
    LA.note(x);
    emit Note(x);
    emit LA.Note(x + 1);
  }
  function modes(uint8 m) external pure returns (LA.Mode, LA.Mode) { return (LA.flip(LA.Mode(m)), LA.Mode.On); }

  function pick(LA.Mode m) internal pure returns (uint256) { return uint256(uint8(m)) + 10; }
  function pick(LB.Mode m) internal pure returns (uint256) { return uint256(uint8(m)) + 20; }
  function pick(Mode m) internal pure returns (uint256) { return uint256(uint8(m)) + 30; }
  function enumPick() external pure returns (uint256, uint256, uint256) {
    return (pick(LA.Mode.On), pick(LB.Mode.B), pick(Mode.Three));
  }
  function enumConv(uint8 k, uint8 m) external pure returns (uint8) {
    if (k == 0) return uint8(LA.Mode(m));
    if (k == 1) return uint8(LB.Mode(m));
    return uint8(Mode(m));
  }
  function enumEnc(uint8 m) external pure returns (bytes memory, bytes32, uint8, uint8) {
    LA.Mode a = LA.Mode(m);
    LA.Mode[2] memory lit = [a, LA.Mode.On];
    return (abi.encode(a, LB.Mode.C, Mode.Three), keccak256(abi.encodePacked(a, LB.Mode.B)), uint8(lit[0]), uint8(lit[1]));
  }
  function enumUsing(uint8 m) external returns (LA.Mode, LB.Mode, LB.Mode) {
    LA.Mode a = LA.Mode(m % 2);
    mb = LB.Mode(m % 3).next();
    return (a.flip(), mb, mb.next());
  }
}

def pBase : SourceUnit := sol% contract PBase {
  uint256 private x = 1;
  uint256 internal shared = 10;
  constructor(uint256 bx) { x += bx; }
  function baseF() public view returns (uint256) { return x + shared; }
}

def pMid : SourceUnit := sol% contract PMid is PBase {
  uint256 private x = 2;
  uint256 public mid = shared + 5;
  constructor(uint256 mx) PBase(mx * 2) { x += mx; }
  function midF() public view returns (uint256) { return x + 100; }
}

def pTop : SourceUnit := sol% contract PTop is PMid {
  uint256 public top;
  uint256 public derivedInit = mid + 1;
  constructor(uint256 a, uint256 mid) PMid(a + 1) { top = mid; }
  function both() external view returns (uint256, uint256) { return (baseF(), midF()); }
}

def qBase : SourceUnit := sol% contract QBase {
  uint256 public got;
  uint256 public seen;
  constructor(uint256 v) { got = v; seen = seen * 10 + 1; }
}

def qTop : SourceUnit := sol% contract QTop is QBase {
  uint256 public init = 5;
  constructor() QBase(init + 1) { seen = seen * 10 + 2; }
}

def rBase : SourceUnit := sol% contract RBase {
  uint256 public s;
  constructor(uint256 v) { s = s * 10 + v; }
}

def rMid : SourceUnit := sol% contract RMid is RBase {
  uint256 public t;
  constructor(uint256 v) RBase(1) { t = v; s = s * 10 + 2; }
}

def rTop : SourceUnit := sol% contract RTop is RMid {
  uint256 public u;
  constructor(uint256 k) RMid(s + k) { u = s; }
}

def fileItem : SourceUnit := sol% struct Item { uint256 solo; }

def iThing : SourceUnit := sol% interface IThing {
  struct Item { uint256 a; uint8 b; }
  enum Kind { X, Y, Z }
  error Nope(uint256 code);
  event Seen(uint256 v);
}

def other : SourceUnit := sol% contract Other {
  struct Item { bool on; uint64 n; }
  enum Kind { Only }
  error Gone(uint256 a, uint256 b);
  event Was(uint256 indexed v);
}

def sBase : SourceUnit := sol% contract SBase {
  struct Item { uint128 p; uint128 q; }
  enum Kind { Lo, Hi }
  uint256 internal constant LIMIT = 50;
  uint256 public bx = 4;
  error Deny(uint8 why);
  event Tick(uint256 n);
  function scale(uint256 v) internal pure virtual returns (uint256) { return v * 2; }
}

def sTop : SourceUnit := sol% contract STop is SBase {
  Item public stored;
  SBase.Kind public kind;
  IThing.Kind public ikind;

  function scale(uint256 v) internal pure override returns (uint256) { return v * 3; }

  function items(uint128 v, uint8 m) external returns (uint256, uint256, uint8, uint8) {
    SBase.Item memory a = SBase.Item(v, v / 2);
    Item memory b = Item(v / 3, 7);
    IThing.Item memory c = IThing.Item(v, m);
    Other.Item memory d = Other.Item(true, 9);
    stored = a;
    kind = SBase.Kind(m % 2);
    ikind = IThing.Kind(m);
    return (uint256(a.p) + b.q + c.a + c.b + d.n, SBase.LIMIT + bx, uint8(SBase.Kind.Hi) + uint8(kind),
      uint8(IThing.Kind.Z) + uint8(ikind) + uint8(Other.Kind.Only));
  }
  function calls(uint256 v) external pure returns (uint256, uint256, uint256) {
    return (scale(v), SBase.scale(v), STop.scale(v));
  }
  function errs(uint8 k) external {
    if (k == 0) revert SBase.Deny(3);
    if (k == 1) revert Deny(4);
    if (k == 2) revert IThing.Nope(9);
    if (k == 3) revert Other.Gone(1, 2);
    emit SBase.Tick(k);
    emit Tick(k + 1);
    emit IThing.Seen(k + 2);
    emit Other.Was(k);
  }
}

def program : Program := [fileK, fileInfo, fileBad, fileNote, fileMode, twice, helper, la, lb, lm, scopes]
def inheritProgram : Program := [pBase, pMid, pTop]
def orderProgram : Program := [qBase, qTop]
def nestProgram : Program := [rBase, rMid, rTop]
def qualProgram : Program := [fileItem, iThing, other, sBase, sTop]

end Scopes.SoliditySpec
