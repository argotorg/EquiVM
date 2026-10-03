import Solidity

/-! Features / IKicker / Child (`Solidity/Test/Fixtures/Features.sol`): free functions, named
arguments, `.selector`, `address.code.length`, literal arithmetic, overloaded events, slices,
`bytesN(bytes)`, `bytesN` indexing.  `Kicker` is deployed from its
solc bytecode; the spec only needs its interface.  Harness input only. -/

namespace Features.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def uncheckedIncFn : SourceUnit := sol% function uncheckedInc(uint256 i) pure returns (uint256 j) {
  unchecked { j = i + 1; }
}

def clampFn : SourceUnit := sol% function clamp(uint256 x, uint256 lo, uint256 hi) pure returns (uint256) {
  if (x < lo) return lo;
  if (x > hi) return hi;
  return x;
}

def ikicker : SourceUnit := sol% interface IKicker {
  function kick(address usr, uint256 tab, uint256 lot) external returns (uint256 id);
}

def child : SourceUnit := sol% contract Child {
  uint256 public a;
  address public b;
  constructor(uint256 a_, address b_) { a = a_; b = b_; }
}

def features : SourceUnit := sol% contract Features {
  uint256 public sum;
  uint256 public lastId;
  bytes4 public sel;
  address public child;

  function sumTo(uint256 n) external returns (uint256 s) {
    for (uint256 i = 0; i < n; i = uncheckedInc(i)) { s += i; }
    sum = s;
  }

  function clamped(uint256 x) external pure returns (uint256) {
    return clamp({ hi: 100, lo: 10, x: x });
  }

  function pair(uint256 a, uint256 b) internal pure returns (uint256) { return a * 1000 + b; }

  function namedInternal(uint256 x, uint256 y) external pure returns (uint256) {
    return pair({ b: y, a: x });
  }

  function namedExternal(address k, address usr, uint256 tab) external returns (uint256) {
    lastId = IKicker(k).kick({ lot: 7, usr: usr, tab: tab });
    return lastId;
  }

  function namedNew(uint256 v) external returns (address) {
    Child c = new Child({ b_: msg.sender, a_: v });
    child = address(c);
    return child;
  }

  function selectors() external returns (bytes4, bytes4) {
    sel = IKicker.kick.selector;
    return (sel, this.sumTo.selector);
  }

  function codeLen(address a) external view returns (uint256) {
    return a.code.length;
  }

  function hasCode(address a) external view returns (bool) {
    return a.code.length > 0;
  }

  function literals() external pure returns (uint256, uint256, uint256) {
    return (2.5 ether, 10 / 2 * 3, 1e18 / 4);
  }

  event File(bytes32 indexed what, uint256 data);
  event File(bytes32 indexed what, address data);
  event File(bytes32 indexed ilk, bytes32 indexed what, uint256 data);
  event Cage();
  event Cage(bytes32 indexed ilk);

  function fileUint(bytes32 what, uint256 data) external { emit File(what, data); }
  function fileAddr(bytes32 what, address data) external { emit File(what, data); }
  function fileIlk(bytes32 ilk, bytes32 what, uint256 data) external { emit File(ilk, what, data); }
  function cage() external { emit Cage(); }
  function cageIlk(bytes32 ilk) external { emit Cage(ilk); }

  function sliceHead(bytes calldata data) external pure returns (bytes4) { return bytes4(data[:4]); }
  function sliceDecode(bytes calldata data) external pure returns (uint256, address) {
    return abi.decode(data[4:], (uint256, address));
  }
  function sliceMid(bytes calldata data, uint256 a, uint256 b) external pure returns (bytes memory) { return data[a:b]; }
  function sliceLen(bytes calldata data, uint256 a) external pure returns (uint256) {
    bytes calldata t = data[a:];
    return t.length;
  }
  function sliceArr(uint256[] calldata xs, uint256 a, uint256 b) external pure returns (uint256[] memory) {
    return xs[a:b];
  }
  function msgTail() external pure returns (bytes memory) { return msg.data[4:]; }
  function toB4(bytes calldata b) external pure returns (bytes4) {
    bytes memory m = b;
    return bytes4(m);
  }
  function toB32(bytes calldata b) external pure returns (bytes32) { return bytes32(b); }

  function byteAt(bytes32 x, uint256 i) external pure returns (bytes1) { return x[i]; }
  function hexDigit(uint8 v) external pure returns (bytes1) {
    bytes16 h = "0123456789abcdef";
    return h[v & 0xf];
  }

  function lenMem(bytes memory b) external pure returns (uint256) { return b.length; }
  function sumMem(uint256[] memory xs, string memory s) external pure returns (uint256 t) {
    for (uint256 i = 0; i < xs.length; i = uncheckedInc(i)) { t += xs[i]; }
    t += bytes(s).length;
  }
}

def program : Program := [uncheckedIncFn, clampFn, ikicker, child, features]

end Features.SoliditySpec
