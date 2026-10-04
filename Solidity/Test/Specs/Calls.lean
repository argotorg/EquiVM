import Solidity

/-! Calls (`Solidity/Test/Fixtures/Calls.sol`).  Harness input only. -/

namespace Calls.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def point : SourceUnit := sol% struct Point { uint128 x; uint128 y; }

def iTarget : SourceUnit := sol% interface ITarget {
  function setX(uint256 v) external returns (uint256);
  function getX() external view returns (uint256);
  function pay() external payable returns (uint256);
  function multi(uint256 a) external view returns (uint256, bool, address);
  function str(uint256 n) external pure returns (string memory);
  function arr(uint256 n) external pure returns (uint256[] memory);
  function point(uint128 x) external pure returns (Point memory);
  function sumPoint(Point calldata p) external pure returns (uint256);
  function failMsg() external pure;
  function failCustom(uint256 c) external view;
  function failPanic() external pure returns (uint256);
  function failEmpty() external pure;
  function sneaky() external view returns (uint256);
  function short() external pure returns (uint256);
  function ping() external;
  function callBack(uint256 v) external;
  function whoami() external view returns (address, address);
}

def calls : SourceUnit := sol% contract Calls {
  uint256 public last;
  uint256 public pokes;
  event Poked(address indexed src, uint256 v);
  error Wrapped(bytes data);

  function callSet(address t, uint256 v) external returns (uint256) {
    uint256 r = ITarget(t).setX(v);
    return r + ITarget(t).getX();
  }
  function callPay(address t, uint256 v) external payable returns (uint256, uint256) {
    uint256 r = ITarget(t).pay{value: v}();
    return (r, address(this).balance);
  }
  function callGas(address t, uint256 g) external returns (uint256) { return ITarget(t).setX{gas: g}(7); }
  function callMulti(address t, uint256 a) external view returns (uint256, bool, address) { return ITarget(t).multi(a); }
  function callMultiPick(address t, uint256 a) external view returns (uint256) {
    (uint256 x, bool b, ) = ITarget(t).multi(a);
    return b ? x : 0;
  }
  function callStr(address t, uint256 n) external pure returns (string memory, uint256) {
    string memory s = ITarget(t).str(n);
    return (s, bytes(s).length);
  }
  function callArr(address t, uint256 n) external pure returns (uint256[] memory a, uint256 s) {
    a = ITarget(t).arr(n);
    for (uint256 i = 0; i < a.length; i++) { s += a[i]; }
  }
  function callPoint(address t, uint128 x) external pure returns (uint128, uint128) {
    Point memory p = ITarget(t).point(x);
    return (p.x, p.y);
  }
  function callSumPoint(address t, uint128 x, uint128 y) external pure returns (uint256) {
    return ITarget(t).sumPoint(Point(x, y));
  }
  function callFail(address t, uint8 k) external view returns (uint256) {
    if (k == 0) ITarget(t).failMsg();
    else if (k == 1) ITarget(t).failCustom(42);
    else if (k == 2) return ITarget(t).failPanic();
    else if (k == 3) ITarget(t).failEmpty();
    else if (k == 4) return ITarget(t).sneaky();
    else if (k == 5) return ITarget(t).short();
    return 99;
  }
  function callPing(address t) external {
    emit Poked(msg.sender, 1);
    ITarget(t).ping();
    emit Poked(msg.sender, 2);
  }
  function poke(uint256 v) external { pokes += v; emit Poked(msg.sender, v); }
  function callBack(address t, uint256 v) external returns (uint256) {
    pokes = 1;
    ITarget(t).callBack(v);
    return pokes;
  }
  function who(address t) external view returns (address, address, address) {
    (address s, address me) = ITarget(t).whoami();
    return (s, me, address(this));
  }
  function selfPoke(uint256 v) external returns (uint256) { this.poke(v); return pokes; }
  function getLast() external view returns (uint256) { return last; }
  function selfView() external view returns (uint256) { return this.getLast() + 1; }

  function lowCall(address t, uint256 v) external returns (bool, bytes memory) {
    return t.call(abi.encodeWithSignature("setX(uint256)", v));
  }
  function lowCallDecode(address t, uint256 v) external returns (uint256) {
    (bool ok, bytes memory out) = t.call(abi.encodeWithSelector(ITarget.setX.selector, v));
    require(ok, "low");
    return abi.decode(out, (uint256));
  }
  function lowValue(address t, uint256 v) external payable returns (bool, uint256) {
    (bool ok, ) = t.call{value: v}("");
    return (ok, address(this).balance);
  }
  function lowFail(address t) external returns (bool, bytes memory) {
    return t.call(abi.encodeWithSignature("failMsg()"));
  }
  function lowStatic(address t) external view returns (bool, bytes memory) {
    return t.staticcall(abi.encodeWithSignature("getX()"));
  }
  function lowStaticWrite(address t) external view returns (bool, bytes memory) {
    return t.staticcall(abi.encodeWithSignature("setX(uint256)", 5));
  }
  function lowDelegate(address t, uint256 v) external returns (bool, uint256) {
    (bool ok, ) = t.delegatecall(abi.encodeWithSignature("setSlot0(uint256)", v));
    return (ok, last);
  }
  function lowUnknown(address t) external returns (bool, bytes memory) {
    return t.call(abi.encodeWithSignature("nope()"));
  }
  function lowBubble(address t) external returns (uint256) {
    (bool ok, bytes memory out) = t.call(abi.encodeWithSignature("failCustom(uint256)", 7));
    if (!ok) revert Wrapped(out);
    return 1;
  }

  function doTransfer(address payable dst, uint256 v) external payable returns (uint256) {
    dst.transfer(v);
    return address(this).balance;
  }
  function doSend(address payable dst, uint256 v) external payable returns (bool, uint256) {
    bool ok = dst.send(v);
    return (ok, address(this).balance);
  }
  function balances(address a) external view returns (uint256, uint256) { return (a.balance, address(this).balance); }

  receive() external payable { last += msg.value; }
}

def program : Program := [point, iTarget, calls]

end Calls.SoliditySpec
