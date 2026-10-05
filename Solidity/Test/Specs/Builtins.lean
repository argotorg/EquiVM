import Solidity

/-! Builtins (`Solidity/Test/Fixtures/Builtins.sol`).  Harness input only. -/

namespace Builtins.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def iThing : SourceUnit := sol% interface IThing {
  function poke(uint256 a, address b) external returns (bool);
  function peek() external view returns (uint256);
  function tag(bytes4 t, string calldata s) external;
}

def small : SourceUnit := sol% contract Small {
  uint256 public v;
  constructor(uint256 x) payable { v = x; }
}

def oBase : SourceUnit := sol% contract OBase {
  function val() external view virtual returns (uint256) { return 1; }
  function dbl(uint256 x) external pure virtual returns (uint256) { return x * 2; }
}

def oDer : SourceUnit := sol% contract ODer is OBase {
  uint256 public override val = 7;
  mapping(uint256 => uint256) public slots;
  function dbl(uint256 x) external pure override returns (uint256) { return x * 3; }
  function set(uint256 k, uint256 v) external { slots[k] = v; }
}

def envC : SourceUnit := sol% contract Env {
  function blockInfo() external view returns (uint256, uint256, uint256, address, uint256, uint256, uint256, uint256) {
    return (block.timestamp, block.number, block.chainid, block.coinbase, block.gaslimit, block.prevrandao,
      block.difficulty, block.basefee);
  }
  function txInfo() external payable returns (address, uint256, address, uint256, bytes4) {
    return (tx.origin, tx.gasprice, msg.sender, msg.value, msg.sig);
  }
  function callData(uint256 a, bytes calldata b) external pure returns (bytes memory, bytes4, uint256, uint256) {
    return (msg.data, msg.sig, msg.data.length, a + b.length);
  }
  function hashes(uint256 n) external view returns (bytes32, bytes32) {
    return (blockhash(n), blockhash(block.number - 1));
  }
  function accounts(address a) external view returns (uint256, uint256, uint256, bytes32, bytes32, uint256) {
    return (a.balance, address(this).balance, a.code.length, a.codehash, address(this).codehash, address(this).code.length);
  }
  function codeHashes(address a) external view returns (bool, bool) {
    return (keccak256(a.code) == a.codehash, keccak256(address(this).code) == address(this).codehash);
  }
  function units() external pure returns (uint256, uint256, uint256, uint256, uint256, uint256, uint256, uint256) {
    return (1 wei, 1 gwei, 1 ether, 1 seconds, 1 minutes, 1 hours, 1 days, 1 weeks);
  }
  function unitMath(uint256 x) external view returns (uint256, bool) {
    return (x * 1 days + 2 hours + 5 gwei, block.timestamp + 3 weeks > x);
  }
  function gasOk() external view returns (bool) { return gasleft() <= block.gaslimit; }
}

def hashC : SourceUnit := sol% contract Hash {
  function hashAll(bytes calldata b) external pure returns (bytes32, bytes32) { return (keccak256(b), sha256(b)); }
  function packed(uint8 a, int16 b, address c, bool d, bytes3 e) external pure returns (bytes memory, bytes32, bytes32) {
    bytes memory p = abi.encodePacked(a, b, c, d, e);
    return (p, keccak256(p), sha256(p));
  }
  function packedDyn(string calldata f, bytes calldata g, int8 a) external pure returns (bytes memory, bytes32) {
    bytes memory p = abi.encodePacked(f, a, g, f);
    return (p, keccak256(p));
  }
  function packedArr(uint16[] calldata xs, uint8 y) external pure returns (bytes memory) {
    uint8[2] memory ys = [y, 7];
    return abi.encodePacked(xs, ys, "lit", uint24(9));
  }
  function strEq(string calldata a, string calldata b) external pure returns (bool) {
    return keccak256(bytes(a)) == keccak256(bytes(b));
  }
  function pair(bytes32 a, bytes32 b) external pure returns (bytes32, bytes32, bytes32) {
    return (sha256(abi.encodePacked(a, b)), sha256(abi.encode(a, b)), keccak256(abi.encode(a, b)));
  }
  function litHash() external pure returns (bytes32, bytes32, bytes32) { return (keccak256("abc"), sha256("abc"), sha256("")); }
}

def ripC : SourceUnit := sol% contract Rip {
  function rip(bytes calldata b) external pure returns (bytes20) { return ripemd160(b); }
  function ripLit() external pure returns (bytes20, bytes20) { return (ripemd160("abc"), ripemd160(abi.encodePacked(uint256(1)))); }
}

def abiC : SourceUnit := sol% contract AbiC {
  struct P { uint128 a; bool b; }
  struct Q { uint256 x; string s; uint8[] ys; }
  enum E { A, B, C }

  function enc(uint256 a, int8 b, address c, bool d, bytes4 e, E f) external pure returns (bytes memory) {
    return abi.encode(a, b, c, d, e, f);
  }
  function encDyn(string calldata s, bytes calldata b, uint256[] calldata xs) external pure returns (bytes memory) {
    return abi.encode(s, b, xs, "lit", 7);
  }
  function encStruct(uint128 a, bool b, string calldata s) external pure returns (bytes memory, bytes memory) {
    P memory p = P(a, b);
    Q memory q = Q(a, s, new uint8[](2));
    q.ys[1] = 7;
    return (abi.encode(p), abi.encode(q, p));
  }
  function encNested(uint256 n) external pure returns (bytes memory) {
    uint256[][] memory m = new uint256[][](2);
    m[0] = new uint256[](n % 4);
    m[1] = new uint256[](1);
    m[1][0] = n;
    return abi.encode(m, n);
  }
  function encSel(uint256 a, address b) external view returns (bytes memory, bytes memory, bytes memory) {
    return (abi.encodeWithSelector(0x12345678, a, b), abi.encodeWithSelector(this.enc.selector, a),
      abi.encodeWithSignature("f(uint256,address)", a, b));
  }
  function encCall(uint256 a, address b, string calldata s) external view returns (bytes memory, bytes memory, bytes memory, bytes memory) {
    return (abi.encodeCall(IThing.poke, (a, b)), abi.encodeCall(IThing.peek, ()),
      abi.encodeCall(IThing.tag, (0x01020304, s)), abi.encodeCall(this.encNested, (a)));
  }
  function dec(bytes calldata d) external pure returns (uint256, address, bool) { return abi.decode(d, (uint256, address, bool)); }
  function decSmall(bytes calldata d) external pure returns (uint8, int16, bytes4, E) { return abi.decode(d, (uint8, int16, bytes4, E)); }
  function decDyn(bytes calldata d) external pure returns (string memory, uint256[] memory) { return abi.decode(d, (string, uint256[])); }
  function decStruct(bytes calldata d) external pure returns (uint128, bool, uint256, string memory, uint256) {
    (P memory p, Q memory q) = abi.decode(d, (P, Q));
    return (p.a, p.b, q.x, q.s, q.ys.length);
  }
  function roundTrip(uint256 a, string calldata s, int8 c) external pure returns (uint256, string memory, int8) {
    return abi.decode(abi.encode(a, s, c), (uint256, string, int8));
  }
  function concatB(bytes calldata a, bytes4 b, bytes calldata c) external pure returns (bytes memory, uint256) {
    bytes memory r = bytes.concat(a, b, c, hex"00ff", bytes1(0x7f));
    return (r, bytes.concat().length);
  }
  function concatS(string calldata a, string calldata b) external pure returns (string memory, string memory) {
    return (string.concat(a, "-", b), string.concat());
  }
}

def abiFixedC : SourceUnit := sol% contract AbiFixed {
  struct W { uint8[2] pair; uint256 z; }
  function encFixed(uint256 a, uint8 b) external pure returns (bytes memory, bytes memory) {
    uint256[2] memory x = [a, a + 1];
    uint8[3] memory y = [b, 2, 3];
    return (abi.encode(x), abi.encode(y, x, b));
  }
  function decFixed(bytes calldata d) external pure returns (uint256, uint256) {
    uint256[2] memory x = abi.decode(d, (uint256[2]));
    return (x[0], x[1]);
  }
  function encW(uint8 a) external pure returns (bytes memory) {
    W memory w = W([a, 1], 5);
    return abi.encode(w);
  }
}

def typeInfoC : SourceUnit := sol% contract TypeInfo {
  enum E { A, B, C }
  event Ping(uint256 indexed a, bytes b);
  error Oops(uint256 code, string why);
  uint256 public total;
  mapping(address => uint256) public bal;

  function ext(uint256 a) external pure returns (uint256) { return a; }
  function names() external pure returns (string memory, string memory, string memory) {
    return (type(TypeInfo).name, type(IThing).name, type(Small).name);
  }
  function ids() external view returns (bytes4, bytes4, bytes4, bytes4, bytes4, bytes4) {
    return (type(IThing).interfaceId, this.names.selector, IThing.poke.selector, TypeInfo.ext.selector,
      this.total.selector, this.bal.selector);
  }
  function topics() external pure returns (bytes32, bytes4, bytes4) {
    return (Ping.selector, Oops.selector, TypeInfo.Oops.selector);
  }
  function codes() external pure returns (bytes32, uint256, bytes32, uint256) {
    return (keccak256(type(Small).creationCode), type(Small).creationCode.length,
      keccak256(type(Small).runtimeCode), type(Small).runtimeCode.length);
  }
  function limits() external pure returns (E, E, uint8, int8, int256, uint256) {
    return (type(E).min, type(E).max, type(uint8).max, type(int8).min, type(int256).max, type(uint256).max);
  }
  function viaType(uint256 k) external returns (uint256, uint256, uint256, bytes4, bytes4, bytes4, bytes4) {
    ODer d = new ODer();
    d.set(k, k / 2 + 1);
    return (d.val(), d.dbl(k), d.slots(k), ODer.dbl.selector, d.val.selector, OBase.val.selector, d.slots.selector);
  }
  function viaRef(uint256 k) external returns (bytes memory, bytes4, bytes4) {
    ODer d = new ODer();
    IThing t = IThing(address(d));
    return (abi.encodeCall(d.set, (k, 1)), t.poke.selector, d.dbl.selector);
  }
  function make(uint256 x) external returns (uint256, bool, bool) {
    Small s = new Small(x);
    return (s.v(), address(s).code.length == type(Small).runtimeCode.length,
      address(s).codehash == keccak256(type(Small).runtimeCode));
  }
}

def convC : SourceUnit := sol% contract Conv {
  enum E { A, B, C }

  function ints(uint256 a, int256 b) external pure returns (uint8, uint64, int8, int128, uint256, int256, uint16, int16) {
    return (uint8(a), uint64(a), int8(b), int128(b), uint256(b), int256(a), uint16(uint8(a)), int16(int8(b)));
  }
  function widen(uint8 a, int8 b) external pure returns (uint256, int256, int16, uint64, int256) {
    uint256 x = a;
    int256 y = b;
    int16 z = b;
    uint64 w = a;
    return (x, y, z, w, int256(uint256(a)) + y);
  }
  function fixedB(bytes32 a, bytes4 b) external pure returns (bytes4, bytes32, uint32, uint256, bytes1, bytes8) {
    return (bytes4(a), bytes32(b), uint32(b), uint256(a), bytes1(a), bytes8(b));
  }
  function fixedU(uint32 c, uint256 d) external pure returns (bytes4, bytes32) { return (bytes4(c), bytes32(d)); }
  function fixedWiden(bytes2 a) external pure returns (bytes4, bytes32) {
    bytes4 x = a;
    bytes32 y = x;
    return (x, y);
  }
  function addrs(address a, uint160 u, bytes20 b) external pure returns (uint160, address, bytes20, address, address payable) {
    return (uint160(a), address(u), bytes20(a), address(b), payable(a));
  }
  function addrWords(address a, uint256 w) external pure returns (address, uint256, bytes32) {
    return (address(uint160(w)), uint256(uint160(a)), bytes32(uint256(uint160(a))));
  }
  function addrLits() external view returns (address, address, address payable, address, bool) {
    return (address(0), address(0x1234), payable(address(this)), 0x5B38Da6a701c568545dCfcB03FcB875f56beddC4,
      address(this) == msg.sender);
  }
  function enums(uint8 x, uint256 y) external pure returns (E, E, uint8, uint256, uint16) {
    E e = E(x);
    return (e, E(y), uint8(e), uint256(e), uint16(e));
  }
  function enumSigned(int8 z) external pure returns (E) { return E(z); }
  function byteStr(string calldata s) external pure returns (bytes memory, uint256, bytes1, bytes2) {
    bytes memory sb = bytes(s);
    return (sb, sb.length, sb.length > 0 ? sb[0] : bytes1(0), bytes2(sb));
  }
  function bytesFixed(bytes calldata b) external pure returns (string memory, bytes4, bytes32) {
    return (string(b), bytes4(b), bytes32(b));
  }
  function lits() external pure returns (bytes4, bytes32, bytes3, bytes memory, string memory) {
    bytes4 a = 0x12345678;
    bytes32 b = "abc";
    bytes3 c = hex"010203";
    bytes memory d = "xyz";
    string memory e = "str";
    return (a, b, c, d, e);
  }
  function litConvs() external pure returns (bytes2, bytes1, uint8, bytes32, bytes4) {
    return (bytes2("ab"), bytes1(uint8(65)), uint8(bytes1("A")), bytes32(0), bytes4(0x01020304));
  }
  function contracts(address a) external view returns (address, address, IThing, address) {
    IThing t = IThing(a);
    return (address(t), address(this), IThing(address(this)), address(Conv(a)));
  }
  function ov(int16 x) internal pure returns (uint256) { return uint256(int256(x)) + 100; }
  function ov(uint16 x) internal pure returns (uint256) { return uint256(x) + 200; }
  function overload(uint8 a) external pure returns (uint256) { return ov(a); }
  function bools(uint256 a) external pure returns (bool, bool, uint256) {
    bool t = a != 0;
    return (t, !t, t ? 1 : 0);
  }
}

def memOpsC : SourceUnit := sol% contract MemOps {
  struct S { uint256 a; uint8 b; address c; }
  uint256[] public arr;
  bytes public blob;
  S[] public recs;

  function delMem(uint256 x) external pure returns (uint256, uint256, uint8, address, uint256) {
    uint256[] memory xs = new uint256[](3);
    xs[0] = x;
    xs[1] = x;
    xs[2] = x;
    delete xs[1];
    S memory s = S(x, 7, address(1));
    delete s.b;
    uint256 y = x;
    delete y;
    S memory t = S(x, 9, address(2));
    delete t;
    return (xs[0] / 2 + xs[1] + xs[2] / 2, s.a, s.b, t.c, y + t.a);
  }
  function pushRef(uint256 x) external returns (uint256, uint256) {
    arr.push() = x;
    uint256 n = arr.length;
    S storage r = recs.push();
    r.a = x;
    r.b = 3;
    return (n, recs[recs.length - 1].a / 2 + recs[recs.length - 1].b);
  }
  function blobOps(bytes1 x) external returns (uint256, bytes1) {
    blob.push(x);
    blob.push();
    blob.push(0x7f);
    blob.pop();
    return (blob.length, blob[0]);
  }
}

def iRet : SourceUnit := sol% interface IRet {
  function get() external view returns (uint256[] memory);
  function str() external view returns (string memory);
}

def retUser : SourceUnit := sol% contract RetUser {
  function fetch(address a) external view returns (uint256) { return IRet(a).get().length; }
  function fetchStr(address a) external view returns (uint256) { return bytes(IRet(a).str()).length; }
  function tryFetch(address a) external view returns (uint256) {
    try IRet(a).get() returns (uint256[] memory xs) { return xs.length; } catch { return 99; }
  }
}

def storeStr : SourceUnit := sol% contract StoreStr {
  struct R { uint128 a; string s; }
  string public sname;
  bytes public sblob;
  R public rec;
  uint256[] public nums;

  function len(bytes memory b) internal pure returns (uint256) { return b.length; }
  function hashes() external view returns (bytes32, bytes32, bytes32, bytes32) {
    return (keccak256(bytes(sname)), keccak256(sblob), sha256(sblob), keccak256(abi.encodePacked(sname, sblob)));
  }
  function cat() external view returns (bytes memory, string memory, uint256) {
    return (bytes.concat(sblob, hex"00", bytes(sname)), string.concat(sname, "-", sname), bytes(sname).length);
  }
  function first() external view returns (bytes1, bytes1) { return (bytes(sname)[0], sblob[0]); }
  function eq(string calldata t) external view returns (bool) { return keccak256(bytes(sname)) == keccak256(bytes(t)); }
  function pass() external view returns (uint256) { return len(bytes(sname)) + len(sblob); }
  function enc() external view returns (bytes memory, bytes memory, bytes memory) {
    return (abi.encode(rec, nums), abi.encodePacked(sname, uint8(1), sblob), abi.encodeWithSignature("f(string)", sname));
  }
  function fixedOf() external view returns (bytes32, bytes4, bytes2) {
    return (bytes32(sblob), bytes4(sblob), bytes2(bytes(sname)));
  }
}

def envProgram : Program := [envC]
def hashProgram : Program := [hashC]
def ripProgram : Program := [ripC]
def abiProgram : Program := [iThing, abiC]
def fixedProgram : Program := [abiFixedC]
def typeProgram : Program := [iThing, small, oBase, oDer, typeInfoC]
def convProgram : Program := [iThing, convC]
def memProgram : Program := [memOpsC]
def retProgram : Program := [iRet, retUser]
def strProgram : Program := [storeStr]

end Builtins.SoliditySpec
