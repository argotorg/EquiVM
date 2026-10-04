import Solidity

/-! Data and Alloc (`Solidity/Test/Fixtures/Data.sol`, `Alloc.sol`): storage layout, arrays,
structs, memory references, `delete`, byte arrays; memory allocation limits.  Harness input only. -/

namespace Data.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def data : SourceUnit := sol% contract Data {
  struct Point { uint128 x; uint128 y; }
  struct Rec { address who; uint64 stamp; bool ok; uint256 amount; uint8[3] tags; }

  bool public flagA;
  uint8 public small8;
  address public addrB;
  uint16 public small16;
  int64 public sneg;
  bytes4 public tag;
  uint256[5] public fixedArr;
  uint8[] public smallArr;
  uint256[][] nested;
  Point public pt;
  Rec rcd;
  mapping(uint256 => Point) public points;
  Point[] public pts;
  bytes public blob;
  string public text;

  function packed(bool a, uint8 b, address c, uint16 d, int64 e, bytes4 t)
      external returns (bool, uint8, address, uint16, int64, bytes4) {
    flagA = a; small8 = b; addrB = c; small16 = d; sneg = e; tag = t;
    return (flagA, small8, addrB, small16, sneg, tag);
  }
  function packedBump(uint8 b, uint16 d, int64 e) external returns (uint8, uint16, int64) {
    small8 = b; small16 = d; sneg = e;
    small8 += 1; small16 -= 1; sneg -= 5;
    return (small8, small16, sneg);
  }
  function packedClear(uint8 b, address c) external returns (uint8, address, uint16) {
    small8 = b; addrB = c; small16 = 7;
    delete small8; delete addrB;
    return (small8, addrB, small16);
  }

  function fixedStore(uint256 i, uint256 v) external returns (uint256 s) {
    fixedArr[i] = v;
    for (uint256 k = 0; k < 5; k++) { s += fixedArr[k]; }
  }
  function fixedMem(uint256 a, uint256 b, uint256 i) external pure returns (uint256, uint256[3] memory) {
    uint256[3] memory r;
    r[0] = a; r[1] = b; r[2] = a + b;
    return (r[i], r);
  }

  function smallOps(uint8 a, uint8 b, uint8 c, uint256 i) external returns (uint256, uint256, uint8) {
    smallArr.push(a); smallArr.push(b); smallArr.push(c);
    smallArr.pop();
    smallArr[0] = c;
    uint256 s;
    for (uint256 k = 0; k < smallArr.length; k++) { s += smallArr[k]; }
    return (smallArr.length, s, smallArr[i]);
  }
  function smallMany(uint8 n) external returns (uint256 s) {
    for (uint256 k = 0; k < n; k++) { smallArr.push(uint8(k)); }
    for (uint256 k = 0; k < smallArr.length; k++) { s += smallArr[k]; }
  }
  function smallClear(uint8 a) external returns (uint256) {
    smallArr.push(a); smallArr.push(a);
    delete smallArr;
    return smallArr.length;
  }
  function popEmpty() external { smallArr.pop(); }

  function nestedOps(uint256 v, uint256 r, uint256 c) external returns (uint256, uint256, uint256) {
    nested.push(); nested.push();
    nested[0].push(v); nested[1].push(v + 1); nested[1].push(v + 2);
    return (nested.length, nested[1].length, nested[r][c]);
  }

  function ptOps(uint128 x, uint128 y, uint256 k) external returns (uint128, uint128, uint128, uint128) {
    pt = Point(x, y);
    points[k] = pt;
    pt.x = y;
    Point memory p = points[k];
    (p.x, p.y) = (p.y, p.x);
    pt = p;
    return (pt.x, pt.y, points[k].x, points[k].y);
  }
  function ptPtr(uint256 k, uint128 x) external returns (uint128, uint128) {
    Point storage p = points[k];
    p.x = x; p.y += 1;
    return (points[k].x, points[k].y);
  }
  function ptsOps(uint128 x, uint128 y, uint256 i) external returns (uint256, uint128, uint128) {
    pts.push(Point({x: x, y: y})); pts.push(Point({x: y, y: x}));
    delete pts[0];
    return (pts.length, pts[i].x, pts[i].y);
  }
  function recOps(address who, uint64 stamp, bool ok, uint256 amount, uint8 t)
      external returns (address, uint64, bool, uint256, uint8, uint8) {
    rcd.who = who; rcd.stamp = stamp; rcd.ok = ok; rcd.amount = amount; rcd.tags[1] = t; rcd.tags[2] = t;
    return (rcd.who, rcd.stamp, rcd.ok, rcd.amount, rcd.tags[1], rcd.tags[0]);
  }
  function recClear(address who, uint256 amount, uint8 t) external returns (address, uint256, uint8) {
    rcd.who = who; rcd.amount = amount; rcd.tags[2] = t;
    delete rcd;
    return (rcd.who, rcd.amount, rcd.tags[2]);
  }
  function pointClear(uint256 k, uint128 x) external returns (uint128) {
    points[k] = Point(x, x);
    delete points[k];
    return points[k].x;
  }

  function newArr(uint8 n) external pure returns (uint256[] memory a) {
    a = new uint256[](n);
    for (uint256 i = 0; i < n; i++) { a[i] = i * i; }
  }
  function newBytes(uint8 n) external pure returns (bytes memory b) {
    b = new bytes(n);
    if (n > 0) { b[0] = 0x41; }
  }
  function memAlias(uint256 v) external pure returns (uint256, uint256) {
    uint256[] memory a = new uint256[](2);
    uint256[] memory b = a;
    b[0] = v;
    return (a[0], a.length);
  }
  function memStruct(uint128 x) external pure returns (uint128, uint128) {
    Point memory p = Point(x, 1);
    Point memory q = p;
    q.x += 1;
    return (p.x, q.y);
  }
  function memCopy(uint128 x) external returns (uint128, uint128) {
    pt = Point(x, 2);
    Point memory p = pt;
    p.x += 5;
    return (pt.x, p.x);
  }

  function blobOps(bytes calldata b, uint256 i) external returns (uint256, bytes1) {
    blob = b;
    return (blob.length, blob[i]);
  }
  function blobClear(bytes calldata b) external returns (uint256) {
    blob = b;
    delete blob;
    return blob.length;
  }
  function blobSet(bytes calldata b, uint256 i, bytes1 x) external returns (bytes memory) {
    blob = b;
    blob[i] = x;
    return blob;
  }
  function textOps(string calldata s) external returns (string memory) {
    text = s;
    return text;
  }
}

def alloc : SourceUnit := sol% contract Alloc {
  function newWords(uint256 n) external pure returns (uint256) { uint256[] memory a = new uint256[](n); return a.length; }
  function newBytes(uint256 n) external pure returns (uint256) { bytes memory b = new bytes(n); return b.length; }
}

def program : Program := [data]
def allocProgram : Program := [alloc]

end Data.SoliditySpec
