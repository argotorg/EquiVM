import Solidity

/-! Udvt (`Solidity/Test/Fixtures/Udvt.sol`).  Harness input only. -/

namespace Udvt.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def tPrice : SourceUnit := sol% type Price is uint128;

def tFlag : SourceUnit := sol% type Flag is bool;

def tWho : SourceUnit := sol% type Who is address;

def tTag : SourceUnit := sol% type Tag is bytes4;

def tDelta : SourceUnit := sol% type Delta is int64;

def tWide : SourceUnit := sol% type Wide is uint256;

def fileK : SourceUnit := sol% Price constant FILE_K = Price.wrap(3);

def usingPrice : SourceUnit := sol% using {pinc, padd, peq as ==, psum as +, pnot as ~} for Price global;

def usingFlag : SourceUnit := sol% using {flip} for Flag;

def fnPinc : SourceUnit := sol% function pinc(Price a) pure returns (Price) { return Price.wrap(Price.unwrap(a) + 1); }

def fnPadd : SourceUnit := sol% function padd(Price a, uint128 amt) pure returns (Price) { return Price.wrap(Price.unwrap(a) + amt); }

def fnPeq : SourceUnit := sol% function peq(Price a, Price b) pure returns (bool) { return Price.unwrap(a) == Price.unwrap(b); }

def fnPsum : SourceUnit := sol% function psum(Price a, Price b) pure returns (Price) { return Price.wrap(Price.unwrap(a) + Price.unwrap(b)); }

def fnPnot : SourceUnit := sol% function pnot(Price a) pure returns (Price) { return Price.wrap(~Price.unwrap(a)); }

def fnFlip : SourceUnit := sol% function flip(Flag f) pure returns (Flag) { return Flag.wrap(!Flag.unwrap(f)); }

def fnTwice : SourceUnit := sol% function twice(uint256 a) pure returns (uint256) { return 2 * a; }

def fnInc2 : SourceUnit := sol% function inc2(Price a) pure returns (Price) { return a.pinc().pinc(); }

def time : SourceUnit := sol% library Time {
  using Time for *;
  type Delay is uint112;
  function toDelay(uint32 d) internal pure returns (Delay) { return Delay.wrap(d); }
  function get(Delay self) internal pure returns (uint32) { return uint32(Delay.unwrap(self)); }
  function longer(Delay self, uint32 other) internal pure returns (Delay) { return self.get() > other ? self : other.toDelay(); }
  function pack(uint32 hi, uint32 lo) internal pure returns (Delay) { return Delay.wrap((uint112(hi) << 32) | lo); }
}

def pl : SourceUnit := sol% library PL {
  using {own} for Price;
  function dbl(Price a) internal pure returns (Price) { return Price.wrap(2 * Price.unwrap(a)).pinc(); }
  function half(Price a) internal pure returns (Price) { return Price.wrap(Price.unwrap(a) / 2); }
  function own(Price a) internal pure returns (Price) { return a; }
  function viaOwn(Price a) internal pure returns (Price) { return half(a.own()); }
}

def pm : SourceUnit := sol% library PM {
  function sq(Price a) internal pure returns (Price) { return Price.wrap(Price.unwrap(a) * Price.unwrap(a)); }
  function half(Price a, uint128 d) internal pure returns (Price) { return Price.wrap(Price.unwrap(a) / d); }
}

def udvt : SourceUnit := sol% contract Udvt {
  Price public price;
  Delta public delta;
  Flag public flag;
  Who public who;
  Tag public tag;
  Wide public wide;
  mapping(Price => Wide) public byPrice;
  mapping(Who => mapping(Tag => Flag)) public marks;
  Price[] public prices;
  struct Quote { Price bid; Price ask; Who maker; Flag live; }
  Quote public quote;
  Price constant TEN = Price.wrap(10);

  event Set(Price indexed p, Delta d, Who indexed w, Tag t);
  error TooHigh(Price p, Price cap);

  function setSome(Price p, Delta d, Flag f) external { price = p; delta = d; flag = f; }
  function setRest(Who w, Tag t, Wide x) external { who = w; tag = t; wide = x; emit Set(price, delta, w, t); }
  function wrap3(uint128 p, int64 d, bool f) external pure returns (Price, Delta, Flag) {
    return (Price.wrap(p), Delta.wrap(d), Flag.wrap(f));
  }
  function wrap2(address w, bytes4 t) external pure returns (Who, Tag) { return (Who.wrap(w), Tag.wrap(t)); }
  function unwrap3(Price p, Delta d, Flag f) external pure returns (uint128, int64, bool) {
    return (Price.unwrap(p), Delta.unwrap(d), Flag.unwrap(f));
  }
  function unwrap2(Who w, Tag t) external pure returns (address, bytes4) { return (Who.unwrap(w), Tag.unwrap(t)); }
  function widen(uint8 x, int8 y) external pure returns (Price, Delta) { return (Price.wrap(x), Delta.wrap(y)); }
  function lits() external pure returns (Price, Tag, Tag, Who, Flag, Delta) {
    return (Price.wrap(7), Tag.wrap("abcd"), Tag.wrap(0x12345678), Who.wrap(address(0x1234)), Flag.wrap(true), Delta.wrap(-5));
  }
  function sum(Price a, Price b) external pure returns (Price) { return Price.wrap(Price.unwrap(a) + Price.unwrap(b)); }
  function capped(Price p) external pure returns (Price) {
    if (Price.unwrap(p) > Price.unwrap(TEN)) revert TooHigh(p, TEN);
    return p;
  }
  function put(Price k, Wide v) external { byPrice[k] = v; }
  function mark(Who w, Tag t, Flag f) external { marks[w][t] = f; }
  function push(Price p) external returns (uint256) { prices.push(p); return prices.length; }
  function pop() external returns (Price) { Price last = prices[prices.length - 1]; prices.pop(); return last; }
  function setQuote(Price bid, Price ask, Who maker) external { quote = Quote(bid, ask, maker, Flag.wrap(true)); }
  function spread() external view returns (uint128) { Quote memory q = quote; return Price.unwrap(q.ask) - Price.unwrap(q.bid); }
  function clear() external { delete quote; delete prices; }
  function pick(bool c, Price a, Price b) external pure returns (Price) { return c ? a : b; }
  function same(Price p) external pure returns (Price) { return Price(p); }
  function zeros() external pure returns (Price p, Flag f, Who w, Tag t, Delta d) { }
  function locals(uint128 x) external pure returns (uint128) { Price p; Price q = Price.wrap(x); p = q; return Price.unwrap(p); }
  function shadow(uint128 Price) external pure returns (uint128) { return Price + 1; }
  function fileK() external pure returns (Price) { return FILE_K; }
}

def udvtAbi : SourceUnit := sol% contract UdvtAbi {
  function enc(Price p, Tag t, Flag f) external pure returns (bytes memory, bytes memory) {
    return (abi.encode(p, t, f), abi.encodePacked(p, t, f));
  }
  function dec(bytes calldata d) external pure returns (Price, Delta, Flag) { return abi.decode(d, (Price, Delta, Flag)); }
  function sumArr(Price[] calldata xs) external pure returns (uint256 s) {
    for (uint256 i = 0; i < xs.length; i++) { s += Price.unwrap(xs[i]); }
  }
  function flagAt(Flag[] calldata fs, uint256 i) external pure returns (bool) { return Flag.unwrap(fs[i]); }
  function fixedArr(Price[2] memory ys) external pure returns (Price) { return ys[1]; }
  function mem(uint128 a, uint128 b) external pure returns (Price[] memory out) {
    out = new Price[](2);
    out[0] = Price.wrap(a);
    out[1] = Price.wrap(b);
  }
  function hash(Price p, Who w) external pure returns (bytes32) { return keccak256(abi.encode(p, w)); }
  function sel() external pure returns (bytes4) { return this.enc.selector; }
}

def udvtArr : SourceUnit := sol% contract UdvtArr {
  function flagMem(Flag[] memory fs, uint256 i) external pure returns (bool) { return Flag.unwrap(fs[i]); }
  function flagFixed(Flag[2] calldata fs, uint256 i) external pure returns (bool) { return Flag.unwrap(fs[i]); }
  function priceAt(Price[] calldata xs, uint256 i) external pure returns (Price) { return xs[i]; }
  function boolMem(bool[] memory bs, uint256 i) external pure returns (bool) { return bs[i]; }
  function boolFixed(bool[2] calldata bs, uint256 i) external pure returns (bool) { return bs[i]; }
}

def iOracle : SourceUnit := sol% interface IOracle {
  type Feed is bytes8;
  function quote(Feed f, Price p) external view returns (Price);
}

def oracle : SourceUnit := sol% contract Oracle is IOracle {
  function quote(Feed f, Price p) external pure returns (Price) { return Price.wrap(Price.unwrap(p) + uint64(Feed.unwrap(f))); }
}

def udvtCall : SourceUnit := sol% contract UdvtCall {
  function ask(IOracle o, IOracle.Feed f, Price p) external view returns (Price) { return o.quote(f, p); }
  function feed(bytes8 b) external pure returns (IOracle.Feed) { return IOracle.Feed.wrap(b); }
  function unfeed(IOracle.Feed f) external pure returns (bytes8) { return IOracle.Feed.unwrap(f); }
}

def uBase : SourceUnit := sol% contract UBase {
  type Id is uint32;
  Id internal last;
  function mk(uint32 x) internal pure returns (Id) { return Id.wrap(x); }
}

def uDer : SourceUnit := sol% contract UDer is UBase {
  type Slot is bytes32;
  Slot public slot;
  function ids(uint32 x) external returns (Id, UBase.Id) { last = mk(x); return (last, UBase.Id.wrap(x + 1)); }
  function keep(bytes32 s) external returns (Slot) { slot = Slot.wrap(s); return slot; }
  function delay(uint32 a, uint32 b) external pure returns (Time.Delay, uint32) {
    Time.Delay d = Time.pack(a, b);
    return (d, Time.get(d));
  }
  function plain(Id i, Slot s, Time.Delay d) external pure returns (uint32, bytes32, uint112) {
    return (Id.unwrap(i), Slot.unwrap(s), Time.Delay.unwrap(d));
  }
  function again(Id i, Time.Delay d) external pure returns (UBase.Id, Time.Delay) { return (UBase.Id(i), Time.Delay(d)); }
}

def udvtImm : SourceUnit := sol% contract UdvtImm {
  Price immutable base;
  Who immutable owner;
  Price constant K = Price.wrap(9);
  constructor(Price b) { base = b; owner = Who.wrap(msg.sender); }
  function get() external view returns (Price, Who, Price) { return (base, owner, K); }
  function above(Price p) external view returns (bool) { return Price.unwrap(p) > Price.unwrap(base); }
}

def udvtUsing : SourceUnit := sol% contract UdvtUsing {
  using {Time.get, Time.longer} for Time.Delay;
  using PL for Price;
  using PM for Price;
  using {twice} for uint256;
  using {pinc} for Price;
  Price public p;
  function bump(Price x) external pure returns (Price) { return x.pinc(); }
  function addTo(Price x, uint128 amt) external pure returns (Price) { return x.padd(amt).pinc(); }
  function named(Price x) external pure returns (Price) { return x.padd({amt: 3}); }
  function dbl(Price x) external pure returns (Price) { return x.dbl(); }
  function sq(Price x) external pure returns (Price) { return x.sq(); }
  function halves(Price x, uint128 d) external pure returns (Price, Price) { return (x.half(), x.half(d)); }
  function viaOwn(Price x) external pure returns (Price) { return PL.viaOwn(x); }
  function flipIt(Flag f) external pure returns (Flag) { return f.flip(); }
  function delay(uint32 a, uint32 b) external pure returns (uint32, Time.Delay) {
    Time.Delay d = Time.toDelay(a);
    return (d.get(), d.longer(b));
  }
  function tw(uint256 x) external pure returns (uint256) { return x.twice(); }
  function free2(Price x) external pure returns (Price) { return inc2(x); }
  function store(Price x) external returns (Price) { p = x.pinc(); return p.pinc(); }
}

def udvtOps : SourceUnit := sol% contract UdvtOps {
  uint256 public trace;
  function mk(uint128 i) internal returns (Price) { trace = trace * 10 + i; return Price.wrap(i); }
  function fail(uint128 i) internal pure returns (Price) { require(false, i == 1 ? "one" : "two"); return Price.wrap(i); }
  function ord() external returns (Price) { return mk(1) + mk(2); }
  function ordEq() external returns (bool) { return mk(3) == mk(4); }
  function bothFail() external pure returns (bool) { return fail(1) == fail(2); }
  function inv(Price p) external pure returns (Price) { return ~p; }
  function both(Price a, Price b) external pure returns (Price, bool) { return (a + b, a == b); }
}

def program : Program := [tPrice, tFlag, tWho, tTag, tDelta, tWide, fileK, usingPrice, usingFlag, fnPinc, fnPadd, fnPeq, fnPsum, fnPnot, fnFlip, fnTwice, fnInc2, time, pl, pm, udvt, udvtAbi, udvtArr, iOracle, oracle, udvtCall, uBase, uDer, udvtImm, udvtUsing, udvtOps]

end Udvt.SoliditySpec
