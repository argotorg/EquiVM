import Benchmarks.Dss.Flapper.Spec
import Solm.Notation

/-!
# Flapper spec in the Solidity-faithful Solm frontend

The whole `flap.sol` spec written with `solidity%` and proven definitionally equal to the AST spec
in `Spec.lean`.  Checked-math helpers are inlined (uint48 adds are the explicit
`% #uint48Modulus` wraps); the struct field `end` is guillemet-escaped; `extCodeSize` guards on
the storage `vat`/`gem` receivers use the `${…}` escape.  Transition order matches
`contract.transitions` (selector order).
-/

open Solm Solm.Notation Benchmarks.Dss.Flapper

namespace Benchmarks.Dss.Flapper.Syntax

def contractSyntax : ContractDecl := solidity% contract Flapper {
  struct Bid {
    uint256 bid;
    uint256 lot;
    address guy;
    uint48 tic;
    uint48 «end»;
  }

  mapping(address => uint256) wards;
  mapping(uint256 => Bid) bids;
  address vat;
  address gem;
  uint256 beg;
  uint48 ttl;
  uint48 tau;
  uint256 kicks;
  uint256 live;
  uint256 lid;
  uint256 fill;

  constructor(address vat_, address gem_) {
    beg = #defaultBeg;
    ttl = #defaultTtl;
    tau = #defaultTau;
    kicks = 0;
    wards[msg.sender] = 1;
    vat = vat_;
    gem = gem_;
    live = 1;
  }

  function add(uint48 x, uint48 y) internal returns (uint48) {
    uint48 z = (x + y) % #uint48Modulus;
    require(z >= x);
    return z;
  }

  function add256(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x + y) as uint256;
    require(z >= x);
    return z;
  }

  function sub(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x - y) as uint256;
    require(z <= x);
    return z;
  }

  function mul(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x * y) as uint256;
    require(y == 0 || z / y == x);
    return z;
  }

  function beg() external returns (uint256) {
    return beg;
  }

  function bids(uint256 arg0) external returns (uint256, uint256, address, uint48, uint48) {
    return (bids[arg0].bid, bids[arg0].lot, bids[arg0].guy, bids[arg0].tic, bids[arg0].«end»);
  }

  function cage(uint256 rad) external {
    require(wards[msg.sender] == 1);
    live = 0;
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _moveRet = vat.move(address(this), msg.sender, rad);
  }

  function deal(uint256 id) external {
    require(live == 1);
    require(bids[id].tic != 0 && (bids[id].tic < block.timestamp || bids[id].«end» < block.timestamp));
    uint256 lot = bids[id].lot;
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _moveRet = vat.move(address(this), bids[id].guy, lot);
    require(${Expr.extCodeSize (.storage gemRef)} > 0);
    var _burnRet = gem.burn(address(this), bids[id].bid);
    delete bids[id];
    var fillNew = sub(fill, lot);
    fill = fillNew;
  }

  function deny(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 0;
  }

  function file(bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x6265670000000000000000000000000000000000000000000000000000000000)) {
      beg = data;
    } else if (what == bytes32(0x74746c0000000000000000000000000000000000000000000000000000000000)) {
      ttl = data % #uint48Modulus;
    } else if (what == bytes32(0x7461750000000000000000000000000000000000000000000000000000000000)) {
      tau = data % #uint48Modulus;
    } else if (what == bytes32(0x6c69640000000000000000000000000000000000000000000000000000000000)) {
      lid = data;
    } else {
      require(false);
    }
  }

  function fill() external returns (uint256) {
    return fill;
  }

  function gem() external returns (address) {
    return gem;
  }

  function kick(uint256 lot, uint256 bid) external returns (uint256) {
    require(wards[msg.sender] == 1);
    require(live == 1);
    require(kicks < #maxUint256);
    uint256 fillNew = (fill + lot) as uint256;
    require(fillNew >= fill);
    fill = fillNew;
    require(fill <= lid);
    uint256 id = (kicks + 1) as uint256;
    require(id >= kicks);
    kicks = id;
    bids[id].bid = bid;
    bids[id].lot = lot;
    bids[id].guy = msg.sender;
    uint48 end_ = (block.timestamp % #uint48Modulus + tau) % #uint48Modulus;
    require(end_ >= block.timestamp % #uint48Modulus);
    bids[id].«end» = end_;
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _moveRet = vat.move(msg.sender, address(this), lot);
    return id;
  }

  function kicks() external returns (uint256) {
    return kicks;
  }

  function lid() external returns (uint256) {
    return lid;
  }

  function live() external returns (uint256) {
    return live;
  }

  function rely(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 1;
  }

  function tau() external returns (uint48) {
    return tau;
  }

  function tend(uint256 id, uint256 lot, uint256 bid) external {
    require(live == 1);
    require(bids[id].guy != address(0));
    require(bids[id].tic > block.timestamp || bids[id].tic == 0);
    require(bids[id].«end» > block.timestamp);
    require(lot == bids[id].lot);
    require(bid > bids[id].bid);
    uint256 bidOne = (bid * #ONE) as uint256;
    require(#ONE == 0 || bidOne / #ONE == bid);
    uint256 begBid = (beg * bids[id].bid) as uint256;
    require(bids[id].bid == 0 || begBid / bids[id].bid == beg);
    require(bidOne >= begBid);
    if (msg.sender != bids[id].guy) {
      require(${Expr.extCodeSize (.storage gemRef)} > 0);
      var _refundRet = gem.move(msg.sender, bids[id].guy, bids[id].bid);
      bids[id].guy = msg.sender;
    }
    require(${Expr.extCodeSize (.storage gemRef)} > 0);
    var _payRet = gem.move(msg.sender, address(this), (bid - bids[id].bid) % #wordModulus);
    bids[id].bid = bid;
    uint48 tic_ = (block.timestamp % #uint48Modulus + ttl) % #uint48Modulus;
    require(tic_ >= block.timestamp % #uint48Modulus);
    bids[id].tic = tic_;
  }

  function tick(uint256 id) external {
    require(bids[id].«end» < block.timestamp);
    require(bids[id].tic == 0);
    uint48 end_ = (block.timestamp % #uint48Modulus + tau) % #uint48Modulus;
    require(end_ >= block.timestamp % #uint48Modulus);
    bids[id].«end» = end_;
  }

  function ttl() external returns (uint48) {
    return ttl;
  }

  function vat() external returns (address) {
    return vat;
  }

  function wards(address arg0) external returns (uint256) {
    return wards[arg0];
  }

  function yank(uint256 id) external {
    require(live == 0);
    require(bids[id].guy != address(0));
    require(${Expr.extCodeSize (.storage gemRef)} > 0);
    var _moveRet = gem.move(address(this), bids[id].guy, bids[id].bid);
    delete bids[id];
  }
}

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Flapper.contract := by rfl

end Benchmarks.Dss.Flapper.Syntax
