import Benchmarks.Dss.Flipper.Spec
import Solm.Notation

/-!
# Flipper spec in the Solidity-faithful Solm frontend

The whole `flip.sol` spec written with `solidity%` and proven definitionally equal to the AST
spec in `Spec.lean`.  Checked-math helper statement lists are inlined; the `Bid.end` field is
the guillemet-escaped `«end»`; `extCodeSize` guards on storage receivers use `${…}` escapes.
Transition order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation Benchmarks.Dss.Flipper

namespace Benchmarks.Dss.Flipper.Syntax

def contractSyntax : ContractDecl := solidity% contract Flipper {
  struct Bid {
    uint256 bid;
    uint256 lot;
    address guy;
    uint48 tic;
    uint48 «end»;
    address usr;
    address gal;
    uint256 tab;
  }

  mapping(address => uint256) wards;
  mapping(uint256 => Bid) bids;
  address vat;
  bytes32 ilk;
  uint256 beg;
  uint48 ttl;
  uint48 tau;
  uint256 kicks;
  address cat;

  constructor(address vat_, address cat_, bytes32 ilk_) {
    beg = #defaultBeg;
    ttl = #defaultTtl;
    tau = #defaultTau;
    kicks = 0;
    vat = vat_;
    cat = cat_;
    ilk = ilk_;
    wards[msg.sender] = 1;
  }

  function add(uint48 x, uint48 y) internal returns (uint48) {
    uint48 z = (x + y) % #uint48Modulus;
    require(z >= x);
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

  function bids(uint256 arg0) external returns (uint256, uint256, address, uint48, uint48, address, address, uint256) {
    return (bids[arg0].bid, bids[arg0].lot, bids[arg0].guy, bids[arg0].tic,
      bids[arg0].«end», bids[arg0].usr, bids[arg0].gal, bids[arg0].tab);
  }

  function cat() external returns (address) {
    return cat;
  }

  function deal(uint256 id) external {
    require(bids[id].tic != 0 && (bids[id].tic < block.timestamp || bids[id].«end» < block.timestamp));
    require(${Expr.extCodeSize (.storage catRef)} > 0);
    var _clawRet = cat.claw(bids[id].tab);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _fluxRet = vat.flux(ilk, this, bids[id].guy, bids[id].lot);
    delete bids[id];
  }

  function dent(uint256 id, uint256 lot, uint256 bid) external {
    require(bids[id].guy != address(0));
    require(bids[id].tic > block.timestamp || bids[id].tic == 0);
    require(bids[id].«end» > block.timestamp);
    require(bid == bids[id].bid);
    require(bid == bids[id].tab);
    require(lot < bids[id].lot);
    uint256 lotOne = (bids[id].lot * #ONE) as uint256;
    require(#ONE == 0 || lotOne / #ONE == bids[id].lot);
    uint256 begLot = (beg * lot) as uint256;
    require(lot == 0 || begLot / lot == beg);
    require(begLot <= lotOne);
    if (msg.sender != bids[id].guy) {
      require(${Expr.extCodeSize (.storage vatRef)} > 0);
      var _refundRet = vat.move(msg.sender, bids[id].guy, bid);
      bids[id].guy = msg.sender;
    }
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _fluxRet = vat.flux(ilk, this, bids[id].usr, (bids[id].lot - lot) % #wordModulus);
    bids[id].lot = lot;
    uint48 tic_ = (block.timestamp % #uint48Modulus + ttl) % #uint48Modulus;
    require(tic_ >= block.timestamp % #uint48Modulus);
    bids[id].tic = tic_;
  }

  function deny(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 0;
  }

  function file(bytes32 what, address data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x6361740000000000000000000000000000000000000000000000000000000000)) {
      cat = data;
    } else {
      require(false);
    }
  }

  function file(bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x6265670000000000000000000000000000000000000000000000000000000000)) {
      beg = data;
    } else if (what == bytes32(0x74746c0000000000000000000000000000000000000000000000000000000000)) {
      ttl = data % #uint48Modulus;
    } else if (what == bytes32(0x7461750000000000000000000000000000000000000000000000000000000000)) {
      tau = data % #uint48Modulus;
    } else {
      require(false);
    }
  }

  function ilk() external returns (bytes32) {
    return ilk;
  }

  function kick(address usr, address gal, uint256 tab, uint256 lot, uint256 bid) external returns (uint256) {
    require(wards[msg.sender] == 1);
    require(kicks < #maxUint256);
    uint256 id = (kicks + 1) % #wordModulus;
    kicks = id;
    bids[id].bid = bid;
    bids[id].lot = lot;
    bids[id].guy = msg.sender;
    uint48 end_ = (block.timestamp % #uint48Modulus + tau) % #uint48Modulus;
    require(end_ >= block.timestamp % #uint48Modulus);
    bids[id].«end» = end_;
    bids[id].usr = usr;
    bids[id].gal = gal;
    bids[id].tab = tab;
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _fluxRet = vat.flux(ilk, msg.sender, this, lot);
    return id;
  }

  function kicks() external returns (uint256) {
    return kicks;
  }

  function rely(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 1;
  }

  function tau() external returns (uint48) {
    return tau;
  }

  function tend(uint256 id, uint256 lot, uint256 bid) external {
    require(bids[id].guy != address(0));
    require(bids[id].tic > block.timestamp || bids[id].tic == 0);
    require(bids[id].«end» > block.timestamp);
    require(lot == bids[id].lot);
    require(bid <= bids[id].tab);
    require(bid > bids[id].bid);
    uint256 bidOne = (bid * #ONE) as uint256;
    require(#ONE == 0 || bidOne / #ONE == bid);
    uint256 begBid = (beg * bids[id].bid) as uint256;
    require(bids[id].bid == 0 || begBid / bids[id].bid == beg);
    require(bidOne >= begBid || bid == bids[id].tab);
    if (msg.sender != bids[id].guy) {
      require(${Expr.extCodeSize (.storage vatRef)} > 0);
      var _refundRet = vat.move(msg.sender, bids[id].guy, bids[id].bid);
      bids[id].guy = msg.sender;
    }
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _payRet = vat.move(msg.sender, bids[id].gal, (bid - bids[id].bid) % #wordModulus);
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
    require(wards[msg.sender] == 1);
    require(bids[id].guy != address(0));
    require(bids[id].bid < bids[id].tab);
    require(${Expr.extCodeSize (.storage catRef)} > 0);
    var _clawRet = cat.claw(bids[id].tab);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _fluxRet = vat.flux(ilk, this, msg.sender, bids[id].lot);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _moveRet = vat.move(msg.sender, bids[id].guy, bids[id].bid);
    delete bids[id];
  }
}

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Flipper.contract := by rfl

end Benchmarks.Dss.Flipper.Syntax
