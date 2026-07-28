import Benchmarks.Dss.Flopper.Spec
import Solm.Notation

/-!
# Flopper spec in the Solidity-faithful Solm frontend

The whole `flop.sol` spec written with `solidity%` and proven definitionally equal to the AST
spec in `Spec.lean`.  Checked-math helper statement lists are inlined; the `Bid.end` field is
the guillemet-escaped `«end»`; `extCodeSize` guards on storage receivers use `${…}` escapes.
The `Ash`/`kiss` external calls in `dent` have a storage *path* receiver (`bids[id].guy`),
which the surface call form cannot express, so those two checked calls are `${…}` statement
splices of the spec's own `checkedExternalCallStmts`.  Transition order matches
`contract.transitions` (selector order).
-/

open Solm Solm.Notation Benchmarks.Dss.Flopper

namespace Benchmarks.Dss.Flopper.Syntax

def contractSyntax : ContractDecl := solidity% contract Flopper {
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
  uint256 pad;
  uint48 ttl;
  uint48 tau;
  uint256 kicks;
  uint256 live;
  address vow;

  constructor(address vat_, address gem_) {
    beg = #defaultBeg;
    pad = #defaultPad;
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

  function mul(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x * y) as uint256;
    require(y == 0 || z / y == x);
    return z;
  }

  function min(uint256 x, uint256 y) internal returns (uint256) {
    if (x > y) {
      return y;
    } else {
      return x;
    }
  }

  function beg() external returns (uint256) {
    return beg;
  }

  function bids(uint256 arg0) external returns (uint256, uint256, address, uint48, uint48) {
    return (bids[arg0].bid, bids[arg0].lot, bids[arg0].guy, bids[arg0].tic, bids[arg0].«end»);
  }

  function cage() external {
    require(wards[msg.sender] == 1);
    live = 0;
    vow = msg.sender;
  }

  function deal(uint256 id) external {
    require(live == 1);
    require(bids[id].tic != 0 && (bids[id].tic < block.timestamp || bids[id].«end» < block.timestamp));
    require(${Expr.extCodeSize (.storage gemRef)} > 0);
    var _mintRet = gem.mint(bids[id].guy, bids[id].lot);
    delete bids[id];
  }

  function dent(uint256 id, uint256 lot, uint256 bid) external {
    require(live == 1);
    require(bids[id].guy != address(0));
    require(bids[id].tic > block.timestamp || bids[id].tic == 0);
    require(bids[id].«end» > block.timestamp);
    require(bid == bids[id].bid);
    require(lot < bids[id].lot);
    uint256 begLot = (beg * lot) as uint256;
    require(lot == 0 || begLot / lot == beg);
    uint256 lotOne = (bids[id].lot * #ONE) as uint256;
    require(#ONE == 0 || lotOne / #ONE == bids[id].lot);
    require(begLot <= lotOne);
    if (msg.sender != bids[id].guy) {
      require(${Expr.extCodeSize (.storage vatRef)} > 0);
      var _moveRet = vat.move(msg.sender, bids[id].guy, bid);
      if (bids[id].tic == 0) {
        ${checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash" (.intLit 0) [] "Ash"}
        var kissAmt = min(bid, ${Expr.var "Ash"});
        ${checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss" (.intLit 0) [.var "kissAmt"] "_kissRet"}
      }
      bids[id].guy = msg.sender;
    }
    bids[id].lot = lot;
    uint48 tic_ = (block.timestamp % #uint48Modulus + ttl) % #uint48Modulus;
    require(tic_ >= block.timestamp % #uint48Modulus);
    bids[id].tic = tic_;
  }

  function deny(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 0;
  }

  function file(bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x6265670000000000000000000000000000000000000000000000000000000000)) {
      beg = data;
    } else if (what == bytes32(0x7061640000000000000000000000000000000000000000000000000000000000)) {
      pad = data;
    } else if (what == bytes32(0x74746c0000000000000000000000000000000000000000000000000000000000)) {
      ttl = data % #uint48Modulus;
    } else if (what == bytes32(0x7461750000000000000000000000000000000000000000000000000000000000)) {
      tau = data % #uint48Modulus;
    } else {
      require(false);
    }
  }

  function gem() external returns (address) {
    return gem;
  }

  function kick(address gal, uint256 lot, uint256 bid) external returns (uint256) {
    require(wards[msg.sender] == 1);
    require(live == 1);
    require(kicks < #maxUint256);
    uint256 id = kicks + 1;
    kicks = id;
    bids[id].bid = bid;
    bids[id].lot = lot;
    bids[id].guy = gal;
    uint48 end_ = (block.timestamp % #uint48Modulus + tau) % #uint48Modulus;
    require(end_ >= block.timestamp % #uint48Modulus);
    bids[id].«end» = end_;
    return id;
  }

  function kicks() external returns (uint256) {
    return kicks;
  }

  function live() external returns (uint256) {
    return live;
  }

  function pad() external returns (uint256) {
    return pad;
  }

  function rely(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 1;
  }

  function tau() external returns (uint48) {
    return tau;
  }

  function tick(uint256 id) external {
    require(bids[id].«end» < block.timestamp);
    require(bids[id].tic == 0);
    uint256 lotBase = (pad * bids[id].lot) as uint256;
    require(bids[id].lot == 0 || lotBase / bids[id].lot == pad);
    bids[id].lot = lotBase / #ONE;
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

  function vow() external returns (address) {
    return vow;
  }

  function wards(address arg0) external returns (uint256) {
    return wards[arg0];
  }

  function yank(uint256 id) external {
    require(live == 0);
    require(bids[id].guy != address(0));
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _suckRet = vat.suck(vow, bids[id].guy, bids[id].bid);
    delete bids[id];
  }
}

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Flopper.contract := by rfl

end Benchmarks.Dss.Flopper.Syntax
