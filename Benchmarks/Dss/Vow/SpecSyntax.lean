import Benchmarks.Dss.Vow.Spec
import Solm.Notation

/-!
# Vow spec in the Solidity-faithful Solm frontend

The whole `vow.sol` spec written with `solidity%` and proven definitionally equal to the AST
spec in `Spec.lean`.  Checked-math helpers live as the internal `add`/`sub`/`min` functions and
their inlined uses; `{view}` marks the permission-free `vat.dai`/`vat.sin` reads; `extCodeSize`
guards on storage receivers use `${…}` escapes.  Transition order matches `contract.transitions`
(selector order).
-/

open Solm Solm.Notation Benchmarks.Dss.Vow

namespace Benchmarks.Dss.Vow.Syntax

def contractSyntax : ContractDecl := solidity% contract Vow {
  mapping(address => uint256) wards;
  address vat;
  address flapper;
  address flopper;
  mapping(uint256 => uint256) sin;
  uint256 Sin;
  uint256 Ash;
  uint256 wait;
  uint256 dump;
  uint256 sump;
  uint256 bump;
  uint256 hump;
  uint256 live;

  constructor(address vat_, address flapper_, address flopper_) {
    wards[msg.sender] = 1;
    vat = vat_;
    flapper = flapper_;
    flopper = flopper_;
    require(vat_.code.length > 0);
    var _hopeRet = vat_.hope(flapper_);
    live = 1;
  }

  function add(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x + y) as uint256;
    require(z >= x);
    return z;
  }

  function sub(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x - y) as uint256;
    require(z <= x);
    return z;
  }

  function min(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = x <= y ? x : y;
    return z;
  }

  function Ash() external returns (uint256) {
    return Ash;
  }

  function Sin() external returns (uint256) {
    return Sin;
  }

  function bump() external returns (uint256) {
    return bump;
  }

  function cage() external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    live = 0;
    Sin = 0;
    Ash = 0;
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var flapperDai = vat.dai{view}(flapper);
    require(${Expr.extCodeSize (.storage flapperRef)} > 0);
    var _flapCageRet = flapper.cage(flapperDai);
    require(${Expr.extCodeSize (.storage flopperRef)} > 0);
    var _flopCageRet = flopper.cage();
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var vatDai = vat.dai{view}(this);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var vatSin = vat.sin{view}(this);
    var healRad = min(vatDai, vatSin);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _healRet = vat.heal(healRad);
  }

  function deny(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 0;
  }

  function dump() external returns (uint256) {
    return dump;
  }

  function fess(uint256 tab) external {
    require(wards[msg.sender] == 1);
    uint256 sinNew = (sin[block.timestamp] + tab) as uint256;
    require(sinNew >= sin[block.timestamp]);
    sin[block.timestamp] = sinNew;
    uint256 SinNew = (Sin + tab) as uint256;
    require(SinNew >= Sin);
    Sin = SinNew;
  }

  function file(bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x7761697400000000000000000000000000000000000000000000000000000000)) {
      wait = data;
    } else if (what == bytes32(0x62756d7000000000000000000000000000000000000000000000000000000000)) {
      bump = data;
    } else if (what == bytes32(0x73756d7000000000000000000000000000000000000000000000000000000000)) {
      sump = data;
    } else if (what == bytes32(0x64756d7000000000000000000000000000000000000000000000000000000000)) {
      dump = data;
    } else if (what == bytes32(0x68756d7000000000000000000000000000000000000000000000000000000000)) {
      hump = data;
    } else {
      require(false);
    }
  }

  function file(bytes32 what, address data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x666c617070657200000000000000000000000000000000000000000000000000)) {
      require(${Expr.extCodeSize (.storage vatRef)} > 0);
      var _nopeRet = vat.nope(flapper);
      flapper = data;
      require(${Expr.extCodeSize (.storage vatRef)} > 0);
      var _hopeRet = vat.hope(data);
    } else if (what == bytes32(0x666c6f7070657200000000000000000000000000000000000000000000000000)) {
      flopper = data;
    } else {
      require(false);
    }
  }

  function flap() external returns (uint256) {
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var vatSin0 = vat.sin{view}(this);
    var surplus0 = add(vatSin0, bump);
    var surplusNeed = add(surplus0, hump);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var vatDai = vat.dai{view}(this);
    require(vatDai >= surplusNeed);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var vatSin1 = vat.sin{view}(this);
    var freeSin = sub(vatSin1, Sin);
    var debt = sub(freeSin, Ash);
    require(debt == 0);
    require(${Expr.extCodeSize (.storage flapperRef)} > 0);
    var id = flapper.kick(bump, 0);
    return id;
  }

  function flapper() external returns (address) {
    return flapper;
  }

  function flog(uint256 era) external {
    var doneAt = add(era, wait);
    require(doneAt <= block.timestamp);
    var SinNew = sub(Sin, sin[era]);
    Sin = SinNew;
    sin[era] = 0;
  }

  function flop() external returns (uint256) {
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var vatSin = vat.sin{view}(this);
    var freeSin = sub(vatSin, Sin);
    var flopDebt = sub(freeSin, Ash);
    require(sump <= flopDebt);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var vatDai = vat.dai{view}(this);
    require(vatDai == 0);
    var AshNew = add(Ash, sump);
    Ash = AshNew;
    require(${Expr.extCodeSize (.storage flopperRef)} > 0);
    var id = flopper.kick(this, dump, sump);
    return id;
  }

  function flopper() external returns (address) {
    return flopper;
  }

  function heal(uint256 rad) external {
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var vatDai = vat.dai{view}(this);
    require(rad <= vatDai);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var vatSin = vat.sin{view}(this);
    var freeSin = sub(vatSin, Sin);
    var healDebt = sub(freeSin, Ash);
    require(rad <= healDebt);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _healRet = vat.heal(rad);
  }

  function hump() external returns (uint256) {
    return hump;
  }

  function kiss(uint256 rad) external {
    require(rad <= Ash);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var vatDai = vat.dai{view}(this);
    require(rad <= vatDai);
    var AshNew = sub(Ash, rad);
    Ash = AshNew;
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _healRet = vat.heal(rad);
  }

  function live() external returns (uint256) {
    return live;
  }

  function rely(address usr) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    wards[usr] = 1;
  }

  function sin(uint256 arg0) external returns (uint256) {
    return sin[arg0];
  }

  function sump() external returns (uint256) {
    return sump;
  }

  function vat() external returns (address) {
    return vat;
  }

  function wait() external returns (uint256) {
    return wait;
  }

  function wards(address arg0) external returns (uint256) {
    return wards[arg0];
  }
}

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Vow.contract := by rfl

end Benchmarks.Dss.Vow.Syntax
