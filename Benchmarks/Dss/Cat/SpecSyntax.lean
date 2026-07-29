import Benchmarks.Dss.Cat.Spec
import Solm.Notation

/-!
# Cat spec in the Solidity-faithful Solm frontend

The whole `cat.sol` spec written with `solidity%` and proven definitionally equal to the AST
spec in `Spec.lean`.  Checked-math helper stmt-lists and the extCodeSize-guarded external calls
are inlined as surface statements; `file` keys are big-endian `bytes32` literals.  Transition
order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.Cat.Syntax

def contractSyntax : ContractDecl := solidity% contract Cat {
  mapping(address => uint256) wards;
  mapping(bytes32 => Ilk) ilks;
  uint256 live;
  address vat;
  address vow;
  uint256 box;
  uint256 litter;

  struct Ilk {
    address flip;
    uint256 chop;
    uint256 dunk;
  }

  constructor(address vat_) {
    wards[msg.sender] = 1;
    vat = vat_;
    live = 1;
  }

  function min(uint256 x, uint256 y) internal returns (uint256) {
    if (x > y) {
      return y;
    } else {
      return x;
    }
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

  function mul(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x * y) as uint256;
    require(y == 0 || z / y == x);
    return z;
  }

  function bite(bytes32 ilk, address urn) external returns (uint256) {
    require(vat.code.length > 0);
    var vatIlk = vat.ilks{view}(ilk);
    uint256 rate = vatIlk.1;
    uint256 spot = vatIlk.2;
    uint256 dust = vatIlk.4;
    require(vat.code.length > 0);
    var vatUrn = vat.urns{view}(ilk, urn);
    uint256 ink = vatUrn.0;
    uint256 art = vatUrn.1;
    require(live == 1);
    uint256 inkSpot = (ink * spot) as uint256;
    require(spot == 0 || inkSpot / spot == ink);
    uint256 artRateUnsafe = (art * rate) as uint256;
    require(rate == 0 || artRateUnsafe / rate == art);
    require(spot > 0 && inkSpot < artRateUnsafe);
    address milkFlip = ilks[ilk].flip;
    uint256 milkChop = ilks[ilk].chop;
    uint256 milkDunk = ilks[ilk].dunk;
    uint256 room = (box - litter) as uint256;
    require(room <= box);
    require(litter < box && room >= dust);
    var dunkRoom = min(milkDunk, room);
    uint256 dunkRoomWad = (dunkRoom * #WAD) as uint256;
    require(#WAD == 0 || dunkRoomWad / #WAD == dunkRoom);
    uint256 dartDenomRate = dunkRoomWad / rate;
    uint256 dartCandidate = dartDenomRate / milkChop;
    var dart = min(art, dartCandidate);
    uint256 inkDart = (ink * dart) as uint256;
    require(dart == 0 || inkDart / dart == ink);
    uint256 dinkCandidate = inkDart / art;
    var dink = min(ink, dinkCandidate);
    require(dart > 0 && dink > 0);
    require(dart <= #int256Limit && dink <= #int256Limit);
    require(vat.code.length > 0);
    var _grabRet = vat.grab(ilk, urn, address(this), vow, -int256(dink), -int256(dart));
    uint256 dartRate = (dart * rate) as uint256;
    require(rate == 0 || dartRate / rate == dart);
    require(vow.code.length > 0);
    var _fessRet = vow.fess(dartRate);
    uint256 tabBase = (dartRate * milkChop) as uint256;
    require(milkChop == 0 || tabBase / milkChop == dartRate);
    uint256 tab = tabBase / #WAD;
    uint256 litterNew = (litter + tab) as uint256;
    require(litterNew >= litter);
    litter = litterNew;
    require(milkFlip.code.length > 0);
    var id = milkFlip.kick(urn, vow, tab, dink, 0);
    return id;
  }

  function box() external returns (uint256) {
    return box;
  }

  function cage() external {
    require(wards[msg.sender] == 1);
    live = 0;
  }

  function claw(uint256 rad) external {
    require(wards[msg.sender] == 1);
    var litterNew = sub(litter, rad);
    litter = litterNew;
  }

  function deny(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 0;
  }

  function file(bytes32 what, address data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x766f770000000000000000000000000000000000000000000000000000000000)) {
      vow = data;
    } else {
      require(false);
    }
  }

  function file(bytes32 ilk, bytes32 what, address flip) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x666c697000000000000000000000000000000000000000000000000000000000)) {
      require(vat.code.length > 0);
      var _nopeRet = vat.nope(ilks[ilk].flip);
      ilks[ilk].flip = flip;
      require(vat.code.length > 0);
      var _hopeRet = vat.hope(flip);
    } else {
      require(false);
    }
  }

  function file(bytes32 ilk, bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x63686f7000000000000000000000000000000000000000000000000000000000)) {
      ilks[ilk].chop = data;
    } else if (what == bytes32(0x64756e6b00000000000000000000000000000000000000000000000000000000)) {
      ilks[ilk].dunk = data;
    } else {
      require(false);
    }
  }

  function file(bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x626f780000000000000000000000000000000000000000000000000000000000)) {
      box = data;
    } else {
      require(false);
    }
  }

  function ilks(bytes32 arg0) external returns (address, uint256, uint256) {
    return (ilks[arg0].flip, ilks[arg0].chop, ilks[arg0].dunk);
  }

  function litter() external returns (uint256) {
    return litter;
  }

  function live() external returns (uint256) {
    return live;
  }

  function rely(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 1;
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
}

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Cat.contract := by rfl

end Benchmarks.Dss.Cat.Syntax
