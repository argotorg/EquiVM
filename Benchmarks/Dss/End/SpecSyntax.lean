import Benchmarks.Dss.End.Spec
import Solm.Notation

/-!
# End spec in the Solidity-faithful Solm frontend

The whole `end.sol` spec written with `solidity%` and proven definitionally equal to the AST
spec in `Spec.lean`.  Checked external calls are the `require(x.code.length > 0)` +
call pairs; `{view}` marks the spec's `(perm := false)` calls; the `int256(x) >= 0` guards are
the spec's `< 2^255` / `<= 2^255` comparisons against `#int256Limit`; `file` keys are big-endian
`bytes32` ASCII literals.  Transition order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation Benchmarks.Dss.End

namespace Benchmarks.Dss.End.Syntax

def contractSyntax : ContractDecl := solidity% contract End {
  mapping(address => uint256) wards;
  address vat;
  address cat;
  address dog;
  address vow;
  address pot;
  address spot;
  address cure;
  uint256 live;
  uint256 when;
  uint256 wait;
  uint256 debt;
  mapping(bytes32 => uint256) tag;
  mapping(bytes32 => uint256) gap;
  mapping(bytes32 => uint256) Art;
  mapping(bytes32 => uint256) fix;
  mapping(address => uint256) bag;
  mapping(bytes32 => mapping(address => uint256)) out;

  constructor() {
    wards[msg.sender] = 1;
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

  function mul(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x * y) as uint256;
    require(y == 0 || z / y == x);
    return z;
  }

  function min(uint256 x, uint256 y) internal returns (uint256) {
    if (x <= y) {
      return x;
    } else {
      return y;
    }
  }

  function rmul(uint256 x, uint256 y) internal returns (uint256) {
    var m = mul(x, y);
    return m / #RAY;
  }

  function wdiv(uint256 x, uint256 y) internal returns (uint256) {
    var m = mul(x, #WAD);
    return m / y;
  }

  function wards(address arg0) external returns (uint256) {
    return wards[arg0];
  }

  function vat() external returns (address) {
    return vat;
  }

  function cat() external returns (address) {
    return cat;
  }

  function dog() external returns (address) {
    return dog;
  }

  function vow() external returns (address) {
    return vow;
  }

  function pot() external returns (address) {
    return pot;
  }

  function spot() external returns (address) {
    return spot;
  }

  function cure() external returns (address) {
    return cure;
  }

  function live() external returns (uint256) {
    return live;
  }

  function when() external returns (uint256) {
    return when;
  }

  function wait() external returns (uint256) {
    return wait;
  }

  function debt() external returns (uint256) {
    return debt;
  }

  function tag(bytes32 arg0) external returns (uint256) {
    return tag[arg0];
  }

  function gap(bytes32 arg0) external returns (uint256) {
    return gap[arg0];
  }

  function Art(bytes32 arg0) external returns (uint256) {
    return Art[arg0];
  }

  function fix(bytes32 arg0) external returns (uint256) {
    return fix[arg0];
  }

  function bag(address arg0) external returns (uint256) {
    return bag[arg0];
  }

  function out(bytes32 arg0, address arg1) external returns (uint256) {
    return out[arg0][arg1];
  }

  function rely(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 1;
  }

  function deny(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 0;
  }

  function file(bytes32 what, address data) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    if (what == bytes32(0x7661740000000000000000000000000000000000000000000000000000000000)) {
      vat = data;
    } else if (what == bytes32(0x6361740000000000000000000000000000000000000000000000000000000000)) {
      cat = data;
    } else if (what == bytes32(0x646f670000000000000000000000000000000000000000000000000000000000)) {
      dog = data;
    } else if (what == bytes32(0x766f770000000000000000000000000000000000000000000000000000000000)) {
      vow = data;
    } else if (what == bytes32(0x706f740000000000000000000000000000000000000000000000000000000000)) {
      pot = data;
    } else if (what == bytes32(0x73706f7400000000000000000000000000000000000000000000000000000000)) {
      spot = data;
    } else if (what == bytes32(0x6375726500000000000000000000000000000000000000000000000000000000)) {
      cure = data;
    } else {
      require(false);
    }
  }

  function file(bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    if (what == bytes32(0x7761697400000000000000000000000000000000000000000000000000000000)) {
      wait = data;
    } else {
      require(false);
    }
  }

  function cage() external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    live = 0;
    when = block.timestamp;
    require(vat.code.length > 0);
    var _vatCage = vat.cage();
    require(cat.code.length > 0);
    var _catCage = cat.cage();
    require(dog.code.length > 0);
    var _dogCage = dog.cage();
    require(vow.code.length > 0);
    var _vowCage = vow.cage();
    require(spot.code.length > 0);
    var _spotCage = spot.cage();
    require(pot.code.length > 0);
    var _potCage = pot.cage();
    require(cure.code.length > 0);
    var _cureCage = cure.cage();
  }

  function cage(bytes32 ilk) external {
    require(live == 0);
    require(tag[ilk] == 0);
    require(vat.code.length > 0);
    var vatIlk = vat.vatIlks(ilk);
    Art[ilk] = vatIlk.0;
    require(spot.code.length > 0);
    var spotIlk = spot.spotIlks{view}(ilk);
    address pip = spotIlk.0;
    require(spot.code.length > 0);
    var parV = spot.par{view}();
    require(pip.code.length > 0);
    var pipRead = pip.read{view}();
    var tagV = wdiv(parV, uint256(pipRead));
    tag[ilk] = tagV;
  }

  function snip(bytes32 ilk, uint256 id) external {
    require(tag[ilk] != 0);
    require(dog.code.length > 0);
    var dogIlk = dog.dogIlks(ilk);
    address clip = dogIlk.0;
    require(vat.code.length > 0);
    var vatIlk = vat.vatIlks(ilk);
    uint256 rate = vatIlk.1;
    require(clip.code.length > 0);
    var clipSale = clip.sales{view}(id);
    uint256 tab = clipSale.1;
    uint256 lot = clipSale.2;
    address usr = clipSale.3;
    require(vat.code.length > 0);
    var _suck = vat.suck(vow, vow, tab);
    require(clip.code.length > 0);
    var _yank = clip.yank(id);
    uint256 art = tab / rate;
    var ArtNew = add(Art[ilk], art);
    Art[ilk] = ArtNew;
    require(lot < #int256Limit && art < #int256Limit);
    require(vat.code.length > 0);
    var _grab = vat.grab(ilk, usr, address(this), vow, int256(lot), int256(art));
  }

  function skip(bytes32 ilk, uint256 id) external {
    require(tag[ilk] != 0);
    require(cat.code.length > 0);
    var catIlk = cat.catIlks(ilk);
    address flip = catIlk.0;
    require(vat.code.length > 0);
    var vatIlk = vat.vatIlks(ilk);
    uint256 rate = vatIlk.1;
    require(flip.code.length > 0);
    var flipBid = flip.bids{view}(id);
    uint256 bid = flipBid.0;
    uint256 lot = flipBid.1;
    address usr = flipBid.5;
    uint256 tab = flipBid.7;
    require(vat.code.length > 0);
    var _suck1 = vat.suck(vow, vow, tab);
    require(vat.code.length > 0);
    var _suck2 = vat.suck(vow, address(this), bid);
    require(vat.code.length > 0);
    var _hope = vat.hope(flip);
    require(flip.code.length > 0);
    var _yank = flip.yank(id);
    uint256 art = tab / rate;
    var ArtNew = add(Art[ilk], art);
    Art[ilk] = ArtNew;
    require(lot < #int256Limit && art < #int256Limit);
    require(vat.code.length > 0);
    var _grab = vat.grab(ilk, usr, address(this), vow, int256(lot), int256(art));
  }

  function skim(bytes32 ilk, address urn) external {
    require(tag[ilk] != 0);
    require(vat.code.length > 0);
    var vatIlk = vat.vatIlks(ilk);
    uint256 rate = vatIlk.1;
    require(vat.code.length > 0);
    var vatUrn = vat.urns(ilk, urn);
    uint256 ink = vatUrn.0;
    uint256 art = vatUrn.1;
    var owe0 = rmul(art, rate);
    var owe = rmul(owe0, tag[ilk]);
    var wad = min(ink, owe);
    var diff = sub(owe, wad);
    var gapNew = add(gap[ilk], diff);
    gap[ilk] = gapNew;
    require(wad <= #int256Limit && art <= #int256Limit);
    require(vat.code.length > 0);
    var _grab = vat.grab(ilk, urn, address(this), vow, -int256(wad), -int256(art));
  }

  function free(bytes32 ilk) external {
    require(live == 0);
    require(vat.code.length > 0);
    var vatUrn = vat.urns(ilk, msg.sender);
    uint256 ink = vatUrn.0;
    uint256 art = vatUrn.1;
    require(art == 0);
    require(ink <= #int256Limit);
    require(vat.code.length > 0);
    var _grab = vat.grab(ilk, msg.sender, msg.sender, vow, -int256(ink), 0);
  }

  function thaw() external {
    require(live == 0);
    require(debt == 0);
    require(vat.code.length > 0);
    var vatDai = vat.dai{view}(vow);
    require(vatDai == 0);
    var deadline = add(when, wait);
    require(block.timestamp >= deadline);
    require(vat.code.length > 0);
    var vatDebt = vat.debt();
    require(cure.code.length > 0);
    var cureTell = cure.tell{view}();
    var debtNew = sub(vatDebt, cureTell);
    debt = debtNew;
  }

  function flow(bytes32 ilk) external {
    require(debt != 0);
    require(fix[ilk] == 0);
    require(vat.code.length > 0);
    var vatIlk = vat.vatIlks(ilk);
    uint256 rate = vatIlk.1;
    var wad0 = rmul(Art[ilk], rate);
    var wad = rmul(wad0, tag[ilk]);
    var num0 = sub(wad, gap[ilk]);
    var num = mul(num0, #RAY);
    uint256 den = debt / #RAY;
    uint256 fixV = num / den;
    fix[ilk] = fixV;
  }

  function pack(uint256 wad) external {
    require(debt != 0);
    var amt = mul(wad, #RAY);
    require(vat.code.length > 0);
    var _move = vat.move(msg.sender, vow, amt);
    var bagNew = add(bag[msg.sender], wad);
    bag[msg.sender] = bagNew;
  }

  function cash(bytes32 ilk, uint256 wad) external {
    require(fix[ilk] != 0);
    var amt = rmul(wad, fix[ilk]);
    require(vat.code.length > 0);
    var _flux = vat.flux(ilk, address(this), msg.sender, amt);
    var outNew = add(out[ilk][msg.sender], wad);
    out[ilk][msg.sender] = outNew;
    require(outNew <= bag[msg.sender]);
  }
}

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.End.contract := by rfl

end Benchmarks.Dss.End.Syntax
