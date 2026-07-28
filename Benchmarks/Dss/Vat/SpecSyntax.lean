import Benchmarks.Dss.Vat.Spec
import Solm.Notation

/-!
# Vat spec in the Solidity-faithful Solm frontend

The whole `vat.sol` spec written with `solidity%` and proven definitionally equal to the AST
spec in `Spec.lean`.  Maker's checked-arithmetic helper statement lists are inlined: unsigned
add/sub/mul are the `as uint256` range checks, the signed variants wrap with
`% #(Int.ofNat EVM.wordModulus)` and check the sign conditions, and signed mul is the
`as int256` range check plus the `#maxInt256` bound.  `wish` is the inline
`x == msg.sender || can[x][msg.sender] == 1`.  `file` keys are big-endian `bytes32` ASCII
literals.  Transition order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation Benchmarks.Dss.Vat

namespace Benchmarks.Dss.Vat.Syntax

def contractSyntax : ContractDecl := solidity% contract Vat {
  struct Ilk {
    uint256 Art;
    uint256 rate;
    uint256 spot;
    uint256 line;
    uint256 dust;
  }

  struct Urn {
    uint256 ink;
    uint256 art;
  }

  mapping(address => uint256) wards;
  mapping(address => mapping(address => uint256)) can;
  mapping(bytes32 => Ilk) ilks;
  mapping(bytes32 => mapping(address => Urn)) urns;
  mapping(bytes32 => mapping(address => uint256)) gem;
  mapping(address => uint256) dai;
  mapping(address => uint256) sin;
  uint256 debt;
  uint256 vice;
  uint256 Line;
  uint256 live;

  constructor() {
    wards[msg.sender] = 1;
    live = 1;
  }

  function Line() external returns (uint256) {
    return Line;
  }

  function cage() external {
    require(wards[msg.sender] == 1);
    live = 0;
  }

  function can(address arg0, address arg1) external returns (uint256) {
    return can[arg0][arg1];
  }

  function dai(address arg0) external returns (uint256) {
    return dai[arg0];
  }

  function debt() external returns (uint256) {
    return debt;
  }

  function deny(address usr) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    wards[usr] = 0;
  }

  function file(bytes32 ilk, bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    if (what == bytes32(0x73706f7400000000000000000000000000000000000000000000000000000000)) {
      ilks[ilk].spot = data;
    } else if (what == bytes32(0x6c696e6500000000000000000000000000000000000000000000000000000000)) {
      ilks[ilk].line = data;
    } else if (what == bytes32(0x6475737400000000000000000000000000000000000000000000000000000000)) {
      ilks[ilk].dust = data;
    } else {
      require(false);
    }
  }

  function file(bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    if (what == bytes32(0x4c696e6500000000000000000000000000000000000000000000000000000000)) {
      Line = data;
    } else {
      require(false);
    }
  }

  function flux(bytes32 ilk, address src, address dst, uint256 wad) external {
    require(src == msg.sender || can[src][msg.sender] == 1);
    uint256 srcGemNew = (gem[ilk][src] - wad) as uint256;
    require(srcGemNew <= gem[ilk][src]);
    gem[ilk][src] = srcGemNew;
    uint256 dstGemNew = (gem[ilk][dst] + wad) as uint256;
    require(dstGemNew >= gem[ilk][dst]);
    gem[ilk][dst] = dstGemNew;
  }

  function fold(bytes32 i, address u, int256 rate) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    uint256 rateNew = (ilks[i].rate + rate) % #(Int.ofNat EVM.wordModulus);
    require(rate >= 0 || rateNew <= ilks[i].rate);
    require(rate <= 0 || rateNew >= ilks[i].rate);
    ilks[i].rate = rateNew;
    int256 rad = (ilks[i].Art * rate) as int256;
    require(ilks[i].Art <= #maxInt256);
    require(rate == 0 || rad / rate == ilks[i].Art);
    uint256 daiNew = (dai[u] + rad) % #(Int.ofNat EVM.wordModulus);
    require(rad >= 0 || daiNew <= dai[u]);
    require(rad <= 0 || daiNew >= dai[u]);
    dai[u] = daiNew;
    uint256 debtNew = (debt + rad) % #(Int.ofNat EVM.wordModulus);
    require(rad >= 0 || debtNew <= debt);
    require(rad <= 0 || debtNew >= debt);
    debt = debtNew;
  }

  function fork(bytes32 ilk, address src, address dst, int256 dink, int256 dart) external {
    uint256 srcInkNew = (urns[ilk][src].ink - dink) % #(Int.ofNat EVM.wordModulus);
    require(dink <= 0 || srcInkNew <= urns[ilk][src].ink);
    require(dink >= 0 || srcInkNew >= urns[ilk][src].ink);
    urns[ilk][src].ink = srcInkNew;
    uint256 srcArtNew = (urns[ilk][src].art - dart) % #(Int.ofNat EVM.wordModulus);
    require(dart <= 0 || srcArtNew <= urns[ilk][src].art);
    require(dart >= 0 || srcArtNew >= urns[ilk][src].art);
    urns[ilk][src].art = srcArtNew;
    uint256 dstInkNew = (urns[ilk][dst].ink + dink) % #(Int.ofNat EVM.wordModulus);
    require(dink >= 0 || dstInkNew <= urns[ilk][dst].ink);
    require(dink <= 0 || dstInkNew >= urns[ilk][dst].ink);
    urns[ilk][dst].ink = dstInkNew;
    uint256 dstArtNew = (urns[ilk][dst].art + dart) % #(Int.ofNat EVM.wordModulus);
    require(dart >= 0 || dstArtNew <= urns[ilk][dst].art);
    require(dart <= 0 || dstArtNew >= urns[ilk][dst].art);
    urns[ilk][dst].art = dstArtNew;
    uint256 srcArtFinal = urns[ilk][src].art;
    uint256 dstArtFinal = urns[ilk][dst].art;
    uint256 srcInkFinal = urns[ilk][src].ink;
    uint256 dstInkFinal = urns[ilk][dst].ink;
    uint256 utab = (srcArtFinal * ilks[ilk].rate) as uint256;
    require(ilks[ilk].rate == 0 || utab / ilks[ilk].rate == srcArtFinal);
    uint256 vtab = (dstArtFinal * ilks[ilk].rate) as uint256;
    require(ilks[ilk].rate == 0 || vtab / ilks[ilk].rate == dstArtFinal);
    uint256 srcInkSpot = (srcInkFinal * ilks[ilk].spot) as uint256;
    require(ilks[ilk].spot == 0 || srcInkSpot / ilks[ilk].spot == srcInkFinal);
    uint256 dstInkSpot = (dstInkFinal * ilks[ilk].spot) as uint256;
    require(ilks[ilk].spot == 0 || dstInkSpot / ilks[ilk].spot == dstInkFinal);
    require((src == msg.sender || can[src][msg.sender] == 1) &&
      (dst == msg.sender || can[dst][msg.sender] == 1));
    require(utab <= srcInkSpot);
    require(vtab <= dstInkSpot);
    require(utab >= ilks[ilk].dust || srcArtFinal == 0);
    require(vtab >= ilks[ilk].dust || dstArtFinal == 0);
  }

  function frob(bytes32 i, address u, address v, address w, int256 dink, int256 dart) external {
    require(live == 1);
    uint256 urnInk = urns[i][u].ink;
    uint256 urnArt = urns[i][u].art;
    uint256 ilkArt = ilks[i].Art;
    uint256 ilkRate = ilks[i].rate;
    uint256 ilkSpot = ilks[i].spot;
    uint256 ilkLine = ilks[i].line;
    uint256 ilkDust = ilks[i].dust;
    require(ilkRate != 0);
    uint256 urnInkNew = (urnInk + dink) % #(Int.ofNat EVM.wordModulus);
    require(dink >= 0 || urnInkNew <= urnInk);
    require(dink <= 0 || urnInkNew >= urnInk);
    uint256 urnArtNew = (urnArt + dart) % #(Int.ofNat EVM.wordModulus);
    require(dart >= 0 || urnArtNew <= urnArt);
    require(dart <= 0 || urnArtNew >= urnArt);
    uint256 ilkArtNew = (ilkArt + dart) % #(Int.ofNat EVM.wordModulus);
    require(dart >= 0 || ilkArtNew <= ilkArt);
    require(dart <= 0 || ilkArtNew >= ilkArt);
    int256 dtab = (ilkRate * dart) as int256;
    require(ilkRate <= #maxInt256);
    require(dart == 0 || dtab / dart == ilkRate);
    uint256 tab = (ilkRate * urnArtNew) as uint256;
    require(urnArtNew == 0 || tab / urnArtNew == ilkRate);
    uint256 debtNew = (debt + dtab) % #(Int.ofNat EVM.wordModulus);
    require(dtab >= 0 || debtNew <= debt);
    require(dtab <= 0 || debtNew >= debt);
    debt = debtNew;
    uint256 ceilingDebt = (ilkArtNew * ilkRate) as uint256;
    require(ilkRate == 0 || ceilingDebt / ilkRate == ilkArtNew);
    uint256 inkSpot = (urnInkNew * ilkSpot) as uint256;
    require(ilkSpot == 0 || inkSpot / ilkSpot == urnInkNew);
    require(dart <= 0 || (ceilingDebt <= ilkLine && debtNew <= Line));
    require((dart <= 0 && dink >= 0) || tab <= inkSpot);
    require((dart <= 0 && dink >= 0) || (u == msg.sender || can[u][msg.sender] == 1));
    require(dink <= 0 || (v == msg.sender || can[v][msg.sender] == 1));
    require(dart >= 0 || (w == msg.sender || can[w][msg.sender] == 1));
    require(urnArtNew == 0 || tab >= ilkDust);
    uint256 gemNew = (gem[i][v] - dink) % #(Int.ofNat EVM.wordModulus);
    require(dink <= 0 || gemNew <= gem[i][v]);
    require(dink >= 0 || gemNew >= gem[i][v]);
    gem[i][v] = gemNew;
    uint256 daiNew = (dai[w] + dtab) % #(Int.ofNat EVM.wordModulus);
    require(dtab >= 0 || daiNew <= dai[w]);
    require(dtab <= 0 || daiNew >= dai[w]);
    dai[w] = daiNew;
    urns[i][u].ink = urnInkNew;
    urns[i][u].art = urnArtNew;
    ilks[i].Art = ilkArtNew;
    ilks[i].rate = ilkRate;
    ilks[i].spot = ilkSpot;
    ilks[i].line = ilkLine;
    ilks[i].dust = ilkDust;
  }

  function gem(bytes32 arg0, address arg1) external returns (uint256) {
    return gem[arg0][arg1];
  }

  function grab(bytes32 i, address u, address v, address w, int256 dink, int256 dart) external {
    require(wards[msg.sender] == 1);
    uint256 urnInkNew = (urns[i][u].ink + dink) % #(Int.ofNat EVM.wordModulus);
    require(dink >= 0 || urnInkNew <= urns[i][u].ink);
    require(dink <= 0 || urnInkNew >= urns[i][u].ink);
    urns[i][u].ink = urnInkNew;
    uint256 urnArtNew = (urns[i][u].art + dart) % #(Int.ofNat EVM.wordModulus);
    require(dart >= 0 || urnArtNew <= urns[i][u].art);
    require(dart <= 0 || urnArtNew >= urns[i][u].art);
    urns[i][u].art = urnArtNew;
    uint256 ilkArtNew = (ilks[i].Art + dart) % #(Int.ofNat EVM.wordModulus);
    require(dart >= 0 || ilkArtNew <= ilks[i].Art);
    require(dart <= 0 || ilkArtNew >= ilks[i].Art);
    ilks[i].Art = ilkArtNew;
    int256 dtab = (ilks[i].rate * dart) as int256;
    require(ilks[i].rate <= #maxInt256);
    require(dart == 0 || dtab / dart == ilks[i].rate);
    uint256 gemNew = (gem[i][v] - dink) % #(Int.ofNat EVM.wordModulus);
    require(dink <= 0 || gemNew <= gem[i][v]);
    require(dink >= 0 || gemNew >= gem[i][v]);
    gem[i][v] = gemNew;
    uint256 sinNew = (sin[w] - dtab) % #(Int.ofNat EVM.wordModulus);
    require(dtab <= 0 || sinNew <= sin[w]);
    require(dtab >= 0 || sinNew >= sin[w]);
    sin[w] = sinNew;
    uint256 viceNew = (vice - dtab) % #(Int.ofNat EVM.wordModulus);
    require(dtab <= 0 || viceNew <= vice);
    require(dtab >= 0 || viceNew >= vice);
    vice = viceNew;
  }

  function heal(uint256 rad) external {
    uint256 sinNew = (sin[msg.sender] - rad) as uint256;
    require(sinNew <= sin[msg.sender]);
    sin[msg.sender] = sinNew;
    uint256 daiNew = (dai[msg.sender] - rad) as uint256;
    require(daiNew <= dai[msg.sender]);
    dai[msg.sender] = daiNew;
    uint256 viceNew = (vice - rad) as uint256;
    require(viceNew <= vice);
    vice = viceNew;
    uint256 debtNew = (debt - rad) as uint256;
    require(debtNew <= debt);
    debt = debtNew;
  }

  function hope(address usr) external {
    can[msg.sender][usr] = 1;
  }

  function ilks(bytes32 arg0) external returns (uint256, uint256, uint256, uint256, uint256) {
    return (ilks[arg0].Art, ilks[arg0].rate, ilks[arg0].spot, ilks[arg0].line, ilks[arg0].dust);
  }

  function init(bytes32 ilk) external {
    require(wards[msg.sender] == 1);
    require(ilks[ilk].rate == 0);
    ilks[ilk].rate = #ray;
  }

  function live() external returns (uint256) {
    return live;
  }

  function move(address src, address dst, uint256 rad) external {
    require(src == msg.sender || can[src][msg.sender] == 1);
    uint256 srcDaiNew = (dai[src] - rad) as uint256;
    require(srcDaiNew <= dai[src]);
    dai[src] = srcDaiNew;
    uint256 dstDaiNew = (dai[dst] + rad) as uint256;
    require(dstDaiNew >= dai[dst]);
    dai[dst] = dstDaiNew;
  }

  function nope(address usr) external {
    can[msg.sender][usr] = 0;
  }

  function rely(address usr) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    wards[usr] = 1;
  }

  function sin(address arg0) external returns (uint256) {
    return sin[arg0];
  }

  function slip(bytes32 ilk, address usr, int256 wad) external {
    require(wards[msg.sender] == 1);
    uint256 gemNew = (gem[ilk][usr] + wad) % #(Int.ofNat EVM.wordModulus);
    require(wad >= 0 || gemNew <= gem[ilk][usr]);
    require(wad <= 0 || gemNew >= gem[ilk][usr]);
    gem[ilk][usr] = gemNew;
  }

  function suck(address u, address v, uint256 rad) external {
    require(wards[msg.sender] == 1);
    uint256 sinNew = (sin[u] + rad) as uint256;
    require(sinNew >= sin[u]);
    sin[u] = sinNew;
    uint256 daiNew = (dai[v] + rad) as uint256;
    require(daiNew >= dai[v]);
    dai[v] = daiNew;
    uint256 viceNew = (vice + rad) as uint256;
    require(viceNew >= vice);
    vice = viceNew;
    uint256 debtNew = (debt + rad) as uint256;
    require(debtNew >= debt);
    debt = debtNew;
  }

  function urns(bytes32 arg0, address arg1) external returns (uint256, uint256) {
    return (urns[arg0][arg1].ink, urns[arg0][arg1].art);
  }

  function vice() external returns (uint256) {
    return vice;
  }

  function wards(address arg0) external returns (uint256) {
    return wards[arg0];
  }
}

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Vat.contract := by rfl

end Benchmarks.Dss.Vat.Syntax
