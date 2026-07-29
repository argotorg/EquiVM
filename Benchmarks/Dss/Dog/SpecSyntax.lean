import Benchmarks.Dss.Dog.Spec
import Solm.Notation

/-!
# Dog spec in the Solidity-faithful Solm frontend

The whole `dog.sol` spec written with `solidity%` and proven definitionally equal to the AST
spec in `Spec.lean`, quantified over the immutable `vat` address.  Calls through the immutable
`vat` (`vatExpr v`, a cast literal) cannot head a surface call, so those sites splice the
guarded require/externalCall statement pair and reference the returned tuple binders via `${…}`
escapes.  Transition order matches `(contract v).transitions` (selector order).
-/

open Solm Solm.Notation
open Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog.Syntax

def contractSyntax (v : DogImmutables) : ContractDecl := solidity% contract Dog {
  mapping(address => uint256) wards;
  mapping(bytes32 => Ilk) ilks;
  address vow;
  uint256 live;
  uint256 Hole;
  uint256 Dirt;

  struct Ilk {
    address clip;
    uint256 chop;
    uint256 hole;
    uint256 dirt;
  }

  constructor(address vat_) {
    address imm_vat = vat_;
    live = 1;
    wards[msg.sender] = 1;
  }

  function min(uint256 x, uint256 y) internal returns (uint256) {
    if (x <= y) {
      return x;
    } else {
      return y;
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

  function Dirt() external returns (uint256) {
    return Dirt;
  }

  function Hole() external returns (uint256) {
    return Hole;
  }

  function bark(bytes32 ilk, address urn, address kpr) external returns (uint256) {
    require(live == 1);
    ${[Stmt.require (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)),
       Stmt.externalCall (vatExpr v) "urns" (.intLit 0)
         [.var "ilk", .var "urn"] "vatUrn" (perm := false)]}
    uint256 ink = ${Expr.var "vatUrn"}.0;
    uint256 art = ${Expr.var "vatUrn"}.1;
    address milkClip = ilks[ilk].clip;
    uint256 milkChop = ilks[ilk].chop;
    uint256 milkHole = ilks[ilk].hole;
    uint256 milkDirt = ilks[ilk].dirt;
    ${[Stmt.require (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)),
       Stmt.externalCall (vatExpr v) "ilks" (.intLit 0)
         [.var "ilk"] "vatIlk" (perm := false)]}
    uint256 rate = ${Expr.var "vatIlk"}.1;
    uint256 spot = ${Expr.var "vatIlk"}.2;
    uint256 dust = ${Expr.var "vatIlk"}.4;
    uint256 inkSpot = (ink * spot) as uint256;
    require(spot == 0 || inkSpot / spot == ink);
    uint256 artRateUnsafe = (art * rate) as uint256;
    require(rate == 0 || artRateUnsafe / rate == art);
    require(spot > 0 && inkSpot < artRateUnsafe);
    require(Hole > Dirt && milkHole > milkDirt);
    uint256 globalRoom = (Hole - Dirt) as uint256;
    require(globalRoom <= Hole);
    uint256 ilkRoom = (milkHole - milkDirt) as uint256;
    require(ilkRoom <= milkHole);
    var room = min(globalRoom, ilkRoom);
    uint256 roomWad = (room * #WAD) as uint256;
    require(#WAD == 0 || roomWad / #WAD == room);
    uint256 dartByRate = roomWad / rate;
    uint256 dartCandidate = dartByRate / milkChop;
    var dart = min(art, dartCandidate);
    if (art > dart) {
      uint256 leftoverArt = (art - dart) as uint256;
      require(leftoverArt <= art);
      uint256 leftoverDue = (leftoverArt * rate) as uint256;
      require(rate == 0 || leftoverDue / rate == leftoverArt);
      if (leftoverDue < dust) {
        dart = art;
      } else {
        uint256 partialDue = (dart * rate) as uint256;
        require(rate == 0 || partialDue / rate == dart);
        require(partialDue >= dust);
      }
    }
    uint256 inkDart = (ink * dart) as uint256;
    require(dart == 0 || inkDart / dart == ink);
    uint256 dink = inkDart / art;
    require(dink > 0);
    require(dart <= #int256Limit && dink <= #int256Limit);
    ${[Stmt.require (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)),
       Stmt.externalCall (vatExpr v) "grab" (.intLit 0)
         [.var "ilk", .var "urn", .var "milkClip", vowAddr,
           .unary .neg (asInt256 (.var "dink")),
           .unary .neg (asInt256 (.var "dart"))] "_grabRet"]}
    uint256 due = (dart * rate) as uint256;
    require(rate == 0 || due / rate == dart);
    require(vow.code.length > 0);
    var _fessRet = vow.fess(due);
    uint256 tabBase = (due * milkChop) as uint256;
    require(milkChop == 0 || tabBase / milkChop == due);
    uint256 tab = tabBase / #WAD;
    uint256 DirtNew = (Dirt + tab) as uint256;
    require(DirtNew >= Dirt);
    Dirt = DirtNew;
    uint256 ilkDirtNew = (milkDirt + tab) as uint256;
    require(ilkDirtNew >= milkDirt);
    ilks[ilk].dirt = ilkDirtNew;
    require(milkClip.code.length > 0);
    var id = milkClip.kick(tab, dink, urn, kpr);
    return id;
  }

  function cage() external {
    require(wards[msg.sender] == 1);
    live = 0;
  }

  function chop(bytes32 ilk) external returns (uint256) {
    return ilks[ilk].chop;
  }

  function deny(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 0;
  }

  function digs(bytes32 ilk, uint256 rad) external {
    require(wards[msg.sender] == 1);
    var DirtNew = sub(Dirt, rad);
    Dirt = DirtNew;
    var ilkDirtNew = sub(ilks[ilk].dirt, rad);
    ilks[ilk].dirt = ilkDirtNew;
  }

  function file(bytes32 ilk, bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x63686f7000000000000000000000000000000000000000000000000000000000)) {
      require(data >= #WAD);
      ilks[ilk].chop = data;
    } else if (what == bytes32(0x686f6c6500000000000000000000000000000000000000000000000000000000)) {
      ilks[ilk].hole = data;
    } else {
      require(false);
    }
  }

  function file(bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x486f6c6500000000000000000000000000000000000000000000000000000000)) {
      Hole = data;
    } else {
      require(false);
    }
  }

  function file(bytes32 what, address data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x766f770000000000000000000000000000000000000000000000000000000000)) {
      vow = data;
    } else {
      require(false);
    }
  }

  function file(bytes32 ilk, bytes32 what, address clip) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x636c697000000000000000000000000000000000000000000000000000000000)) {
      require(clip.code.length > 0);
      var clipIlk = clip.ilk{view}();
      require(ilk == clipIlk);
      ilks[ilk].clip = clip;
    } else {
      require(false);
    }
  }

  function ilks(bytes32 arg0) external returns (address, uint256, uint256, uint256) {
    return (ilks[arg0].clip, ilks[arg0].chop, ilks[arg0].hole, ilks[arg0].dirt);
  }

  function live() external returns (uint256) {
    return live;
  }

  function rely(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 1;
  }

  function vat() external returns (address) {
    return ${vatExpr v};
  }

  function vow() external returns (address) {
    return vow;
  }

  function wards(address arg0) external returns (uint256) {
    return wards[arg0];
  }
}

/-- Definitional equality with the AST spec.  A bare `rfl` diverges here: `bark` mentions the
immutable `vatExpr v` six times, and the elaborator's defeq cache is disabled on terms with free
variables, so the lazy pairwise comparison blows up.  `simp only` first rewrites both sides to the
same cons-normal form (no defeq search); the closing `rfl` then only crosses closed leaves. -/
theorem contractSyntax_eq (v : DogImmutables) :
    contractSyntax v = Benchmarks.Dss.Dog.contract v := by
  simp only [contractSyntax, Benchmarks.Dss.Dog.contract, Benchmarks.Dss.Dog.transitions,
    Benchmarks.Dss.Dog.barkTransition, Benchmarks.Dss.Dog.barkBodyRest,
    Benchmarks.Dss.Dog.vatTransition, Benchmarks.Dss.Dog.nonpayable,
    Benchmarks.Dss.Dog.checkedExternalCallStmts, Benchmarks.Dss.Dog.checkedMulUintInto,
    Benchmarks.Dss.Dog.checkedSubUintInto, Benchmarks.Dss.Dog.checkedAddUintInto,
    Benchmarks.Dss.Dog.liveRef, Benchmarks.Dss.Dog.vowAddr, Benchmarks.Dss.Dog.vowRef,
    Benchmarks.Dss.Dog.HoleRef, Benchmarks.Dss.Dog.DirtRef, Benchmarks.Dss.Dog.ilksF,
    Benchmarks.Dss.Dog.varRef, Benchmarks.Dss.Dog.uint256, Benchmarks.Dss.Dog.addr,
    Benchmarks.Dss.Dog.uint256Int, Benchmarks.Dss.Dog.u256, Benchmarks.Dss.Dog.mul256,
    Benchmarks.Dss.Dog.sub256, Benchmarks.Dss.Dog.add256,
    List.cons_append, List.nil_append]
  rfl

end Benchmarks.Dss.Dog.Syntax
