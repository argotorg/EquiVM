import Benchmarks.Dss.Spot.Spec
import Solm.Notation

/-!
# Spotter spec in the Solidity-faithful Solm frontend

The whole Spotter benchmark spec, written with `solidity%` and proven definitionally equal to the
AST spec in `Benchmarks/Dss/Spot/Spec.lean`.

Escapes: the `"pip"`/`"par"`/`"mat"`/`"spot"` `bytes32` parameter literals are the spec's
`fixedBytesLit` defs; `poke`'s oracle call has an indexed-path receiver (`ilks[ilk].pip`), which
the surface method-call syntax cannot express, so that require+call pair is spliced with the
spec's own `checkedExternalCallStmts` (its `peekRet` binder is then referenced via `${…}`).
Transition order matches `contract.transitions`.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.Spot.Syntax

def contractSyntax : ContractDecl := solidity% contract Spotter {
  struct Ilk {
    address pip;
    uint256 mat;
  }

  mapping(address => uint256) wards;
  mapping(bytes32 => Ilk) ilks;
  address vat;
  uint256 par;
  uint256 live;

  constructor(address vat_) {
    wards[msg.sender] = 1;
    vat = vat_;
    par = #one;
    live = 1;
  }

  function mul(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x * y) as uint256;
    require(y == 0 || z / y == x);
    return z;
  }

  function rdiv(uint256 x, uint256 y) internal returns (uint256) {
    var z = mul(x, #one);
    z = z / y;
    return z;
  }

  function cage() external {
    require(wards[msg.sender] == 1);
    live = 0;
  }

  function deny(address guy) external {
    require(wards[msg.sender] == 1);
    wards[guy] = 0;
  }

  function file(bytes32 ilk, bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    if (what == ${matParamLit}) {
      ilks[ilk].mat = data;
    } else {
      require(false);
    }
  }

  function file(bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    if (what == ${parParamLit}) {
      par = data;
    } else {
      require(false);
    }
  }

  function file(bytes32 ilk, bytes32 what, address pip_) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    if (what == ${pipParamLit}) {
      ilks[ilk].pip = pip_;
    } else {
      require(false);
    }
  }

  function ilks(bytes32 arg0) external returns (address, uint256) {
    return (ilks[arg0].pip, ilks[arg0].mat);
  }

  function live() external returns (uint256) {
    return live;
  }

  function par() external returns (uint256) {
    return par;
  }

  function poke(bytes32 ilk) external {
    ${checkedExternalCallStmts (.storage (ilksF (.var "ilk") "pip")) "peek" (.intLit 0) []
      "peekRet"}
    bytes32 val = ${Expr.tupleGet (Expr.var "peekRet") 0};
    bool has = ${Expr.tupleGet (Expr.var "peekRet") 1};
    uint256 spot = 0;
    if (has) {
      uint256 valScaled = (uint256(val) * #billion) as uint256;
      require(#billion == 0 || valScaled / #billion == uint256(val));
      var spot1 = rdiv(valScaled, par);
      var spot2 = rdiv(spot1, ilks[ilk].mat);
      spot = spot2;
    }
    require(${Expr.extCodeSize (Expr.storage vatRef)} > 0);
    var _fileRet = vat.file(ilk, ${spotParamLit}, spot);
  }

  function rely(address guy) external {
    require(wards[msg.sender] == 1);
    wards[guy] = 1;
  }

  function vat() external returns (address) {
    return vat;
  }

  function wards(address arg0) external returns (uint256) {
    return wards[arg0];
  }
}

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Spot.contract := by rfl

end Benchmarks.Dss.Spot.Syntax
