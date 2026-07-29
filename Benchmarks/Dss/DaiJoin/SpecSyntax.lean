import Benchmarks.Dss.DaiJoin.Spec
import Solm.Notation

/-!
# DaiJoin spec in the Solidity-faithful Solm frontend

The whole DaiJoin benchmark spec, written with `solidity%` and proven definitionally equal to the
AST spec in `Benchmarks/Dss/DaiJoin/Spec.lean`.  The `extCodeSize` guards on storage receivers
(`vat`, `dai`) use the `${…}` expression escape (surface `x.code.length` only covers locals).
Transition order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.DaiJoin.Syntax

def contractSyntax : ContractDecl := solidity% contract DaiJoin {
  mapping(address => uint256) wards;
  address vat;
  address dai;
  uint256 live;

  constructor(address vat_, address dai_) {
    wards[msg.sender] = 1;
    live = 1;
    vat = vat_;
    dai = dai_;
  }

  function mul(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x * y) as uint256;
    require(y == 0 || z / y == x);
    return z;
  }

  function cage() external {
    require(wards[msg.sender] == 1);
    live = 0;
  }

  function dai() external returns (address) {
    return dai;
  }

  function deny(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 0;
  }

  function exit(address usr, uint256 wad) external {
    require(live == 1);
    uint256 rad = mul(#ONE, wad);
    require(${Expr.extCodeSize (Expr.storage vatRef)} > 0);
    var moveRet = vat.move(msg.sender, this, rad);
    require(${Expr.extCodeSize (Expr.storage daiRef)} > 0);
    var mintRet = dai.mint(usr, wad);
  }

  function join(address usr, uint256 wad) external {
    uint256 rad = mul(#ONE, wad);
    require(${Expr.extCodeSize (Expr.storage vatRef)} > 0);
    var moveRet = vat.move(this, usr, rad);
    require(${Expr.extCodeSize (Expr.storage daiRef)} > 0);
    var burnRet = dai.burn(msg.sender, wad);
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

  function wards(address arg0) external returns (uint256) {
    return wards[arg0];
  }
}

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.DaiJoin.contract := by rfl

end Benchmarks.Dss.DaiJoin.Syntax
