import Benchmarks.Dss.GemJoin.Spec
import Solm.Notation

/-!
# GemJoin spec in the Solidity-faithful Solm frontend

The whole GemJoin benchmark spec, written with `solidity%` and proven definitionally equal to the
AST spec in `Benchmarks/Dss/GemJoin/Spec.lean`.  The `extCodeSize` guards on storage receivers
(`vat`, `gem`) use the `${…}` expression escape; the constructor's `decimals()` STATICCALL is the
`{view}` call on the local `gem_`.  Transition order matches `contract.transitions`.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.GemJoin.Syntax

def contractSyntax : ContractDecl := solidity% contract GemJoin {
  mapping(address => uint256) wards;
  address vat;
  bytes32 ilk;
  address gem;
  uint256 dec;
  uint256 live;

  constructor(address vat_, bytes32 ilk_, address gem_) {
    wards[msg.sender] = 1;
    live = 1;
    vat = vat_;
    ilk = ilk_;
    gem = gem_;
    require(gem_.code.length > 0);
    var decimalsRet = gem_.decimals{view}();
    dec = decimalsRet;
  }

  function cage() external {
    require(wards[msg.sender] == 1);
    live = 0;
  }

  function dec() external returns (uint256) {
    return dec;
  }

  function deny(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 0;
  }

  function exit(address usr, uint256 wad) external {
    require(wad <= #intLimit);
    require(${Expr.extCodeSize (Expr.storage vatRef)} > 0);
    var slipRet = vat.slip(ilk, msg.sender, -int256(wad));
    require(${Expr.extCodeSize (Expr.storage gemRef)} > 0);
    var transferOk = gem.transfer(usr, wad);
    require(transferOk);
  }

  function gem() external returns (address) {
    return gem;
  }

  function ilk() external returns (bytes32) {
    return ilk;
  }

  function join(address usr, uint256 wad) external {
    require(live == 1);
    require(wad < #intLimit);
    require(${Expr.extCodeSize (Expr.storage vatRef)} > 0);
    var slipRet = vat.slip(ilk, usr, int256(wad));
    require(${Expr.extCodeSize (Expr.storage gemRef)} > 0);
    var transferFromOk = gem.transferFrom(msg.sender, this, wad);
    require(transferFromOk);
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

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.GemJoin.contract := by rfl

end Benchmarks.Dss.GemJoin.Syntax
