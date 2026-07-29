import Examples.TinyImmutable.Spec
import Solm.Notation

/-!
# TinyImmutable spec in the Solidity-faithful Solm frontend

The spec is parameterized by the immutable valuation `v : TinyImmutables`, so `contractSyntax` is
too, and the immutable reads use the `${…}` expression escape.  The `unchecked` product in `quote`
is the explicit `% 2^256` wrap, as in the AST spec.
-/

open Solm Solm.Notation
open TinyImmutable.Immutables

namespace TinyImmutable.Syntax

def contractSyntax (v : TinyImmutables) : ContractDecl := solidity% contract TinyImmutable {
  constructor(address _owner, uint256 _scale, bool useScale) {
    address imm_owner = _owner;
    if (useScale) {
      uint256 imm_scale = _scale;
    } else {
      uint256 imm_scale = 0;
    }
  }

  function owner() external returns (address) {
    return ${owner v};
  }

  function quote(uint256 amount) external returns (uint256) {
    require(msg.sender == ${owner v});
    return (amount * ${scale v}) % #(Int.ofNat EVM.wordModulus);
  }

  function scale() external returns (uint256) {
    return ${scale v};
  }
}

theorem contractSyntax_eq (v : TinyImmutables) :
    contractSyntax v = TinyImmutable.contract v := by rfl

end TinyImmutable.Syntax
