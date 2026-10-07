import Examples.TinyImmutable.Spec
import Solm.Notation

/-!
# TinyImmutable spec in the Solidity-faithful Solm frontend

The immutables are declared as in Solidity and assigned in the constructor.  The `unchecked`
product in `quote` is the explicit `% 2^256` wrap, as in the AST spec.
-/

open Solm Solm.Notation
open TinyImmutable.Immutables

namespace TinyImmutable.Syntax

def contractSyntax : ContractDecl := solidity% contract TinyImmutable {
  address immutable owner;
  uint256 immutable scale;

  constructor(address _owner, uint256 _scale, bool useScale) {
    owner = _owner;
    if (useScale) {
      scale = _scale;
    }
  }

  function owner() external returns (address) {
    return owner;
  }

  function quote(uint256 amount) external returns (uint256) {
    require(msg.sender == owner);
    return (amount * scale) % #(Int.ofNat EVM.wordModulus);
  }

  function scale() external returns (uint256) {
    return scale;
  }
}

theorem contractSyntax_eq : contractSyntax = TinyImmutable.contract := by rfl

end TinyImmutable.Syntax
