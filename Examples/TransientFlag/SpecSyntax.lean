import Examples.TransientFlag.Spec
import Solm.Notation

/-!
# TransientFlag in the Solidity-faithful surface

The constructor is `payable` so its body stays empty. Both functions are non-payable,
so the callvalue guard is inserted by the notation.
-/

open Solm Solm.Notation

namespace TransientFlag.Syntax

def contractSyntax : ContractDecl := solidity% contract TransientFlag {
  uint256 transient flag;

  constructor() payable { }

  function setFlag(uint256 v) external {
    flag = v;
  }

  function getFlag() external view returns (uint256) {
    return flag;
  }
}

theorem contractSyntax_eq : contractSyntax = TransientFlag.flagContract := by rfl

end TransientFlag.Syntax
