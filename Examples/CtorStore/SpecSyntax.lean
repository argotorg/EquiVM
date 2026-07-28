import Examples.CtorStore.Spec
import Solm.Notation

/-!
# CtorStore spec in the Solidity-faithful Solm frontend

The payable constructor stores its `uint256` argument into the private `stored` field; there are
no runtime transitions.
-/

open Solm Solm.Notation

namespace CtorStore.Syntax

def contractSyntax : ContractDecl := solidity% contract CtorStore {
  uint256 stored;

  constructor(uint256 x) payable {
    stored = x;
  }
}

theorem contractSyntax_eq : contractSyntax = CtorStore.contract := by rfl

end CtorStore.Syntax
