import Examples.Truth.Spec
import Solm.Notation

/-!
# Truth spec in the Solidity-faithful Solm frontend

The spec's constructor has an empty body (no callvalue guard), so it is written `payable`;
`truth()` is non-payable, so its guard is implicit.
-/

open Solm Solm.Notation

namespace Truth.Syntax

def contractSyntax : ContractDecl := solidity% contract Truth {
  constructor() payable { }

  function truth() external returns (bool) {
    return true;
  }
}

theorem contractSyntax_eq : contractSyntax = truthContract := by rfl

end Truth.Syntax
