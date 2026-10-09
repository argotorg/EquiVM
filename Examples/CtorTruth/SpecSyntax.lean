import Examples.CtorTruth.Spec
import Solm.Notation

/-!
# CtorTruth spec in the Solidity-faithful Solm frontend

The spec's constructor is payable with an empty body (no callvalue guard); `truth()` is
non-payable, so its guard is implicit.
-/

open Solm Solm.Notation

namespace CtorTruth.Syntax

def contractSyntax : ContractDecl := solidity% contract CtorTruth {
  constructor() payable { }

  function truth() external returns (bool) {
    return true;
  }
}

theorem contractSyntax_eq : contractSyntax = CtorTruth.contract := by rfl

end CtorTruth.Syntax
