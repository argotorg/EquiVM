import Examples.Reuse.Spec
import Solm.Notation

/-!
# Reuse spec in the Solidity-faithful Solm frontend

The `C` contract from `Examples/Reuse/Spec.lean` written with `solidity%` and proven
definitionally equal to the AST spec.

* The spec's constructor body is empty (no non-payable guard), so the surface constructor is
  marked `payable` to suppress the auto-inserted guard.
* `g` calls the public `f` internally, written as the bound internal call `var r = f(v);`.
-/

open Solm Solm.Notation

namespace Reuse.Syntax

def contractSyntax : ContractDecl := solidity% contract C {
  uint256 s;

  constructor() payable { }

  function f(uint256 v) external returns (uint256) {
    return (v * 2 + 1) as uint256;
  }

  function g(uint256 v) external {
    var r = f(v);
    s = r;
  }
}

theorem contractSyntax_eq : contractSyntax = Reuse.cContract := by rfl

end Reuse.Syntax
