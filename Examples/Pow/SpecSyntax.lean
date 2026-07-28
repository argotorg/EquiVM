import Examples.Pow.Spec
import Solm.Notation

/-!
# Pow spec in the Solidity-faithful Solm frontend

The spec's constructor has an empty body (no callvalue guard), so it is written `payable`.
`pow2` is non-payable; the loop's local updates are `letDecl` re-binds, written as re-declarations
so the annotations (`some uint256`) match.
-/

open Solm Solm.Notation

namespace Pow.Syntax

def contractSyntax : ContractDecl := solidity% contract Pow {
  constructor() payable { }

  function pow2(uint256 n) external returns (uint256) {
    require(n < 256);
    uint256 r = 1;
    uint256 i = 0;
    while (i < n) {
      uint256 r = r * 2;
      uint256 i = i + 1;
    }
    return r;
  }
}

theorem contractSyntax_eq : contractSyntax = Pow.powContract := by rfl

end Pow.Syntax
