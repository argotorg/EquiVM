import Examples.StringStoreLite.Spec
import Solm.Notation

/-!
# StringStoreLite spec in the Solidity-faithful Solm frontend

The `StringStoreLite` contract from `Examples/StringStoreLite/Spec.lean` written with
`solidity%` and proven definitionally equal to the AST spec.

* The spec's constructor body is empty (no non-payable guard), so the surface constructor is
  marked `payable` to suppress the auto-inserted guard.
* `string memory copy = …;` gives the typed `letDecl` (`some ABIType.string`) of the AST;
  `copy.length` / `current.length` give the local/storage `arrayLength` reads.
-/

open Solm Solm.Notation

namespace StringStoreLite.Syntax

def contractSyntax : ContractDecl := solidity% contract StringStoreLite {
  string current;

  constructor() payable { }

  function set(string memory value) external returns (uint256) {
    string memory copy = value;
    current = copy;
    return copy.length;
  }

  function clearCurrent() external returns (uint256) {
    string memory copy = current;
    delete current;
    return copy.length;
  }

  function currentLength() external returns (uint256) {
    return current.length;
  }
}

theorem contractSyntax_eq : contractSyntax = StringStoreLite.stringStoreLiteContract := by rfl

end StringStoreLite.Syntax
