import Examples.OpenZeppelinBench.Pausable.Spec
import Solm.Notation

/-!
# Pausable spec in the Solidity-faithful Solm frontend

The `PausableBench` spec written with `solidity%`, proven definitionally equal to the AST spec in
`Examples/OpenZeppelinBench/Pausable/Spec.lean`.

The AST constructor has no callvalue guard, so the surface constructor is marked `payable`.
Transition order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation

namespace OpenZeppelinBench.Pausable.Syntax

def contractSyntax : ContractDecl := solidity% contract PausableBench {
  bool _paused;

  constructor() payable {
    _paused = false;
  }

  function guardedWhenNotPaused() external returns (bool) {
    require(!_paused);
    return true;
  }

  function guardedWhenPaused() external returns (bool) {
    require(_paused);
    return true;
  }

  function pause() external {
    require(!_paused);
    _paused = true;
  }

  function paused() external returns (bool) {
    return _paused;
  }

  function unpause() external {
    require(_paused);
    _paused = false;
  }
}

theorem contractSyntax_eq : contractSyntax = OpenZeppelinBench.Pausable.contract := by rfl

end OpenZeppelinBench.Pausable.Syntax
