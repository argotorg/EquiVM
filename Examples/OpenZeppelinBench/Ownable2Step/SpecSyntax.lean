import Examples.OpenZeppelinBench.Ownable2Step.Spec
import Solm.Notation

/-!
# Ownable2Step spec in the Solidity-faithful Solm frontend

The `Ownable2StepBench` spec written with `solidity%`, proven definitionally equal to the AST spec
in `Examples/OpenZeppelinBench/Ownable2Step/Spec.lean`.

The AST constructor has no callvalue guard, so the surface constructor is marked `payable`.
Transition order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation

namespace OpenZeppelinBench.Ownable2Step.Syntax

def contractSyntax : ContractDecl := solidity% contract Ownable2StepBench {
  address _owner;
  address _pendingOwner;

  constructor(address initialOwner) payable {
    require(initialOwner != address(0));
    _owner = initialOwner;
  }

  function acceptOwnership() external {
    require(_pendingOwner == msg.sender);
    _pendingOwner = address(0);
    _owner = msg.sender;
  }

  function owner() external returns (address) {
    return _owner;
  }

  function pendingOwner() external returns (address) {
    return _pendingOwner;
  }

  function renounceOwnership() external {
    require(_owner == msg.sender);
    _pendingOwner = address(0);
    _owner = address(0);
  }

  function transferOwnership(address newOwner) external {
    require(_owner == msg.sender);
    _pendingOwner = newOwner;
  }
}

theorem contractSyntax_eq : contractSyntax = OpenZeppelinBench.Ownable2Step.contract := by rfl

end OpenZeppelinBench.Ownable2Step.Syntax
