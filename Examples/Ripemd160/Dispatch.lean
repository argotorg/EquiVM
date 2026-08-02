import Examples.Ripemd160.Common

/-!
# Ripemd160Deployed fallback dispatch

The contract has no named transitions or receive function, so all calldata selects its fallback.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Ripemd160

@[simp] theorem selectorDispatch_none (calldata : ByteArray) :
    selectorDispatchMsg contract calldata = none := by
  rfl

@[simp] theorem receiveDispatch_none (calldata : ByteArray) :
    receiveDispatchMsg contract calldata = none := by
  simp [receiveDispatchMsg, contract, Syntax.contractSyntax]

@[simp] theorem dispatch_fallback (calldata : ByteArray) :
    dispatchMsg contract calldata = some fallbackTransition := by
  rw [dispatchMsg, selectorDispatch_none, receiveDispatch_none]
  change contract.fallback = some fallbackTransition
  rfl

@[simp] theorem fallback_callargs (calldata : ByteArray) :
    fallbackCallargs calldata fallbackTransition.params =
      some ((∅ : Store).insert "data" (.bytes calldata)) := by
  rfl

@[simp] theorem fallback_returnConvention :
    fallbackReturnConvention fallbackTransition = some .rawBytes := by
  rfl

end Ripemd160
