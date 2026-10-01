import Examples.OpenZeppelinBench.Ownable2Step.Bytecode
import Solm.Semantics

open Solm Ethereum Ethereum.EVM

namespace OpenZeppelinBench.Ownable2Step

/-!
# Ownable2StepBench selector facts

The jump-destination table is computed from the deployed runtime byte array in `Bytecode.lean`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("acceptOwnership()")[0:4] = 0x79ba5097`. -/
theorem acceptOwnershipSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr acceptOwnershipTransition))).extract 0 4 =
      ⟨#[0x79, 0xba, 0x50, 0x97]⟩ := by decide +kernel

/-- `keccak("owner()")[0:4] = 0x8da5cb5b`. -/
theorem ownerSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr ownerTransition))).extract 0 4 =
      ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩ := by decide +kernel

/-- `keccak("pendingOwner()")[0:4] = 0xe30c3978`. -/
theorem pendingOwnerSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr pendingOwnerTransition))).extract 0 4 =
      ⟨#[0xe3, 0x0c, 0x39, 0x78]⟩ := by decide +kernel

/-- `keccak("renounceOwnership()")[0:4] = 0x715018a6`. -/
theorem renounceOwnershipSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr renounceOwnershipTransition))).extract 0 4 =
      ⟨#[0x71, 0x50, 0x18, 0xa6]⟩ := by decide +kernel

/-- `keccak("transferOwnership(address)")[0:4] = 0xf2fde38b`. -/
theorem transferOwnershipSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr transferOwnershipTransition))).extract 0 4 =
      ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩ := by
  have hsig : Solm.transitionSigStr transferOwnershipTransition =
      "transferOwnership(address)" := by
    simp [Solm.transitionSigStr, ABI.printSignature, transitionSignature,
      transferOwnershipTransition, addr, ABI.abiToSigStr, ABI.elemToSigStr]
    decide +kernel
  rw [hsig]
  decide +kernel

end OpenZeppelinBench.Ownable2Step
