import Examples.OpenZeppelinBench.Ownable2Step.Bytecode
import Solm.Semantics

open Solm Ethereum Ethereum.EVM

namespace OpenZeppelinBench.Ownable2Step

/-!
# Ownable2StepBench trusted bytecode facts

The selector facts are trusted because `ffi.KEC` is opaque to Lean.  The jump-destination table is
computed from the deployed runtime byte array by `native_decide` in `Bytecode.lean`; this file gives
it the Phase-0 benchmark name used by the proof.
-/

/-- `keccak("acceptOwnership()")[0:4] = 0x79ba5097`. -/
axiom acceptOwnershipSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr acceptOwnershipTransition))).extract 0 4 =
      ⟨#[0x79, 0xba, 0x50, 0x97]⟩

/-- `keccak("owner()")[0:4] = 0x8da5cb5b`. -/
axiom ownerSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr ownerTransition))).extract 0 4 =
      ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩

/-- `keccak("pendingOwner()")[0:4] = 0xe30c3978`. -/
axiom pendingOwnerSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr pendingOwnerTransition))).extract 0 4 =
      ⟨#[0xe3, 0x0c, 0x39, 0x78]⟩

/-- `keccak("renounceOwnership()")[0:4] = 0x715018a6`. -/
axiom renounceOwnershipSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr renounceOwnershipTransition))).extract 0 4 =
      ⟨#[0x71, 0x50, 0x18, 0xa6]⟩

/-- `keccak("transferOwnership(address)")[0:4] = 0xf2fde38b`. -/
axiom transferOwnershipSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr transferOwnershipTransition))).extract 0 4 =
      ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩

/-- The `JUMPDEST` set of `ownable2StepBenchBytecode`, named for the benchmark proof. -/
@[valid_jumps] theorem ownable2StepBenchValidJumps :
    Ethereum.EVM.D_J ownable2StepBenchBytecode 0
      = #[⟨15⟩, ⟨85⟩, ⟨89⟩, ⟨97⟩, ⟨99⟩, ⟨107⟩, ⟨119⟩, ⟨147⟩, ⟨164⟩, ⟨178⟩,
          ⟨183⟩, ⟨191⟩, ⟨200⟩, ⟨202⟩, ⟨254⟩, ⟨263⟩, ⟨272⟩, ⟨275⟩, ⟨283⟩,
          ⟨331⟩, ⟨387⟩, ⟨431⟩, ⟨530⟩, ⟨546⟩, ⟨568⟩] := by
  simpa using validJumps

end OpenZeppelinBench.Ownable2Step
