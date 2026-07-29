import Examples.OpenZeppelinBench.Pausable.Bytecode
import Solm.Semantics

open Solm Ethereum Ethereum.EVM

namespace OpenZeppelinBench.Pausable

/-!
# PausableBench trusted bytecode facts

The selector facts are trusted because `ffi.KEC` is opaque to Lean.  The jump-destination table is
computed from the deployed runtime byte array in `Bytecode.lean`; this file gives it the Phase-0
benchmark name used by the proof.
-/

/-- `keccak("unpause()")[0:4] = 0x3f4ba83a`. -/
axiom unpauseSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr unpauseTransition))).extract 0 4 =
      ⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩

/-- `keccak("paused()")[0:4] = 0x5c975abb`. -/
axiom pausedSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr pausedTransition))).extract 0 4 =
      ⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩

/-- `keccak("pause()")[0:4] = 0x8456cb59`. -/
axiom pauseSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr pauseTransition))).extract 0 4 =
      ⟨#[0x84, 0x56, 0xcb, 0x59]⟩

/-- `keccak("guardedWhenNotPaused()")[0:4] = 0x9bb8bcec`. -/
axiom guardedWhenNotPausedSelectorBytes :
    (ffi.KEC
      (String.toByteArray (Solm.transitionSigStr guardedWhenNotPausedTransition))).extract 0 4 =
      ⟨#[0x9b, 0xb8, 0xbc, 0xec]⟩

/-- `keccak("guardedWhenPaused()")[0:4] = 0xddf70309`. -/
axiom guardedWhenPausedSelectorBytes :
    (ffi.KEC
      (String.toByteArray (Solm.transitionSigStr guardedWhenPausedTransition))).extract 0 4 =
      ⟨#[0xdd, 0xf7, 0x03, 0x09]⟩

/-- The `JUMPDEST` set of `pausableBenchBytecode`, named for the benchmark proof. -/
@[valid_jumps] theorem pausableBenchValidJumps :
    Ethereum.EVM.D_J pausableBenchBytecode 0
      = #[⟨15⟩, ⟨85⟩, ⟨89⟩, ⟨97⟩, ⟨99⟩, ⟨105⟩, ⟨125⟩, ⟨133⟩, ⟨141⟩,
          ⟨149⟩, ⟨157⟩, ⟨159⟩, ⟨167⟩, ⟨176⟩, ⟨182⟩, ⟨191⟩, ⟨199⟩,
          ⟨243⟩, ⟨272⟩, ⟨280⟩, ⟨332⟩, ⟨367⟩] := by
  simpa using validJumps

end OpenZeppelinBench.Pausable
