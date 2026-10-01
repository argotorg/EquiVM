import Examples.OpenZeppelinBench.Pausable.Bytecode
import Solm.Semantics

open Solm Ethereum Ethereum.EVM

namespace OpenZeppelinBench.Pausable

/-!
# PausableBench selector facts

The jump-destination table is computed from the deployed runtime byte array in `Bytecode.lean`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("unpause()")[0:4] = 0x3f4ba83a`. -/
theorem unpauseSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr unpauseTransition))).extract 0 4 =
      ⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩ := by decide +kernel

/-- `keccak("paused()")[0:4] = 0x5c975abb`. -/
theorem pausedSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr pausedTransition))).extract 0 4 =
      ⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩ := by decide +kernel

/-- `keccak("pause()")[0:4] = 0x8456cb59`. -/
theorem pauseSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr pauseTransition))).extract 0 4 =
      ⟨#[0x84, 0x56, 0xcb, 0x59]⟩ := by decide +kernel

/-- `keccak("guardedWhenNotPaused()")[0:4] = 0x9bb8bcec`. -/
theorem guardedWhenNotPausedSelectorBytes :
    (KEC
      (String.toByteArray (Solm.transitionSigStr guardedWhenNotPausedTransition))).extract 0 4 =
      ⟨#[0x9b, 0xb8, 0xbc, 0xec]⟩ := by decide +kernel

/-- `keccak("guardedWhenPaused()")[0:4] = 0xddf70309`. -/
theorem guardedWhenPausedSelectorBytes :
    (KEC
      (String.toByteArray (Solm.transitionSigStr guardedWhenPausedTransition))).extract 0 4 =
      ⟨#[0xdd, 0xf7, 0x03, 0x09]⟩ := by decide +kernel

end OpenZeppelinBench.Pausable
