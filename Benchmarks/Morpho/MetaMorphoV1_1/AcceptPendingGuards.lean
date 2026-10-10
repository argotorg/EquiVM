import Benchmarks.Morpho.MetaMorphoV1_1.AcceptPendingEntry
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_024

/-! Runtime validation of pending update timestamps. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

def acceptPendingTimePC (guardian : Bool) : UInt256 := if guardian then ⟨4211⟩ else ⟨4925⟩
def acceptPendingValuePC (guardian : Bool) : UInt256 := if guardian then ⟨4217⟩ else ⟨4931⟩

set_option maxRecDepth 2000 in
theorem acceptPendingReadNonzero {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 4 ≤ 1024)
    (hnz : pendingUpdateTime guardian (pendingUpdateWord guardian evm) ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 (acceptPendingReadPC guardian) R
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 (acceptPendingTimePC guardian)
      (pendingUpdateTime guardian (pendingUpdateWord guardian evm) ::
        pendingUpdateWord guardian evm :: R) mem aw rdata evm.accountMap k' C' := by
  have hc := isZero_eq_zero_of_ne hnz
  cases guardian
  · exact metaMorphoV1_1_block_4912_fallthrough
      (immWords := wordsOf (immStore v)) hstack hc rd
  · exact metaMorphoV1_1_block_4189_fallthrough
      (immWords := wordsOf (immStore v)) hstack hc rd

set_option maxRecDepth 2000 in
theorem acceptPendingRevertMissing {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 4 ≤ 1024)
    (hz : pendingUpdateTime guardian (pendingUpdateWord guardian evm) = ⟨0⟩)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 (acceptPendingReadPC guardian) R
      mem aw rdata evm.accountMap k C) : RDrev (deployedRuntime v) g s0 := by
  have hc : UInt256.isZero (pendingUpdateTime guardian (pendingUpdateWord guardian evm)) ≠
      ⟨0⟩ := by rw [hz]; decide
  have hrev : ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨4249⟩
      (pendingUpdateTime guardian (pendingUpdateWord guardian evm) ::
        pendingUpdateWord guardian evm :: R) mem aw rdata evm.accountMap k' C' := by
    cases guardian
    · exact metaMorphoV1_1_block_4912_taken (immWords := wordsOf (immStore v)) hstack hc
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    · exact metaMorphoV1_1_block_4189_taken (immWords := wordsOf (immStore v)) hstack hc
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨_, _, hrev⟩ := hrev
  exact metaMorphoV1_1_block_4249 (immWords := wordsOf (immStore v))
    (by simp only [List.length]; omega) hrev

set_option maxRecDepth 2000 in
theorem acceptPendingTimePassed {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {time : UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 2 ≤ 1024)
    (htime : time.toNat ≤ (UInt256.ofNat I.header.timestamp).toNat)
    (rd : RD (deployedRuntime v) I g s0 (acceptPendingTimePC guardian) (time :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 (acceptPendingValuePC guardian) R
      mem aw rdata σ k' C' := by
  have hc := ult_zero htime
  cases guardian
  · exact ⟨_, _, metaMorphoV1_1_block_4925_fallthrough
      (immWords := wordsOf (immStore v)) hstack hc rd⟩
  · exact ⟨_, _, metaMorphoV1_1_block_4211_fallthrough
      (immWords := wordsOf (immStore v)) hstack hc rd⟩

set_option maxRecDepth 2000 in
theorem acceptPendingRevertPremature {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {time : UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 2 ≤ 1024)
    (htime : ¬ time.toNat ≤ (UInt256.ofNat I.header.timestamp).toNat)
    (rd : RD (deployedRuntime v) I g s0 (acceptPendingTimePC guardian) (time :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hc : UInt256.lt (UInt256.ofNat I.header.timestamp) time ≠ ⟨0⟩ := by
    rw [ult_one (by omega : (UInt256.ofNat I.header.timestamp).toNat < time.toNat)]
    decide
  have hrev : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨4234⟩ R mem aw rdata σ k' C' := by
    cases guardian
    · exact ⟨_, _, metaMorphoV1_1_block_4925_taken
        (immWords := wordsOf (immStore v)) hstack hc
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd⟩
    · exact ⟨_, _, metaMorphoV1_1_block_4211_taken
        (immWords := wordsOf (immStore v)) hstack hc
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd⟩
  obtain ⟨_, _, hrev⟩ := hrev
  exact metaMorphoV1_1_block_4234 (immWords := wordsOf (immStore v)) hstack hrev

theorem acceptPendingReachValue {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 4 ≤ 1024)
    (hgood : acceptPendingAllowed guardian evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 (acceptPendingReadPC guardian) R
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 (acceptPendingValuePC guardian)
      (pendingUpdateWord guardian evm :: R) mem aw rdata evm.accountMap k' C' := by
  obtain ⟨_, _, r1⟩ := acceptPendingReadNonzero v guardian hstack hgood.1 rd
  exact acceptPendingTimePassed v guardian (by simpa using (by omega : R.length + 3 ≤ 1024))
    hgood.2 r1

theorem acceptPendingRevertTime {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 4 ≤ 1024)
    (hbad : ¬ acceptPendingAllowed guardian evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 (acceptPendingReadPC guardian) R
      mem aw rdata evm.accountMap k C) : RDrev (deployedRuntime v) g s0 := by
  by_cases hz : pendingUpdateTime guardian (pendingUpdateWord guardian evm) = ⟨0⟩
  · exact acceptPendingRevertMissing v guardian hstack hz rd
  · obtain ⟨_, _, r1⟩ := acceptPendingReadNonzero v guardian hstack hz rd
    exact acceptPendingRevertPremature v guardian
      (by simpa using (by omega : R.length + 3 ≤ 1024)) (fun ht ↦ hbad ⟨hz, ht⟩) r1

end Benchmarks.Morpho.MetaMorphoV1_1
