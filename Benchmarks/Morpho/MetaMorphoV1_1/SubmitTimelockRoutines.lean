import Benchmarks.Morpho.MetaMorphoV1_1.SubmitTimelockGuards
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitTimelockSource
import Benchmarks.Morpho.MetaMorphoV1_1.ScheduledTimelockRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.ScheduledTimelockStatic
import Benchmarks.Morpho.MetaMorphoV1_1.SetPendingRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_013

/-! Immediate and deferred runtime outcomes for timelock submission. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem submitTimelockReachImmediate {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hz : (pendingTimelockDelay evm).toNat < value.toNat)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨6938⟩
      (pendingTimelockDelay evm :: value :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨14755⟩
      (value :: ⟨1867⟩ :: R) mem aw rdata evm.accountMap k' C' := by
  have r1 := metaMorphoV1_1_block_6938_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (by rw [ugt_one hz]; decide) rd
  have r2 := metaMorphoV1_1_block_6946 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
  exact ⟨_, _, r2⟩

set_option maxRecDepth 2000 in
theorem submitTimelockReachScheduled {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hn : ¬ (pendingTimelockDelay evm).toNat < value.toNat)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨6938⟩
      (pendingTimelockDelay evm :: value :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨6955⟩
      (pendingTimelockDelay evm :: value :: R)
      mem aw rdata evm.accountMap k' C' := by
  exact ⟨_, _, metaMorphoV1_1_block_6938_taken (immWords := wordsOf (immStore v))
    (by omega) (by rw [ugt_zero (Nat.le_of_not_gt hn)]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd⟩

set_option maxRecDepth 2000 in
theorem submitTimelockStoreReturn {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hperm : evm.executionEnv.perm = true) (hbound : timelockInBounds value)
    (hfit : submitTimelockFits evm value)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨6938⟩
      (pendingTimelockDelay evm :: value :: R)
      mem aw rdata evm.accountMap k C) :
    RDret (deployedRuntime v) g s0 (submitTimelockState evm value).accountMap
      ByteArray.empty := by
  by_cases hz : (pendingTimelockDelay evm).toNat < value.toNat
  · rw [submitTimelockState, if_pos hz]
    obtain ⟨_, _, r1⟩ := submitTimelockReachImmediate v (by omega) hz rd
    obtain ⟨_, _, _, r2⟩ := setTimelockReturn (evm := evm) v (by omega) hperm
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
    exact metaMorphoV1_1_block_1867 (immWords := wordsOf (immStore v)) (by omega) r2
  · rw [submitTimelockState, if_neg hz]
    obtain ⟨_, _, r1⟩ := submitTimelockReachScheduled v (by omega) hz rd
    exact scheduledTimelockReturn v hstack hperm hbound (hfit.resolve_left hz) r1

theorem submitTimelockStoreStatic {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hperm : evm.executionEnv.perm = false)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨6938⟩
      (pendingTimelockDelay evm :: value :: R)
      mem aw rdata evm.accountMap k C) : RDstatic (deployedRuntime v) g s0 := by
  by_cases hz : (pendingTimelockDelay evm).toNat < value.toNat
  · obtain ⟨_, _, r1⟩ := submitTimelockReachImmediate v (by omega) hz rd
    exact setTimelockStatic v (by omega) hperm r1
  · obtain ⟨_, _, r1⟩ := submitTimelockReachScheduled v (by omega) hz rd
    exact scheduledTimelockStatic v (by omega) hperm r1

theorem submitTimelockRevertOverflow {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hperm : evm.executionEnv.perm = true) (hbound : timelockInBounds value)
    (hbad : ¬ submitTimelockFits evm value)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨6938⟩
      (pendingTimelockDelay evm :: value :: R)
      mem aw rdata evm.accountMap k C) : RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, r1⟩ := submitTimelockReachScheduled v (by omega) (fun hz ↦ hbad (.inl hz)) rd
  exact scheduledTimelockRevert v hstack hperm hbound (fun hfit ↦ hbad (.inr hfit)) r1

end Benchmarks.Morpho.MetaMorphoV1_1
