import Benchmarks.Morpho.MetaMorphoV1_1.SubmitGuardianGuards
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitGuardianSource
import Benchmarks.Morpho.MetaMorphoV1_1.ScheduledGuardianRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.ScheduledGuardianStatic
import Benchmarks.Morpho.MetaMorphoV1_1.SetPendingRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_013

/-! Immediate and deferred runtime outcomes for guardian submission. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem submitGuardianReachImmediate {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : AccountAddress}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hz : guardianAddress evm = AccountAddress.ofNat 0)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨4445⟩
      (guardianWord evm :: UInt256.ofNat value.val :: UInt256.ofNat value.val :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨15404⟩
      (UInt256.ofNat value.val :: ⟨1867⟩ :: R) mem aw rdata evm.accountMap k' C' := by
  have r1 := metaMorphoV1_1_block_4445_fallthrough (immWords := wordsOf (immStore v))
    (by simpa only [List.length] using hstack) ((guardianWord_zero_iff evm).mpr hz) rd
  have r2 := metaMorphoV1_1_block_4449 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
  exact ⟨_, _, r2⟩

set_option maxRecDepth 2000 in
theorem submitGuardianReachScheduled {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : AccountAddress}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hn : guardianAddress evm ≠ AccountAddress.ofNat 0)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨4445⟩
      (guardianWord evm :: UInt256.ofNat value.val :: UInt256.ofNat value.val :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨4458⟩
      (UInt256.ofNat value.val :: UInt256.ofNat value.val :: R)
      mem aw rdata evm.accountMap k' C' := by
  exact ⟨_, _, metaMorphoV1_1_block_4445_taken (immWords := wordsOf (immStore v))
    (by simpa only [List.length] using hstack) ((guardianWord_zero_iff evm).not.mpr hn)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd⟩

set_option maxRecDepth 2000 in
theorem submitGuardianStoreReturn {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : AccountAddress}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hperm : evm.executionEnv.perm = true) (hfit : submitGuardianFits evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨4445⟩
      (guardianWord evm :: UInt256.ofNat value.val :: UInt256.ofNat value.val :: R)
      mem aw rdata evm.accountMap k C) :
    RDret (deployedRuntime v) g s0 (submitGuardianState evm value).accountMap
      ByteArray.empty := by
  by_cases hz : guardianAddress evm = AccountAddress.ofNat 0
  · rw [submitGuardianState, if_pos hz]
    obtain ⟨_, _, r1⟩ := submitGuardianReachImmediate v (by omega) hz rd
    obtain ⟨_, _, _, r2⟩ := setGuardianReturn (evm := evm) v hstack hperm
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
    exact metaMorphoV1_1_block_1867 (immWords := wordsOf (immStore v)) (by omega) r2
  · rw [submitGuardianState, if_neg hz]
    obtain ⟨_, _, r1⟩ := submitGuardianReachScheduled v (by omega) hz rd
    exact scheduledGuardianReturn v hstack hperm (hfit.resolve_left hz) r1

theorem submitGuardianStoreStatic {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : AccountAddress}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hperm : evm.executionEnv.perm = false)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨4445⟩
      (guardianWord evm :: UInt256.ofNat value.val :: UInt256.ofNat value.val :: R)
      mem aw rdata evm.accountMap k C) : RDstatic (deployedRuntime v) g s0 := by
  by_cases hz : guardianAddress evm = AccountAddress.ofNat 0
  · obtain ⟨_, _, r1⟩ := submitGuardianReachImmediate v (by omega) hz rd
    exact setGuardianStatic v hstack hperm r1
  · obtain ⟨_, _, r1⟩ := submitGuardianReachScheduled v (by omega) hz rd
    exact scheduledGuardianStatic v hstack hperm r1

theorem submitGuardianRevertOverflow {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : AccountAddress}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hperm : evm.executionEnv.perm = true) (hbad : ¬ submitGuardianFits evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨4445⟩
      (guardianWord evm :: UInt256.ofNat value.val :: UInt256.ofNat value.val :: R)
      mem aw rdata evm.accountMap k C) : RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, r1⟩ := submitGuardianReachScheduled v (by omega) (fun hz ↦ hbad (.inl hz)) rd
  exact scheduledGuardianRevert v hstack hperm (fun hfit ↦ hbad (.inr hfit)) r1

end Benchmarks.Morpho.MetaMorphoV1_1
