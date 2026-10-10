import Benchmarks.UniswapV4PoolManager.PoolUpdateTickFeeTrace
import Benchmarks.UniswapV4PoolManager.SignedComparison
import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickLowerFeeGuardExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 x1 : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (h : RD (deployedRuntime v) I g s0 ⟨7662⟩
      (tick :: x0 :: x1 :: tickSlot id (EVM.signed tick) :: R) mem aw rdata evm.accountMap k C) :
    if EVM.signed tick ≤ EVM.signed (slot0TickWord (poolSlot0Word evm id)) then
      if I.perm = false then RDstatic (deployedRuntime v) g s0 else ∃ k' C',
        RD (deployedRuntime v) I g s0 ⟨7679⟩ (x0 :: x1 :: tickSlot id (EVM.signed tick) :: R)
          mem (M aw (UInt256.ofNat 128) ⟨32⟩) rdata (tickFeeWrites evm id (EVM.signed tick)).accountMap k' C'
    else ∃ k' C', RD (deployedRuntime v) I g s0 ⟨7679⟩
      (x0 :: x1 :: tickSlot id (EVM.signed tick) :: R) mem (M aw (UInt256.ofNat 128) ⟨32⟩) rdata evm.accountMap k' C' := by
  have hword : solcSlotWordAt (memLoad (UInt256.ofNat 128) mem) evm.accountMap I = poolSlot0Word evm id := by
    rw [hm]
    exact (storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])).symm
  have hg : UInt256.isZero (UInt256.slt
      (UInt256.signextend (UInt256.ofNat 2) (UInt256.shiftRight
        (solcSlotWordAt (memLoad (UInt256.ofNat 128) mem) evm.accountMap I) (UInt256.ofNat 160))) tick) =
      UInt256.isZero (UInt256.fromBool (decide (EVM.signed (slot0TickWord (poolSlot0Word evm id)) < EVM.signed tick))) := by
    rw [hword, slt_signed]
    rfl
  dsimp only [solcSlotWordAt] at hg
  by_cases hc : EVM.signed tick ≤ EVM.signed (slot0TickWord (poolSlot0Word evm id))
  · rw [if_pos hc]
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_7662_taken
      (by simp only [List.length_cons]; omega)
      (by change UInt256.isZero (UInt256.slt _ tick) ≠ UInt256.ofNat 0
          rw [hg, decide_eq_false (by omega)]; decide +kernel)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have hwrites := tickFeeWritesTrace v false hstack hI hm rd1
    by_cases hp : I.perm = false
    · simpa only [if_pos hp] using hwrites
    · rw [if_neg hp] at hwrites ⊢
      obtain ⟨k2, C2, rd2⟩ := hwrites
      simp only [memoryWords_idem] at rd2
      exact ⟨k2, C2, rd2⟩
  · rw [if_neg hc]
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_7662_fallthrough
      (by simp only [List.length_cons]; omega)
      (by change UInt256.isZero (UInt256.slt _ tick) = UInt256.ofNat 0
          rw [hg, decide_eq_true (by omega)]; rfl) h
    exact ⟨k1, C1, rd1⟩

theorem tickUpperFeeGuardExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 x1 x3 x4 x5 x6 x7 x8 x9 : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+14 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (h : RD (deployedRuntime v) I g s0 ⟨7617⟩
      (x0 :: x1 :: tickSlot id (EVM.signed tick) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tick :: R)
      mem aw rdata evm.accountMap k C) :
    if EVM.signed tick ≤ EVM.signed (slot0TickWord (poolSlot0Word evm id)) then
      if I.perm = false then RDstatic (deployedRuntime v) g s0 else ∃ k' C',
        RD (deployedRuntime v) I g s0 ⟨7132⟩
          (x0 :: x1 :: tickSlot id (EVM.signed tick) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tick :: R)
          mem (M aw (UInt256.ofNat 128) ⟨32⟩) rdata (tickFeeWrites evm id (EVM.signed tick)).accountMap k' C'
    else ∃ k' C', RD (deployedRuntime v) I g s0 ⟨7132⟩
      (x0 :: x1 :: tickSlot id (EVM.signed tick) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tick :: R)
      mem (M aw (UInt256.ofNat 128) ⟨32⟩) rdata evm.accountMap k' C' := by
  have hword : solcSlotWordAt (memLoad (UInt256.ofNat 128) mem) evm.accountMap I = poolSlot0Word evm id := by
    rw [hm]
    exact (storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])).symm
  have hg : UInt256.sgt tick
      (UInt256.signextend (UInt256.ofNat 2) (UInt256.shiftRight
        (solcSlotWordAt (memLoad (UInt256.ofNat 128) mem) evm.accountMap I) (UInt256.ofNat 160))) =
      UInt256.fromBool (decide (EVM.signed (slot0TickWord (poolSlot0Word evm id)) < EVM.signed tick)) := by
    rw [hword, sgt_signed]
    rfl
  dsimp only [solcSlotWordAt] at hg
  by_cases hc : EVM.signed tick ≤ EVM.signed (slot0TickWord (poolSlot0Word evm id))
  · rw [if_pos hc]
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_7617_fallthrough (by omega)
      (by change UInt256.sgt tick _ = UInt256.ofNat 0
          rw [hg, decide_eq_false (by omega)]; rfl) h
    have hwrites := tickFeeWritesTrace v true (by simp only [List.length_cons]; omega) hI hm rd1
    by_cases hp : I.perm = false
    · simpa only [if_pos hp] using hwrites
    · rw [if_neg hp] at hwrites ⊢
      obtain ⟨k2, C2, rd2⟩ := hwrites
      simp only [memoryWords_idem] at rd2
      exact ⟨k2, C2, rd2⟩
  · rw [if_neg hc]
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_7617_taken (by omega)
      (by change UInt256.sgt tick _ ≠ UInt256.ofNat 0
          rw [hg, decide_eq_true (by omega)]; decide +kernel)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact ⟨k1, C1, rd1⟩

theorem tickLowerFeeGuardTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 x1 : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (h : RD (deployedRuntime v) I g s0 ⟨7662⟩
      (tick :: x0 :: x1 :: tickSlot id (EVM.signed tick) :: R) mem aw rdata evm.accountMap k C) :
    if EVM.signed tick ≤ EVM.signed (slot0TickWord (poolSlot0Word evm id)) then
      if I.perm = false then RDstatic (deployedRuntime v) g s0 else ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ⟨7679⟩ (x0 :: x1 :: tickSlot id (EVM.signed tick) :: R)
          mem aw' rdata (tickFeeWrites evm id (EVM.signed tick)).accountMap k' C'
    else ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨7679⟩
      (x0 :: x1 :: tickSlot id (EVM.signed tick) :: R) mem aw' rdata evm.accountMap k' C' := by
  have hr := tickLowerFeeGuardExactTrace v hstack hI hm h
  split_ifs at hr ⊢
  all_goals first | exact hr | (obtain ⟨k', C', rd⟩ := hr; exact ⟨_, k', C', rd⟩)

theorem tickUpperFeeGuardTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 x1 x3 x4 x5 x6 x7 x8 x9 : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+14 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (h : RD (deployedRuntime v) I g s0 ⟨7617⟩
      (x0 :: x1 :: tickSlot id (EVM.signed tick) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tick :: R)
      mem aw rdata evm.accountMap k C) :
    if EVM.signed tick ≤ EVM.signed (slot0TickWord (poolSlot0Word evm id)) then
      if I.perm = false then RDstatic (deployedRuntime v) g s0 else ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ⟨7132⟩
          (x0 :: x1 :: tickSlot id (EVM.signed tick) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tick :: R)
          mem aw' rdata (tickFeeWrites evm id (EVM.signed tick)).accountMap k' C'
    else ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨7132⟩
      (x0 :: x1 :: tickSlot id (EVM.signed tick) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tick :: R)
      mem aw' rdata evm.accountMap k' C' := by
  have hr := tickUpperFeeGuardExactTrace v hstack hI hm h
  split_ifs at hr ⊢
  all_goals first | exact hr | (obtain ⟨k', C', rd⟩ := hr; exact ⟨_, k', C', rd⟩)

end Benchmarks.UniswapV4PoolManager
