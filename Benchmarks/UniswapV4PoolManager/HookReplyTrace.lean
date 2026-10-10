import Benchmarks.UniswapV4PoolManager.HookCallSource
import Benchmarks.UniswapV4PoolManager.HookReplyMemory
import Benchmarks.UniswapV4PoolManager.MemoryGas
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_044
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_046

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem hookReplyDecisionTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw x0 x1 cond ret ptr : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+5 ≤ 1024) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16263⟩
      (x0 :: x1 :: cond :: ret :: ptr :: R) mem aw out σ k C) :
    if cond = ⟨0⟩ then ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ret (ptr :: R) mem aw out σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hc : cond = ⟨0⟩
  · rw [if_pos hc]
    have rd1 := poolManagerBlocks.poolManager_block_16263_fallthrough
      (by simp only [List.length_cons]; omega) hc h
    have rd2 := poolManagerBlocks.poolManager_block_16270
      (by simp only [List.length_cons]; omega) hret rd1
    exact ⟨_, _, by omega, rd2⟩
  · rw [if_neg hc]
    have rd1 := poolManagerBlocks.poolManager_block_16263_taken
      (by simp only [List.length_cons]; omega) hc
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_15621
      (by change R.length+2+2 ≤ 1024; omega) rd1

theorem hookReplyCostTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem data out : ByteArray} {aw ptr hook ret free : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+7 ≤ 1024)
    (hmem : 96 ≤ mem.size) (hdata : BytesObjectView mem ptr data)
    (hd : 32 ≤ data.size) (ho : out.size < UInt256.size) (hlo : 96 ≤ ptr.toNat+32)
    (hbefore : ptr.toNat+32+data.size ≤ free.toNat) (hfit : free.toNat+32 < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16189⟩
      (ptr :: hook :: ret :: (ptr+⟨32⟩) :: R) mem aw out σ k C) :
    if hookReplyValid data out then ∃ aw' k' C',
      C+Cₘ aw' ≤ C'+Cₘ aw ∧ (free.toNat+out.size+63)/32 ≤ aw'.toNat ∧
      RD (deployedRuntime v) I g s0 ret (free :: R) (solcReturnDataMem mem free out) aw' out σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hm : poolManagerBlocks.poolManager_block_16189_taken_memory (mem := mem) (rdata := out) =
      solcReturnDataMem mem free out := by
    simp only [poolManagerBlocks.poolManager_block_16189_taken_memory, hfree,
      UInt256.toNat_ofNat_of_lt ho]
    rfl
  have hm' : poolManagerBlocks.poolManager_block_16189_fallthrough_memory (mem := mem) (rdata := out) =
      solcReturnDataMem mem free out := hm
  have hlength := returnDataMemory_length mem free out hfit
  have hguard : (⟨0⟩ : UInt256).toNat+(UInt256.ofNat out.size).toNat ≤ out.size := by
    rw [UInt256.toNat_ofNat_of_lt ho]; change 0+out.size ≤ out.size; omega
  by_cases hlong : 32 ≤ out.size
  · have hlt : UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨0⟩ :=
      ult_zero (by rw [UInt256.toNat_ofNat_of_lt ho]; exact hlong)
    have rd1 := poolManagerBlocks.poolManager_block_16189_taken hstack hguard
      (by change UInt256.isZero (UInt256.lt (memLoad (memLoad (UInt256.ofNat 64) mem)
            (poolManagerBlocks.poolManager_block_16189_taken_memory (mem := mem) (rdata := out))) _) ≠ _
          rw [hfree, hm, hlength, hlt]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have hst : poolManagerBlocks.poolManager_block_16189_taken_stack (mem := mem) (rdata := out)
        (x2 := ret) (x3 := ptr+⟨32⟩) (R := R) =
        ((free+⟨32⟩) :: (ptr+⟨32⟩) :: ⟨0⟩ :: ret :: free :: R) := by
      change (memLoad (UInt256.ofNat 64) mem+⟨32⟩) :: (ptr+⟨32⟩) ::
        UInt256.lt (memLoad (memLoad (UInt256.ofNat 64) mem)
          (poolManagerBlocks.poolManager_block_16189_taken_memory (mem := mem) (rdata := out))) _ ::
        ret :: memLoad (UInt256.ofNat 64) mem :: R = _
      rw [hfree, hm, hlength, hlt]
    rw [hst, hm, hfree] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_16271
      (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    have heq := hookReplyMemory_selector hmem hdata hd hlong hlo hbefore hfit
    have hr := hookReplyDecisionTrace v (by omega) hret rd2
    simp only [poolManagerBlocks.poolManager_block_16271_stack] at hr
    change (if UInt256.isZero (UInt256.eq
      (UInt256.land bytes4Mask (memLoad (ptr+⟨32⟩) (solcReturnDataMem mem free out)))
      (UInt256.land bytes4Mask (memLoad (free+⟨32⟩) (solcReturnDataMem mem free out)))) = ⟨0⟩
      then _ else _) at hr
    by_cases hsel : data.extract 0 4 = out.extract 0 4
    · have hw := heq.mpr hsel
      have hc : UInt256.isZero (UInt256.eq
          (UInt256.land bytes4Mask (memLoad (ptr+⟨32⟩) (solcReturnDataMem mem free out)))
          (UInt256.land bytes4Mask (memLoad (free+⟨32⟩) (solcReturnDataMem mem free out)))) = ⟨0⟩ := by
        rw [hw]; simp only [UInt256.eq, UInt256.fromBool, decide_true]; rfl
      rw [if_pos hc] at hr
      simp only [hookReplyValid, hlong, hsel.symm, and_self, if_true]
      obtain ⟨k3, C3, hcost, hr⟩ := hr
      refine ⟨_, k3, C3, ?_, ?_, hr⟩
      · dsimp only [memExpansionCost] at hcost
        omega
      · let a3 := M (M (M aw (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩) free ⟨32⟩
        let a4 := M a3 (free+UInt256.ofNat 32) (UInt256.ofNat out.size)
        have hs4 := memoryWords_ge_span a3 (free+UInt256.ofNat 32) (UInt256.ofNat out.size)
          (by rw [UInt256.toNat_ofNat_of_lt ho]; omega)
        rw [uadd_word_ofNat_toNat free 32 hfit, UInt256.toNat_ofNat_of_lt ho] at hs4
        have hs5 := memoryWords_ge_active a4 free ⟨32⟩
        have hs6 := memoryWords_ge_active (M a4 free ⟨32⟩) (free+UInt256.ofNat 32) ⟨32⟩
        have hs7 := memoryWords_ge_active (M (M a4 free ⟨32⟩) (free+UInt256.ofNat 32) ⟨32⟩)
          (ptr+⟨32⟩) ⟨32⟩
        change (free.toNat+out.size+63)/32 ≤
          (M (M (M a4 free ⟨32⟩) (free+UInt256.ofNat 32) ⟨32⟩) (ptr+⟨32⟩) ⟨32⟩).toNat
        change (free.toNat+32+out.size+31)/32 ≤ a4.toNat at hs4
        omega
    · have hw := fun hh => hsel (heq.mp hh)
      have hc : UInt256.isZero (UInt256.eq
          (UInt256.land bytes4Mask (memLoad (ptr+⟨32⟩) (solcReturnDataMem mem free out)))
          (UInt256.land bytes4Mask (memLoad (free+⟨32⟩) (solcReturnDataMem mem free out)))) ≠ ⟨0⟩ := by
        simp only [UInt256.eq, UInt256.fromBool, decide_eq_false hw]; decide
      rw [if_neg hc] at hr
      simp only [hookReplyValid, hlong, show ¬out.extract 0 4 = data.extract 0 4 from Ne.symm hsel,
        and_false, if_false]
      exact hr
  · have hlt : UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨1⟩ :=
      ult_one (by rw [UInt256.toNat_ofNat_of_lt ho]; change out.size < 32; omega)
    obtain ⟨aw1, k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_16189_fallthrough_packed hstack hguard
      (by change UInt256.isZero (UInt256.lt (memLoad (memLoad (UInt256.ofNat 64) mem)
            (poolManagerBlocks.poolManager_block_16189_fallthrough_memory (mem := mem) (rdata := out))) _) = _
          rw [hfree, hm', hlength, hlt]; decide) h
    have hst : poolManagerBlocks.poolManager_block_16189_fallthrough_stack (mem := mem) (rdata := out)
        (x2 := ret) (x3 := ptr+⟨32⟩) (R := R) =
        ((free+⟨32⟩) :: (ptr+⟨32⟩) :: ⟨1⟩ :: ret :: free :: R) := by
      change (memLoad (UInt256.ofNat 64) mem+⟨32⟩) :: (ptr+⟨32⟩) ::
        UInt256.lt (memLoad (memLoad (UInt256.ofNat 64) mem)
          (poolManagerBlocks.poolManager_block_16189_fallthrough_memory (mem := mem) (rdata := out))) _ ::
        ret :: memLoad (UInt256.ofNat 64) mem :: R = _
      rw [hfree, hm', hlength, hlt]
    rw [hst, hm'] at rd1
    have hr := hookReplyDecisionTrace v (by omega) hret rd1
    simp only [hookReplyValid, hlong, false_and, if_false]
    simpa only [show (⟨1⟩ : UInt256) ≠ ⟨0⟩ from by decide, if_false] using hr

theorem hookReplyTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem data out : ByteArray} {aw ptr hook ret free : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+7 ≤ 1024)
    (hmem : 96 ≤ mem.size) (hdata : BytesObjectView mem ptr data)
    (hd : 32 ≤ data.size) (ho : out.size < UInt256.size) (hlo : 96 ≤ ptr.toNat+32)
    (hbefore : ptr.toNat+32+data.size ≤ free.toNat) (hfit : free.toNat+32 < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16189⟩
      (ptr :: hook :: ret :: (ptr+⟨32⟩) :: R) mem aw out σ k C) :
    if hookReplyValid data out then ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ret (free :: R) (solcReturnDataMem mem free out) aw' out σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hr := hookReplyCostTrace v hstack hmem hdata hd ho hlo hbefore hfit hfree hret h
  split_ifs at hr ⊢ with hv
  · obtain ⟨aw', k', C', _, _, hr⟩ := hr
    exact ⟨aw', k', C', hr⟩
  · exact hr

end Benchmarks.UniswapV4PoolManager
