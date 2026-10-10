import Benchmarks.UniswapV4PoolManager.InitializeValidationSource
import Benchmarks.UniswapV4PoolManager.HookValidationTrace
import Benchmarks.UniswapV4PoolManager.PoolKeyView
import Benchmarks.UniswapV4PoolManager.MemoryGas
import Benchmarks.UniswapV4PoolManager.SignedComparison
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_014
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_016

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem initializeValidationTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw keyPtr price : UInt256} {key : PoolKeyWords}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+17 ≤ 1024)
    (hv : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (haw : aw.toNat ≤ 2048) (hp : keyPtr.toNat ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨4088⟩ (price :: keyPtr :: price :: R) mem aw rdata σ k C) :
    if initializeKeyValid key then ∃ aw' k' C', aw'.toNat ≤ 2048 ∧
      RD (deployedRuntime v) I g s0 ⟨4257⟩
        (initialLPFeeWord key.fee :: (keyPtr+⟨32⟩) :: (keyPtr+⟨64⟩) :: (keyPtr+⟨128⟩) ::
          keyPtr :: price :: (keyPtr+⟨96⟩) :: price :: R) mem aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hs : UInt256.signextend (UInt256.ofNat 2) (memLoad (keyPtr+UInt256.ofNat 96) mem) =
      key.tickSpacing := (congrArg (UInt256.signextend (UInt256.ofNat 2)) (hv.load (i := 3) rfl)).trans
        ((signextend24_eq_iff _).mpr hc.2.2.2.1)
  have h0load : memLoad keyPtr mem = key.currency0 := by
    have hh := hv.load (i := 0) rfl
    change memLoad (keyPtr+⟨0⟩) mem = key.currency0 at hh
    simpa only [u256_add_zero] using hh
  have h0 : UInt256.land (memLoad keyPtr mem)
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = key.currency0 := by
    rw [h0load]; exact solcAddrMask_clean hc.1
  have h1 : UInt256.land (memLoad (keyPtr+UInt256.ofNat 32) mem)
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = key.currency1 := by
    rw [hv.load (i := 1) rfl]; exact solcAddrMask_clean hc.2.1
  have hh : UInt256.land (memLoad (keyPtr+UInt256.ofNat 128) mem)
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = key.hooks := by
    rw [hv.load (i := 4) rfl]; exact solcAddrMask_clean hc.2.2.2.2
  have he : UInt256.land (memLoad (keyPtr+UInt256.ofNat 64) mem) (UInt256.ofNat 16777215) = key.fee := by
    rw [hv.load (i := 2) rfl]; exact u256LandMaskCleanOfToNat _ _ rfl hc.2.2.1
  have hgt : UInt256.sgt (UInt256.signextend (UInt256.ofNat 2)
      (memLoad (keyPtr+UInt256.ofNat 96) mem)) (UInt256.ofNat 32767) =
      (decide (32767 < EVM.signed key.tickSpacing)).toUInt256 := by
    rw [hs, sgt_signed]; rfl
  have hlt : UInt256.slt (UInt256.signextend (UInt256.ofNat 2)
      (memLoad (keyPtr+UInt256.ofNat 96) mem)) (UInt256.ofNat 1) =
      (decide (EVM.signed key.tickSpacing < 1)).toUInt256 := by
    rw [hs, slt_signed]; rfl
  by_cases ht0 : EVM.signed key.tickSpacing ≤ 32767
  · have hg0 : UInt256.sgt (UInt256.signextend (UInt256.ofNat 2)
        (memLoad (keyPtr+UInt256.ofNat 96) mem)) (UInt256.ofNat 32767) = ⟨0⟩ := by
      rw [hgt, decide_eq_false (by omega)]; rfl
    obtain ⟨k1, C1, rd1⟩ := RD.pack (poolManagerBlocks.poolManager_block_4088_fallthrough
      (by simp only [List.length_cons]; omega) hg0 h)
    simp only [poolManagerBlocks.poolManager_block_4088_fallthrough_stack, hs] at rd1
    by_cases ht1 : 1 ≤ EVM.signed key.tickSpacing
    · have hg1 : UInt256.slt (UInt256.signextend (UInt256.ofNat 2)
          (memLoad (keyPtr+UInt256.ofNat 96) mem)) (UInt256.ofNat 1) = ⟨0⟩ := by
        rw [hlt, decide_eq_false (by omega)]; rfl
      obtain ⟨k2, C2, rd2⟩ := RD.pack (poolManagerBlocks.poolManager_block_4108_fallthrough
        (by simp only [List.length_cons]; omega) hg1 rd1)
      simp only [poolManagerBlocks.poolManager_block_4108_fallthrough_stack, hs] at rd2
      by_cases hord : key.currency0.toNat < key.currency1.toNat
      · have hg2 : UInt256.isZero (UInt256.lt
            (UInt256.land (memLoad keyPtr mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))
            (UInt256.land (memLoad (keyPtr+UInt256.ofNat 32) mem)
              (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = ⟨0⟩ := by
          rw [h0, h1, ult_one hord]; rfl
        obtain ⟨k3, C3, rd3⟩ := RD.pack (poolManagerBlocks.poolManager_block_4122_fallthrough
          (by simp only [List.length_cons]; omega) hg2 rd2)
        simp only [poolManagerBlocks.poolManager_block_4122_fallthrough_stack, h0, h1] at rd3
        obtain ⟨k4, C4, rd4⟩ := RD.pack (poolManagerBlocks.poolManager_block_4184
          (by simp only [List.length_cons]; omega)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3)
        simp only [poolManagerBlocks.poolManager_block_4184_stack, hh, he] at rd4
        obtain ⟨k5, C5, rd5⟩ := hookValidationTrace v (by simp only [List.length_cons]; omega)
          hc.2.2.2.2 hc.2.2.1 (by rw [deployedRuntime_jumps]; jump_dest) rd4
        by_cases hvalid : hookAddressValid key.hooks key.fee = true
        · have rd6 := poolManagerBlocks.poolManager_block_4236_fallthrough
            (by simp only [List.length_cons]; omega) (by rw [hvalid]; rfl) rd5
          obtain ⟨k7, C7, rd7⟩ := RD.pack (poolManagerBlocks.poolManager_block_4242
            (by simp only [List.length_cons]; omega)
            (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd6)
          simp only [poolManagerBlocks.poolManager_block_4242_stack, he] at rd7
          have hfee := initialLPFeeTrace v (by simp only [List.length_cons]; omega) hc.2.2.1
            (by rw [deployedRuntime_jumps]; jump_dest) rd7
          by_cases hallowed : initialLPFeeAllowed key.fee
          · rw [if_pos (show initializeKeyValid key from ⟨ht0, ht1, hord, hvalid, hallowed⟩)]
            rw [if_pos hallowed] at hfee
            obtain ⟨k8, C8, rd8⟩ := hfee
            refine ⟨_, k8, C8, ?_, rd8⟩
            clear * - haw hp
            iterate 7 apply memoryWords_le
            · exact haw
            all_goals
              simp only [uadd_toNat, UInt256.size,
                show (UInt256.ofNat 32).toNat = 32 from rfl,
                show (UInt256.ofNat 64).toNat = 64 from rfl,
                show (UInt256.ofNat 96).toNat = 96 from rfl,
                show (UInt256.ofNat 128).toNat = 128 from rfl,
                show (⟨32⟩ : UInt256).toNat = 32 from rfl]
              omega
          · rw [if_neg (fun hg => hallowed hg.2.2.2.2)]
            rw [if_neg hallowed] at hfee
            exact hfee
        · rw [if_neg (fun hg => hvalid hg.2.2.2.1)]
          have hf : hookAddressValid key.hooks key.fee = false := Bool.eq_false_iff.mpr hvalid
          have rd6 := poolManagerBlocks.poolManager_block_4236_taken
            (by simp only [List.length_cons]; omega) (by rw [hf]; decide)
            (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd5
          exact poolManagerBlocks.poolManager_block_5015 (by simp only [List.length_cons]; omega) rd6
      · rw [if_neg (fun hg => hord hg.2.2.1)]
        have hg2 : UInt256.isZero (UInt256.lt
            (UInt256.land (memLoad keyPtr mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))
            (UInt256.land (memLoad (keyPtr+UInt256.ofNat 32) mem)
              (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ ⟨0⟩ := by
          rw [h0, h1, ult_zero (by omega)]; decide
        have rd3 := poolManagerBlocks.poolManager_block_4122_taken
          (by simp only [List.length_cons]; omega) hg2
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
        exact poolManagerBlocks.poolManager_block_5058 (by simp only [List.length_cons]; omega) rd3
    · rw [if_neg (fun hg => ht1 hg.2.1)]
      have hg1 : UInt256.slt (UInt256.signextend (UInt256.ofNat 2)
          (memLoad (keyPtr+UInt256.ofNat 96) mem)) (UInt256.ofNat 1) ≠ ⟨0⟩ := by
        rw [hlt, decide_eq_true (by omega)]; decide
      have rd2 := poolManagerBlocks.poolManager_block_4108_taken
        (by simp only [List.length_cons]; omega) hg1
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact poolManagerBlocks.poolManager_block_5113 (by simp only [List.length_cons]; omega) rd2
  · rw [if_neg (fun hg => ht0 hg.1)]
    have hg0 : UInt256.sgt (UInt256.signextend (UInt256.ofNat 2)
        (memLoad (keyPtr+UInt256.ofNat 96) mem)) (UInt256.ofNat 32767) ≠ ⟨0⟩ := by
      rw [hgt, decide_eq_true (by omega)]; decide
    have rd1 := poolManagerBlocks.poolManager_block_4088_taken
      (by simp only [List.length_cons]; omega) hg0
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_5156 (by simp only [List.length_cons]; omega) rd1

end Benchmarks.UniswapV4PoolManager
