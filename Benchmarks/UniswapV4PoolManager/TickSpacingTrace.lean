import Benchmarks.UniswapV4PoolManager.TickSpacingArithmetic
import Benchmarks.UniswapV4PoolManager.SignedModStep
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_021
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_022

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

open poolManagerBlocks in
/-- Compute the inlined spacing limit and execute the first gross-liquidity check. -/
theorem tickSpacingLimitTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw spacing gross x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨7400⟩
      (EVM.wordOfInt (-887272) :: spacing :: ⟨0⟩ :: spacing :: ⟨1⟩ :: ⟨2^128-1⟩ :: gross ::
        x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C) :
    if tickSpacingLimit (EVM.signed spacing) < Int.ofNat gross.toNat then RDrev (deployedRuntime v) g s0
    else ∃ k' C', RD (deployedRuntime v) I g s0 ⟨7456⟩
      (tickSpacingWordLimit spacing :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)
      mem aw rdata σ k' C' := by
  have rd1 := rdSmod h
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨7400⟩ : UInt256), UInt8.ofNat 7,
      .SMOD, none, immutableLayout_inBounds, immutableTemplate_size64))
    (by simp only [List.length_cons]; omega)
  have hval := tickSpacingWordLimit_value spacing
  have hcompiled : UInt256.land (UInt256.div ⟨2^128-1⟩
      (UInt256.sub (UInt256.sdiv (UInt256.ofNat 887272) spacing)
        (UInt256.sub (UInt256.sdiv (UInt256.ofNat
          115792089237316195423570985008687907853269984665640564039457584007913128752664) spacing)
          (UInt256.slt (UInt256.smod (EVM.wordOfInt (-887272)) spacing) ⟨0⟩)) + ⟨1⟩))
      ⟨2^128-1⟩ = tickSpacingWordLimit spacing := rfl
  by_cases hg : tickSpacingLimit (EVM.signed spacing) < Int.ofNat gross.toNat
  · rw [if_pos hg]
    have hb : (tickSpacingWordLimit spacing).toNat < gross.toNat := by
      rw [← hval] at hg
      exact Int.ofNat_lt.mp hg
    have rd2 := poolManagerBlocks.poolManager_block_7401_taken
      (by simp only [List.length_cons]; omega)
      (by rw [hcompiled, ugt_one hb]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact poolManagerBlocks.poolManager_block_7528 (by omega) rd2
  · rw [if_neg hg]
    have hb : gross.toNat ≤ (tickSpacingWordLimit spacing).toNat := by
      rw [← hval] at hg
      simp only [Int.ofNat_eq_natCast] at hg
      omega
    have rd2 := poolManagerBlocks.poolManager_block_7401_fallthrough
      (by simp only [List.length_cons]; omega) (by rw [hcompiled, ugt_zero hb]; rfl) rd1
    simpa only [poolManagerBlocks.poolManager_block_7401_fallthrough_stack, hcompiled] using RD.pack rd2

/-- The second gross-liquidity check consumes the same computed limit. -/
theorem tickSpacingUpperGuardExactTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw spacing gross x0 x1 x2 ptr x4 x5 x6 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+11 ≤ 1024)
    (hm : memLoad (ptr+UInt256.ofNat 96) mem = gross) (hgross : gross.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 ⟨7456⟩
      (tickSpacingWordLimit spacing :: x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: R)
      mem aw rdata σ k C) :
    if tickSpacingLimit (EVM.signed spacing) < Int.ofNat gross.toNat then RDrev (deployedRuntime v) g s0
    else ∃ k' C', RD (deployedRuntime v) I g s0 ⟨7256⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: R) mem (M aw (ptr+UInt256.ofNat 96) ⟨32⟩) rdata σ k' C' := by
  have hclean : UInt256.land gross (UInt256.ofNat 340282366920938463463374607431768211455) = gross :=
    u256LandMaskCleanOfToNat _ _ rfl hgross
  have hval := tickSpacingWordLimit_value spacing
  by_cases hg : tickSpacingLimit (EVM.signed spacing) < Int.ofNat gross.toNat
  · rw [if_pos hg]
    have hb : (tickSpacingWordLimit spacing).toNat < gross.toNat := by
      rw [← hval] at hg
      exact Int.ofNat_lt.mp hg
    have rd1 := poolManagerBlocks.poolManager_block_7456_fallthrough
      (by simp only [List.length_cons]; omega) (by rw [hm, hclean, ugt_one hb]; rfl) h
    exact poolManagerBlocks.poolManager_block_7485 (by omega) rd1
  · rw [if_neg hg]
    have hb : gross.toNat ≤ (tickSpacingWordLimit spacing).toNat := by
      rw [← hval] at hg
      simp only [Int.ofNat_eq_natCast] at hg
      omega
    have rd1 := poolManagerBlocks.poolManager_block_7456_taken
      (by simp only [List.length_cons]; omega) (by rw [hm, hclean, ugt_zero hb]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact ⟨_, _, rd1⟩

theorem tickSpacingUpperGuardTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw spacing gross x0 x1 x2 ptr x4 x5 x6 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+11 ≤ 1024)
    (hm : memLoad (ptr+UInt256.ofNat 96) mem = gross) (hgross : gross.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 ⟨7456⟩
      (tickSpacingWordLimit spacing :: x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: R)
      mem aw rdata σ k C) :
    if tickSpacingLimit (EVM.signed spacing) < Int.ofNat gross.toNat then RDrev (deployedRuntime v) g s0
    else ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨7256⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: R) mem aw' rdata σ k' C' := by
  have hr := tickSpacingUpperGuardExactTrace v hstack hm hgross h
  split_ifs at hr ⊢
  · exact hr
  · obtain ⟨k', C', rd⟩ := hr
    exact ⟨_, k', C', rd⟩

end Benchmarks.UniswapV4PoolManager
