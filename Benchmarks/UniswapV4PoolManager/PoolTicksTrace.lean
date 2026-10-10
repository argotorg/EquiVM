import Benchmarks.UniswapV4PoolManager.PoolTicksSource
import Benchmarks.UniswapV4PoolManager.SignedComparison
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_017
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_022

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

/-- The inlined tick-range check also finishes constructing the modification parameters. -/
theorem poolTicksCostTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x0 x1 x2 x3 x4 x5 x6 upper delta lower x10 ptr : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨5584⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: upper :: delta :: lower :: x10 :: ptr :: R)
      mem aw rdata σ k C) :
    if poolTicksValid lower upper then ∃ aw' k' C', Cₘ aw'+C ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ⟨5680⟩
      (x4 :: x3 :: ⟨0⟩ :: x5 :: x6 :: upper :: delta :: lower :: x10 :: ptr :: R)
      (poolManagerBlocks.poolManager_block_5584_fallthrough_memory (ee := I) (mem := mem)
        (x0 := x0) (x1 := x1) (x2 := x2) (x7 := upper) (x8 := delta) (x9 := lower) (x11 := ptr))
      aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hmin : EVM.signed (UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913128752664) = -887272 := by native_decide
  have hmax : EVM.signed (UInt256.ofNat 887272) = 887272 := rfl
  by_cases h0 : EVM.signed lower < EVM.signed upper
  · have hg0 : UInt256.isZero (UInt256.slt lower upper) = ⟨0⟩ := by
      rw [slt_signed, decide_eq_true h0]; rfl
    have rd1 := poolManagerBlocks.poolManager_block_5584_fallthrough (by omega) hg0 h
    simp only [poolManagerBlocks.poolManager_block_5584_fallthrough_stack] at rd1
    by_cases h1 : -887272 ≤ EVM.signed lower
    · have hg1 : UInt256.slt lower (UInt256.ofNat
          115792089237316195423570985008687907853269984665640564039457584007913128752664) = ⟨0⟩ := by
        rw [slt_signed, hmin, decide_eq_false (by omega)]; rfl
      have rd2 := poolManagerBlocks.poolManager_block_5631_fallthrough
        (by simp only [List.length_cons]; omega) hg1 rd1
      by_cases h2 : EVM.signed upper ≤ 887272
      · rw [if_pos ⟨h0, h1, h2⟩]
        have hg2 : UInt256.sgt upper (UInt256.ofNat 887272) = ⟨0⟩ := by
          rw [sgt_signed, hmax, decide_eq_false (by omega)]; rfl
        have rd3 := poolManagerBlocks.poolManager_block_5670_fallthrough
          (by simp only [List.length_cons]; omega) hg2 rd2
        refine ⟨_, _, _, ?_, rd3⟩
        dsimp only [memExpansionCost]
        omega
      · rw [if_neg (fun hh => h2 hh.2.2)]
        have hg2 : UInt256.sgt upper (UInt256.ofNat 887272) ≠ ⟨0⟩ := by
          rw [sgt_signed, hmax, decide_eq_true (by omega)]; decide
        have rd3 := poolManagerBlocks.poolManager_block_5670_taken
          (by simp only [List.length_cons]; omega) hg2
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
        exact poolManagerBlocks.poolManager_block_7714 (by simp only [List.length_cons]; omega) rd3
    · rw [if_neg (fun hh => h1 hh.2.1)]
      have hg1 : UInt256.slt lower (UInt256.ofNat
          115792089237316195423570985008687907853269984665640564039457584007913128752664) ≠ ⟨0⟩ := by
        rw [slt_signed, hmin, decide_eq_true (by omega)]; decide
      have rd2 := poolManagerBlocks.poolManager_block_5631_taken
        (by simp only [List.length_cons]; omega) hg1
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact poolManagerBlocks.poolManager_block_7758 (by simp only [List.length_cons]; omega) rd2
  · rw [if_neg (fun hh => h0 hh.1)]
    have hg0 : UInt256.isZero (UInt256.slt lower upper) ≠ ⟨0⟩ := by
      rw [slt_signed, decide_eq_false h0]; decide
    have rd1 := poolManagerBlocks.poolManager_block_5584_taken (by omega) hg0
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_7802 (by simp only [List.length_cons]; omega) rd1

theorem poolTicksTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x0 x1 x2 x3 x4 x5 x6 upper delta lower x10 ptr : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨5584⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: upper :: delta :: lower :: x10 :: ptr :: R)
      mem aw rdata σ k C) :
    if poolTicksValid lower upper then ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨5680⟩
      (x4 :: x3 :: ⟨0⟩ :: x5 :: x6 :: upper :: delta :: lower :: x10 :: ptr :: R)
      (poolManagerBlocks.poolManager_block_5584_fallthrough_memory (ee := I) (mem := mem)
        (x0 := x0) (x1 := x1) (x2 := x2) (x7 := upper) (x8 := delta) (x9 := lower) (x11 := ptr))
      aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hr := poolTicksCostTrace v hstack h
  split_ifs at hr ⊢
  · obtain ⟨aw', k', C', _, rd⟩ := hr
    exact ⟨aw', k', C', rd⟩
  · exact hr

end Benchmarks.UniswapV4PoolManager
