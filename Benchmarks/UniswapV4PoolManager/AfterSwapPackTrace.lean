import Benchmarks.UniswapV4PoolManager.AfterSwapPackSource
import Benchmarks.UniswapV4PoolManager.SwapParamsEncodeTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_045

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem afterSwapPackGuard (p : SwapParamsWords) :
    UInt256.eq ⟨0⟩ (UInt256.eq (UInt256.isZero (UInt256.isZero (UInt256.fromBool p.zeroForOne)))
      (UInt256.slt p.amountSpecified ⟨0⟩)) = UInt256.fromBool (!afterSwapSpecifiedFirst p) := by
  rw [slt_signed]
  change UInt256.eq ⟨0⟩ (UInt256.eq (UInt256.isZero (UInt256.isZero (UInt256.fromBool p.zeroForOne)))
    (UInt256.fromBool (decide (EVM.signed p.amountSpecified < 0)))) = _
  cases hz : p.zeroForOne <;> by_cases hn : EVM.signed p.amountSpecified < 0 <;>
    simp only [afterSwapSpecifiedFirst, hz, hn, decide_true, decide_false] <;> decide +kernel

theorem afterSwapPackTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr delta ret old : UInt256} {specified unspecified : Int}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {p : SwapParamsWords}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (hp : MemorySlice mem ptr.toNat (wordBytes (swapParamsWordList p)))
    (hfit : ptr.toNat+96 < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨15832⟩
      (ptr :: EVM.wordOfInt unspecified :: EVM.wordOfInt specified :: delta :: ret :: old :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', C+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ⟨15880⟩
      (afterSwapPackWord (afterSwapSpecifiedFirst p) specified unspecified :: UInt256.ofNat 15887 :: ret :: delta :: R)
        mem aw' rdata σ k' C' := by
  have hz : memLoad ptr mem = UInt256.fromBool p.zeroForOne :=
    hp.word_load (i := 0) (word := UInt256.fromBool p.zeroForOne) rfl (by omega)
  have ha : memLoad (ptr+UInt256.ofNat 32) mem = p.amountSpecified :=
    hp.word_load (i := 1) (word := p.amountSpecified) rfl (by rw [uadd_word_ofNat_toNat ptr 32 (by omega)])
  have hg : UInt256.eq ⟨0⟩ (UInt256.eq (UInt256.isZero (UInt256.isZero (memLoad ptr mem)))
      (UInt256.slt (memLoad (ptr+UInt256.ofNat 32) mem) ⟨0⟩)) = UInt256.fromBool (!afterSwapSpecifiedFirst p) := by
    rw [hz, ha]; exact afterSwapPackGuard p
  cases hc : afterSwapSpecifiedFirst p with
  | true =>
    have rd1 := poolManager_block_15832_fallthrough hstack (by rw [hg, hc]; rfl) h
    simp only [poolManager_block_15832_fallthrough_stack] at rd1
    have rd2 := poolManager_block_15857 (by simp only [List.length_cons]; omega) rd1
    simp only [hc, afterSwapPackWord, if_true]
    refine ⟨_, _, _, ?_, rd2⟩
    dsimp only [memExpansionCost]; omega
  | false =>
    have rd1 := poolManager_block_15832_taken hstack (by rw [hg, hc]; decide +kernel)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_15832_taken_stack] at rd1
    have rd2 := poolManager_block_15895 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [hc, afterSwapPackWord, Bool.false_eq_true, if_false]
    refine ⟨_, _, _, ?_, rd2⟩
    dsimp only [memExpansionCost]; omega

end Benchmarks.UniswapV4PoolManager
