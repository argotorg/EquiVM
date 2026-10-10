import Benchmarks.UniswapV4PoolManager.AfterSwapPackTrace
import Benchmarks.UniswapV4PoolManager.AfterSwapFinishSource
import Benchmarks.UniswapV4PoolManager.BalanceDeltaSubCostTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000
attribute [local irreducible] afterSwapPackWord balanceDeltaCombineWord balanceDeltaCombineFits

theorem afterSwapFinishActiveTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw ptr delta ret old : UInt256} {specified unspecified : Int}
    {k C : Nat} {R : List UInt256} {p : SwapParamsWords}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hp : MemorySlice mem ptr.toNat (wordBytes (swapParamsWordList p)))
    (hfit : ptr.toNat+96 < UInt256.size) (hn : unspecified ≠ 0 ∨ specified ≠ 0)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15832⟩
      (ptr :: EVM.wordOfInt unspecified :: EVM.wordOfInt specified :: delta :: ret :: old :: R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0 (fun post values => post = evm ∧
      values = some [.int (EVM.signed (balanceDeltaCombineWord true delta
        (afterSwapPackWord (afterSwapSpecifiedFirst p) specified unspecified))),
        .int (EVM.signed (afterSwapPackWord (afterSwapSpecifiedFirst p) specified unspecified))] ∧
      ∃ aw' k' C', C+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ret
        (afterSwapPackWord (afterSwapSpecifiedFirst p) specified unspecified ::
          balanceDeltaCombineWord true delta (afterSwapPackWord (afterSwapSpecifiedFirst p) specified unspecified) :: R)
        mem aw' rdata post.accountMap k' C')
      (afterSwapFinishResult f evm p delta specified unspecified) := by
  obtain ⟨aw1, k1, C1, hcost1, rd1⟩ := afterSwapPackTrace v (by omega) hp hfit h
  have rd2 := poolManager_block_15880 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
  simp only [poolManager_block_15880_stack] at rd2
  have ht := balanceDeltaSubCostTrace f v (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd2
  by_cases hf : balanceDeltaCombineFits true delta (afterSwapPackWord (afterSwapSpecifiedFirst p) specified unspecified)
  · rw [balanceDeltaCombineResult, if_pos hf] at ht
    obtain ⟨_, _, k2, C2, hcost2, rd3⟩ := ht
    have rd4 := poolManager_block_15887 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
    have rd5 := poolManager_block_15825 (by omega) hret rd4
    rw [afterSwapFinishResult, if_pos hn, if_pos hf]
    exact ⟨rfl, rfl, _, _, _, by omega, rd5⟩
  · rw [balanceDeltaCombineResult, if_neg hf] at ht
    rw [afterSwapFinishResult, if_pos hn, if_neg hf]
    exact ht

end Benchmarks.UniswapV4PoolManager
