import Benchmarks.UniswapV4PoolManager.BalanceDeltaCombineWords
import Benchmarks.UniswapV4PoolManager.SafeCast128Trace
import Benchmarks.UniswapV4PoolManager.FunctionResultTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_018

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

/-- Both checked components are available before the compiler combines packing with the event block. -/
theorem balanceDeltaAddTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw a b j0 j1 j2 x4 x5 : UInt256} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨6046⟩ (j0 :: j1 :: j2 :: a :: x4 :: x5 :: b :: R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0 (fun post values => post = evm ∧
      values = some [.int (EVM.signed (balanceDeltaCombineWord false a b))] ∧ ∃ k' C',
        RD (deployedRuntime v) I g s0 ⟨6084⟩
          (EVM.wordOfInt (balanceDeltaCombineAmount false true a b) ::
            EVM.wordOfInt (balanceDeltaCombineAmount false false a b) :: x4 :: x5 :: b :: R)
          mem aw rdata post.accountMap k' C')
      (balanceDeltaCombineResult f evm false a b) := by
  have rd1 := poolManagerBlocks.poolManager_block_6046 hstack
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  have hc0 := signedToInt128Trace (ret := ⟨6069⟩) (R := ⟨6084⟩ :: a :: x4 :: x5 :: b :: R)
    (n := balanceDeltaCombineAmount false false a b) v (by simp only [List.length_cons]; omega)
    (balanceDeltaCombineAmount_int256 false false a b) (by rw [deployedRuntime_jumps]; jump_dest)
    (by rw [balanceDeltaCombineAmount0_word]; exact rd1)
  by_cases h0 : signedFits ⟨128, by decide⟩ (balanceDeltaCombineAmount false false a b)
  · rw [if_pos h0] at hc0
    obtain ⟨k2, C2, rd2⟩ := hc0
    have rd3 := poolManagerBlocks.poolManager_block_6069 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    have hc1 := signedToInt128Trace (ret := ⟨6084⟩) (R := EVM.wordOfInt (balanceDeltaCombineAmount false false a b) :: x4 :: x5 :: b :: R)
      (n := balanceDeltaCombineAmount false true a b) v (by simp only [List.length_cons]; omega)
      (balanceDeltaCombineAmount_int256 false true a b) (by rw [deployedRuntime_jumps]; jump_dest)
      (by rw [balanceDeltaCombineAmount1_word]; exact rd3)
    by_cases h1 : signedFits ⟨128, by decide⟩ (balanceDeltaCombineAmount false true a b)
    · rw [if_pos h1] at hc1
      rw [balanceDeltaCombineResult, if_pos (show balanceDeltaCombineFits false a b from ⟨h0, h1⟩)]
      exact ⟨rfl, rfl, hc1⟩
    · rw [balanceDeltaCombineResult, if_neg (show ¬balanceDeltaCombineFits false a b from fun hh => h1 hh.2)]
      rw [if_neg h1] at hc1
      exact hc1
  · rw [balanceDeltaCombineResult, if_neg (show ¬balanceDeltaCombineFits false a b from fun hh => h0 hh.1)]
    rw [if_neg h0] at hc0
    exact hc0

end Benchmarks.UniswapV4PoolManager
