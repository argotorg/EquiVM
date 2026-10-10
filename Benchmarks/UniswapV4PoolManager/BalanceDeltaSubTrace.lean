import Benchmarks.UniswapV4PoolManager.BalanceDeltaCombineWords
import Benchmarks.UniswapV4PoolManager.SafeCast128Trace
import Benchmarks.UniswapV4PoolManager.FunctionResultTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_051

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem balanceDeltaSubTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw a b ret : UInt256} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+8 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨17855⟩ (a :: b :: ret :: R) mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0 (fun post values => post = evm ∧
      values = some [.int (EVM.signed (balanceDeltaCombineWord true a b))] ∧ ∃ k' C',
        RD (deployedRuntime v) I g s0 ret (balanceDeltaCombineWord true a b :: R)
          mem aw rdata post.accountMap k' C')
      (balanceDeltaCombineResult f evm true a b) := by
  have rd1 := poolManagerBlocks.poolManager_block_17855 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  have hc0 := signedToInt128Trace (ret := ⟨17876⟩) (R := a :: ⟨17890⟩ :: b :: ret :: R)
    (n := balanceDeltaCombineAmount true false a b) v (by simp only [List.length_cons]; omega)
    (balanceDeltaCombineAmount_int256 true false a b) (by rw [deployedRuntime_jumps]; jump_dest)
    (by rw [balanceDeltaCombineAmount0_word]; exact rd1)
  by_cases h0 : signedFits ⟨128, by decide⟩ (balanceDeltaCombineAmount true false a b)
  · rw [if_pos h0] at hc0
    obtain ⟨k2, C2, rd2⟩ := hc0
    have rd3 := poolManagerBlocks.poolManager_block_17876 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    have hc1 := signedToInt128Trace (ret := ⟨17890⟩) (R := EVM.wordOfInt (balanceDeltaCombineAmount true false a b) :: ret :: R)
      (n := balanceDeltaCombineAmount true true a b) v (by simp only [List.length_cons]; omega)
      (balanceDeltaCombineAmount_int256 true true a b) (by rw [deployedRuntime_jumps]; jump_dest)
      (by rw [balanceDeltaCombineAmount1_word]; exact rd3)
    by_cases h1 : signedFits ⟨128, by decide⟩ (balanceDeltaCombineAmount true true a b)
    · rw [if_pos h1] at hc1
      obtain ⟨k4, C4, rd4⟩ := hc1
      have rd5 := poolManagerBlocks.poolManager_block_17890 (by omega) hret rd4
      rw [balanceDeltaCombineResult, if_pos (show balanceDeltaCombineFits true a b from ⟨h0, h1⟩)]
      exact ⟨rfl, rfl, _, _, rd5⟩
    · rw [balanceDeltaCombineResult, if_neg (show ¬balanceDeltaCombineFits true a b from fun hh => h1 hh.2)]
      rw [if_neg h1] at hc1
      exact hc1
  · rw [balanceDeltaCombineResult, if_neg (show ¬balanceDeltaCombineFits true a b from fun hh => h0 hh.1)]
    rw [if_neg h0] at hc0
    exact hc0

end Benchmarks.UniswapV4PoolManager
