import Benchmarks.UniswapV4PoolManager.PoolModifyPositionUpdate
import Benchmarks.UniswapV4PoolManager.PositionUpdateCorrect
import Benchmarks.UniswapV4PoolManager.BlockResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyPositionTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id key fee0 upper x0 x1 x2 ptr x4 x5 lower x9 fee1 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256} (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+31 ≤ 1024)
    (hI : evm.executionEnv = I) (hlo : -(2^127 : Int) ≤ delta) (hhi : delta < 2^127)
    (h : RD (deployedRuntime v) I g s0 ⟨5915⟩
      (positionUpdateInputStack evm id key delta fee0 upper x0 x1 x2 ptr x4 x5 lower x9 fee1 R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post =>
      post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ k' C', RD (deployedRuntime v) I g s0 ⟨12458⟩
        (positionUpdateOwed evm id key delta fee0 false :: ⟨5993⟩ :: ⟨5999⟩ ::
          positionUpdateOwed evm id key delta fee1 true ::
          positionUpdateContinuation delta upper x0 x1 x2 ptr x4 x5 lower x9 R)
        mem aw rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyPositionUpdateResult f evm id key delta fee0 fee1) := by
  have hr := positionUpdateTrace (poolModifyUpdateAliasFrame f id key) v hstack hI hlo hhi h
  apply blockResultTrace_continueCall hr
  intro cf post values hv ht
  obtain ⟨hIpost, hσpost, owed0, owed1, hvalues, k1, C1, rd1⟩ := ht
  rw [positionUpdateReturnedValues hv] at hvalues
  simp only [Option.some.injEq, List.cons.injEq, Value.int.injEq, and_true] at hvalues
  have h0 := congrArg EVM.wordOfInt hvalues.1
  have h1 := congrArg EVM.wordOfInt hvalues.2
  simp only [wordOfInt_ofNat_toNat] at h0 h1
  rw [← h0, ← h1] at rd1
  exact ⟨hIpost, hσpost, k1, C1, rd1⟩

end Benchmarks.UniswapV4PoolManager
