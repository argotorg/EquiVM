import Benchmarks.UniswapV4PoolManager.PositionLiquidityTrace
import Benchmarks.UniswapV4PoolManager.PositionFeesTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem positionUpdateTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id key fee0 upper x0 x1 x2 x3 x4 x5 lower x9 fee1 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256} (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+31 ≤ 1024)
    (hI : evm.executionEnv = I) (hlo : -(2^127 : Int) ≤ delta) (hhi : delta < 2^127)
    (h : RD (deployedRuntime v) I g s0 ⟨5915⟩
      (positionUpdateInputStack evm id key delta fee0 upper x0 x1 x2 x3 x4 x5 lower x9 fee1 R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (positionUpdateReturnTrace v I g s0 evm.σ₀ mem rdata aw ⟨5993⟩ ⟨5999⟩
        (positionUpdateContinuation delta upper x0 x1 x2 x3 x4 x5 lower x9 R))
      (positionUpdateResult f evm id key delta fee0 fee1) := by
  have hr := positionLiquidityTrace v (by omega) hI hlo hhi h
  simp only [positionUpdateResult]
  by_cases he : positionChangeReverts (positionLiquidityWord evm id key) delta
  · rw [if_pos he] at hr ⊢
    exact hr
  · rw [if_neg he] at hr ⊢
    by_cases hp : delta ≠ 0 ∧ evm.executionEnv.perm = false
    · rw [if_pos hp] at hr ⊢
      exact hr
    · rw [if_neg hp] at hr ⊢
      obtain ⟨k1, C1, rd1⟩ := hr
      have hfees := positionFeesTrace f v (by change R.length+13+18 ≤ 1024; omega)
        ((positionChangeState_env _ _ _ _ _).trans hI) rd1
      simpa only [positionChangeState_original] using hfees

end Benchmarks.UniswapV4PoolManager
