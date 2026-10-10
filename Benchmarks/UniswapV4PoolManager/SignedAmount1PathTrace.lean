import Benchmarks.UniswapV4PoolManager.Amount1Trace
import Benchmarks.UniswapV4PoolManager.CheckedAmountPathTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem signedAmount1PathTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b liquidity ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024) (roundUp : Bool)
    (ha : a.toNat < 2^160) (hb : b.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 (if roundUp then ⟨23010⟩ else ⟨23101⟩)
      (a :: b :: liquidity :: (if roundUp then ⟨17691⟩ else ⟨17653⟩) :: ret :: R) mem aw rdata σ k C) :
    if amount1Fits a b liquidity ∧ (amount1Word a b liquidity roundUp).toNat < 2^255 then
      ∃ k' C', RD (deployedRuntime v) I g s0 ret
        (checkedAmountReturnWord (amount1Word a b liquidity roundUp) roundUp :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hcalc := amount1Trace (roundUp := roundUp) v (by change R.length+1+14 ≤ 1024; omega) ha hb hl
    (by cases roundUp <;> rw [poolManagerPatchedValidJumps v] <;> jump_dest) h
  exact checkedAmountPathTrace v (by omega) roundUp hret hcalc

end Benchmarks.UniswapV4PoolManager
