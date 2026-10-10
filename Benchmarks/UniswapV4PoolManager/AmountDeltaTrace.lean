import Benchmarks.UniswapV4PoolManager.SwapStepDeltaWords
import Benchmarks.UniswapV4PoolManager.Amount0Trace
import Benchmarks.UniswapV4PoolManager.Amount1Trace
import Benchmarks.UniswapV4PoolManager.ReachCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def amountDeltaPC (use0 roundUp : Bool) : UInt256 :=
  if use0 then (if roundUp then ⟨23165⟩ else ⟨23348⟩)
  else (if roundUp then ⟨23010⟩ else ⟨23101⟩)

theorem amountDeltaCostTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b liquidity ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (use0 roundUp : Bool) (hstack : R.length+16 ≤ 1024)
    (ha : a.toNat < 2^160) (hb : b.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 (amountDeltaPC use0 roundUp)
      (a :: b :: liquidity :: ret :: R) mem aw rdata σ k C) :
    if amountDeltaFits a b liquidity use0 roundUp then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ret (amountDeltaWord a b liquidity use0 roundUp :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have run : ∀ {budget : Sat256} {start : State} {ki Ci : Nat},
      RD (deployedRuntime v) I budget start (amountDeltaPC use0 roundUp)
      (a :: b :: liquidity :: ret :: R) mem aw rdata σ ki Ci →
      if amountDeltaFits a b liquidity use0 roundUp then ∃ k' C',
        RD (deployedRuntime v) I budget start ret (amountDeltaWord a b liquidity use0 roundUp :: R) mem aw rdata σ k' C'
      else RDrev (deployedRuntime v) budget start := by
    intro budget start ki Ci hin
    cases use0 with
    | false => exact amount1Trace v (by omega) ha hb hl hret hin
    | true =>
      cases roundUp with
      | false => exact amount0DownTrace v (by omega) ha hb hl hret hin
      | true => exact amount0UpTrace v hstack ha hb hl hret hin
  by_cases hf : amountDeltaFits a b liquidity use0 roundUp
  · rw [if_pos hf]
    exact RD_retainCost (fun _ _ hin => by simpa only [if_pos hf] using run hin) h
  · rw [if_neg hf]
    simpa only [if_neg hf] using run h

end Benchmarks.UniswapV4PoolManager
