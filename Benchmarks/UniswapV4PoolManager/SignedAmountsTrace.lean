import Benchmarks.UniswapV4PoolManager.SignedAmountsSource
import Benchmarks.UniswapV4PoolManager.SignedAmount0Trace
import Benchmarks.UniswapV4PoolManager.SignedAmount1Trace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem signedAmountTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b ret : UInt256} {delta : Int}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (one : Bool) (v : PoolManagerImmutables) (hstack : R.length+17 ≤ 1024)
    (ha : a.toNat < 2^160) (hb : b.toNat < 2^160)
    (hdlo : -(2^127 : Int) ≤ delta) (hdhi : delta < 2^127)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 (if one then ⟨17610⟩ else ⟨17703⟩)
      (a :: b :: EVM.wordOfInt delta :: ret :: R) mem aw rdata σ k C) :
    if signedAmountFits one a b delta then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (signedAmountWord one a b delta :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  cases one with
  | false => exact signedAmount0Trace v hstack ha hb hdlo hdhi hret h
  | true => exact signedAmount1Trace v (by omega) ha hb hdlo hdhi hret h

end Benchmarks.UniswapV4PoolManager
