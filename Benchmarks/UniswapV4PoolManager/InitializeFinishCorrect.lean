import Benchmarks.UniswapV4PoolManager.InitializeFinishSource
import Benchmarks.UniswapV4PoolManager.AfterInitializeHookTrace
import Benchmarks.UniswapV4PoolManager.SignedResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem initializeFinishTrace {I : ExecutionEnv} {g : Sat256} {s0 evm evm' : State}
    {f : Frame} {key : PoolKeyWords} {price tick : UInt256} {z : Bool} {out : ByteArray}
    (v : PoolManagerImmutables) (hI : evm.executionEnv = I) (ht : int24Canonical tick)
    (hr : afterInitializeTraceResult v I g s0 evm evm' key price tick
      (AccountAddress.ofNat key.hooks.toNat) z out) :
    signedResultTrace ⟨24, by decide⟩ (deployedRuntime v) g s0
      (initializeFinishResult f evm evm' key price tick z out) := by
  unfold initializeFinishResult
  rw [hI]
  unfold afterInitializeTraceResult at hr
  split_ifs at hr ⊢
  · exact ⟨tick, rfl, int24Canonical_signed_bounds ht, hr⟩
  · exact hr
  · exact ⟨tick, rfl, int24Canonical_signed_bounds ht, hr⟩

end Benchmarks.UniswapV4PoolManager
