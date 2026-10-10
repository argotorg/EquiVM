import Benchmarks.UniswapV4PoolManager.BeforeLiquidityMemory
import Benchmarks.UniswapV4PoolManager.WordBytesCallAllocationGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem beforeLiquidityAllocationGas {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {pc aw ptr len : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hgas : g.toNat < 324518553658429321982441292826060)
    (hf : ptr.toNat+len.toNat+512 < UInt256.size)
    (hbad : ¬AllocationBounds ptr (beforeLiquidityAllocationSize len))
    (hpaid : Cₘ aw ≤ C) (hspan : (ptr.toNat+len.toNat+483)/32 ≤ aw.toNat)
    (h : RD (deployedRuntime v) I g s0 pc R mem aw rdata σ k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass := by
  apply wordBytesCallAllocationGas (words := List.replicate 11 ⟨0⟩) v hgas
    (by simp only [List.length_replicate]; omega) hbad hpaid ?_ h
  simpa only [List.length_replicate, show ptr.toNat+131+32*11+len.toNat = ptr.toNat+len.toNat+483 by omega] using hspan

end Benchmarks.UniswapV4PoolManager
