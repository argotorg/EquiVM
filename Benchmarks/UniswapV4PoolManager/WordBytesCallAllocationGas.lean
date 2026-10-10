import Benchmarks.UniswapV4PoolManager.WordBytesCallAllocation
import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem wordBytesCallAllocationGas {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {pc aw ptr len : UInt256} {σ : AccountMap} {k C : Nat}
    {words R : List UInt256}
    (v : PoolManagerImmutables) (hgas : g.toNat < 324518553658429321982441292826060)
    (hf : ptr.toNat+130+32*words.length+len.toNat < UInt256.size)
    (hbad : ¬AllocationBounds ptr (wordBytesCallAllocationSize words len))
    (hpaid : Cₘ aw ≤ C) (hspan : (ptr.toNat+131+32*words.length+len.toNat)/32 ≤ aw.toNat)
    (h : RD (deployedRuntime v) I g s0 pc R mem aw rdata σ k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass := by
  have he := wordBytesCallAllocation_end_toNat ptr len words hf
  have hl : 2^64 ≤ ptr.toNat+96+32*words.length+paddedSize len.toNat := by
    by_contra hn
    apply hbad
    constructor
    · rw [he]; omega
    · change (allocationEnd ptr (wordBytesCallAllocationSize words len)).toNat ≤ 2^64-1
      rw [he]; omega
  have hp := paddedSize_le_add31 len.toNat
  have hlarge : (UInt256.ofNat (2^59)).toNat ≤ aw.toNat := by
    change 2^59 ≤ aw.toNat
    omega
  have hc := memoryCost_mono hlarge
  have hb : 324518553658429321982441292826060 < Cₘ (UInt256.ofNat (2^59)) := by decide +kernel
  exact RD.oog_of_cost_gt h (by omega)

end Benchmarks.UniswapV4PoolManager
