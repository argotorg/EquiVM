import Benchmarks.EAS.EAS.WordCopyLoop

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- The values-array loop uses the shared sequential-copy memory model.
theorem easEncodeValuesLoop {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (src dst len i n : Nat) (hn : i+n=len)
    (hstack : R.length+7 ≤ 1024)
    (hsrc : src+32*len < UInt256.size) (hdst : dst+32*len < UInt256.size)
    (hlen : len < UInt256.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨14327⟩
      (UInt256.ofNat i::UInt256.ofNat len::UInt256.ofNat (src+32*i)::UInt256.ofNat (dst+32*i)::ret::R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (UInt256.ofNat (dst+32*len)::R)
      (easCopyWords (UInt256.ofNat src) (UInt256.ofNat dst) mem (32*i) n) aw' rdata σ k' C' := by
  exact easEncodeWordLoop v .resolver src dst len i n hn hstack hsrc hdst hlen hvalid rd


theorem easEncodeValues {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {src dst ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (words : List UInt256) (hstack : R.length+7 ≤ 1024)
    (hlo : 96 ≤ src.toNat) (hdisj : src.toNat+32*words.length ≤ dst.toNat)
    (hin : src.toNat+32*words.length ≤ mem.size)
    (hbound : dst.toNat+32*words.length < UInt256.size)
    (hwords : memoryWords mem src.toNat words.length = words)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨14327⟩
      (⟨0⟩::UInt256.ofNat words.length::src::dst::ret::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (UInt256.ofNat (dst.toNat+32*words.length)::R)
      (writeWordSequence mem dst.toNat words) aw' rdata σ k' C' := by
  exact easEncodeWordValues v .resolver words hstack hlo hdisj hin hbound hwords hvalid rd

end Benchmarks.EAS.EAS
