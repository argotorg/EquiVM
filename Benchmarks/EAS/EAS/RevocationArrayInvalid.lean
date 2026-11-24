import Benchmarks.EAS.EAS.CopyRevocationArrayRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easCopyRevocationArrayInvalid {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {header heap ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+12 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hd : decodeRevocationArray ee.calldata header = none)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5924⟩
      ((header+UInt256.ofNat 32)::calldataWord ee.calldata header.toNat::UInt256.ofNat ee.calldata.size::ret::R)
      mem aw rdata σ k C) : RDrev fork (deployedRuntime v) g s0 := by
  by_cases hl : (calldataWord ee.calldata header.toNat).toNat ≤ 2^64-1
  · apply easCopyRevocationArrayReject v hstack hfree hl ?_ rd
    intro he
    have hv : revocationArrayHeaderValid ee.calldata header := ⟨hl,he⟩
    simp only [decodeRevocationArray,if_pos hv] at hd
    contradiction
  · obtain ⟨a1,j1,D1,r1⟩ := easBlocks.eas_block_5924_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hs := easArrayAllocationSize v (by simp only [easBlocks.eas_block_5924_stack,List.length_cons]; omega)
      (by rw [easPatchedValidJumps v]; jump_dest) r1
    simpa only [if_neg hl] using hs

end Benchmarks.EAS.EAS
