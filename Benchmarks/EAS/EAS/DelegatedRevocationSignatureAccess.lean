import Benchmarks.EAS.EAS.DelegatedRevocationDecode
import Benchmarks.EAS.EAS.CalldataAddress
import Benchmarks.EAS.EAS.RuntimeBlocks_007
import Benchmarks.EAS.EAS.RuntimeBlocks_008

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedRevocationLinkData (mem : ByteArray) (row data : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord mem (row+UInt256.ofNat 32).toNat data
def delegatedRevocationLinkSignatures (mem : ByteArray) (row signatures : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord mem (row+UInt256.ofNat 64).toNat signatures

theorem easDelegatedRevocationSignatureAccess {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {root row data a b c d : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+12 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1396⟩ (data::d::a::root::b::c::row::R) mem aw rdata σ k C) :
    if delegatedBatchArrayAccess ee.calldata root 64 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨1439⟩
        (b::a::d::(row+UInt256.ofNat 32)::root::delegatedBatchArray ee.calldata root 64::c::row::R)
        (delegatedRevocationLinkData mem row data) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases ho : (calldataWord ee.calldata (root+UInt256.ofNat 64).toNat).toNat ≤ 2^64-1
  · obtain ⟨a1,j1,D1,r1⟩ := easBlocks.eas_block_1396_fallthrough_packed (immWords := wordsOf (immStore v))
      (by omega) (ugt_zero ho) rd
    by_cases hr : arrayHeaderReadable ee.calldata (delegatedBatchArray ee.calldata root 64)
    · rw [if_pos (show delegatedBatchArrayAccess ee.calldata root 64 from ⟨ho,hr⟩)]
      obtain ⟨a2,j2,D2,r2⟩ := easBlocks.eas_block_1425_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_1396_fallthrough_stack,List.length_cons]; omega) hr r1
      exact ⟨a2,j2,D2,r2⟩
    · rw [if_neg (fun h => hr h.2)]
      obtain ⟨a2,j2,D2,r2⟩ := easBlocks.eas_block_1425_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_1396_fallthrough_stack,List.length_cons]; omega) hr
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
      exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_1425_taken_stack,List.length_cons]; omega) r2
  · rw [if_neg (fun h => ho h.1)]
    obtain ⟨a1,j1,D1,r1⟩ := easBlocks.eas_block_1396_taken_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [ugt_one (by change 18446744073709551615 < (calldataWord ee.calldata (root+UInt256.ofNat 64).toNat).toNat; omega)]; decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_1396_taken_stack,List.length_cons]; omega) r1

theorem easDelegatedRevocationAddressAccess {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {root row sig dst src a b c d : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+13 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1500⟩
      (dst::src::src::b::a::d::(row+UInt256.ofNat 32)::root::sig::c::row::R) mem aw rdata σ k C) :
    if delegatedBatchAddressClean ee.calldata root then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨1521⟩
        (calldataWord ee.calldata (root+UInt256.ofNat 96).toNat::b::a::d::
          (row+UInt256.ofNat 32)::(row+UInt256.ofNat 64)::sig::c::row::R)
        (delegatedRevocationLinkSignatures mem row sig) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨a1,j1,D1,r1⟩ := easBlocks.eas_block_1500_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  exact easCalldataAddress v (by simp only [easBlocks.eas_block_1500_stack,List.length_cons]; omega)
    (by rw [easPatchedValidJumps v]; jump_dest) r1

end Benchmarks.EAS.EAS
