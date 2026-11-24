import Benchmarks.EAS.EAS.DelegatedAttestBuildRun
import Benchmarks.EAS.EAS.DelegatedAttestationFacts
import Benchmarks.EAS.EAS.RuntimeBlocks_011

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedAttestVerifyTail (cd : ByteArray) (root offset base n len available groups total i last : UInt256)
    (R : List UInt256) : List UInt256 :=
  [base,n,len,available,groups,total,i,root+UInt256.ofNat 64,root+UInt256.ofNat 96,offset,root,last,calldataWord cd root.toNat]++R

def multiDelegatedAttestVerifyStack (cd : ByteArray) (j : Nat) (root offset base n len available groups total i last : UInt256)
    (R : List UInt256) : List UInt256 := UInt256.ofNat j::multiDelegatedAttestVerifyTail cd root offset base n len available groups total i last R

theorem easMultiDelegatedAttestVerifyAccess {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C j : Nat}
    {root offset base n len available groups total i last : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+33≤1024)
    (hj : j<len.toNat) (hslot : offset.toNat+32*j<UInt256.size)
    (hs : signatureArrayReferenceAccessValid ee.calldata root)
    (hjs : j<(calldataWord ee.calldata (delegatedBatchArray ee.calldata root 64).toNat).toNat)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨2874⟩
      (multiDelegatedAttestVerifyStack ee.calldata j root offset base n len available groups total i last R) mem aw rdata σ k C) :
    if requestReferenceValid ee.calldata offset (UInt256.ofNat (offset.toNat+32*j)) then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨6240⟩
        (delegatedAttestBuildStack (calldataWord ee.calldata root.toNat) (requestArrayElement ee.calldata offset j)
          (delegatedBatchArray ee.calldata root 64+UInt256.ofNat 32) (root+UInt256.ofNat 96) ⟨3025⟩ (UInt256.ofNat j)
          (multiDelegatedAttestVerifyTail ee.calldata root offset base n len available groups total i last R)) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  simp only [multiDelegatedAttestVerifyStack,multiDelegatedAttestVerifyTail,List.cons_append,List.nil_append] at rd
  have hjb : j<UInt256.size := by have := len.val.isLt;omega
  have hshift : offset+UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 5)=UInt256.ofNat (offset.toNat+32*j) := by
    rw [show UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 5)=UInt256.ofNat (32*j) from shiftLeft5_ofNat_eq (by omega)]
    apply u256_inj
    rw [uadd_word_ofNat_toNat _ _ hslot,ulit_toNat' _ hslot]
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_2874_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons];omega) (by rw [ult_one (by rw [ulit_toNat' _ hjb];exact hj)];rfl) rd
  obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_2883_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons];omega) (by rw [easPatchedValidJumpsRuntime v];jump_dest) r1
  simp only [easBlocks.eas_block_2883_stack,hshift] at r2
  have href := easRequestReference v (by simp only [List.length_cons];omega) (by rw [easPatchedValidJumps v];jump_dest) r2
  by_cases hr : requestReferenceValid ee.calldata offset (UInt256.ofNat (offset.toNat+32*j))
  · rw [if_pos hr] at href ⊢
    obtain ⟨a3,k3,C3,r3⟩ := href
    simp only [ulit_toNat' _ hslot] at r3
    obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_2906_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons];omega) (by rw [easPatchedValidJumpsRuntime v];jump_dest) r3
    simp only [easBlocks.eas_block_2906_stack] at r4
    obtain ⟨a5,k5,C5,r5⟩ := (easSignatureArrayReferenceAccess v (by simp only [List.length_cons];omega)
      (by rw [easPatchedValidJumps v];jump_dest) r4).1 hs
    obtain ⟨a6,k6,C6,r6⟩ := easBlocks.eas_block_2912_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons];omega) (by rw [ult_one (by rw [ulit_toNat' _ hjb];exact hjs)];rfl) r5
    simp only [easBlocks.eas_block_2912_fallthrough_stack] at r6
    obtain ⟨a7,k7,C7,r7⟩ := easBlocks.eas_block_2923_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [easPatchedValidJumpsRuntime v];jump_dest) r6
    exact ⟨a7,k7,C7,r7⟩
  · rw [if_neg hr] at href ⊢
    exact href

end Benchmarks.EAS.EAS
