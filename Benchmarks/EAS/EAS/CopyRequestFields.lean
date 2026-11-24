import Benchmarks.EAS.EAS.CalldataAddress
import Benchmarks.EAS.EAS.WordSequence
import Benchmarks.EAS.EAS.Storage
import Benchmarks.EAS.EAS.RuntimeBlocks_021

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def requestCopyWord (cd : ByteArray) (src : UInt256) (off : Nat) : UInt256 :=
  calldataWord cd (src+UInt256.ofNat off).toNat

def requestCopyFieldsValid (cd : ByteArray) (src : UInt256) : Prop :=
  (calldataWord cd src.toNat).toNat < EVM.addressModulus ∧
  requestCopyWord cd src 32 = UInt256.land (requestCopyWord cd src 32) easUint64Mask ∧
  requestCopyWord cd src 64 = UInt256.isZero (UInt256.isZero (requestCopyWord cd src 64)) ∧
  (requestCopyWord cd src 128).toNat ≤ 2^64-1
instance (cd : ByteArray) (src : UInt256) : Decidable (requestCopyFieldsValid cd src) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def requestCopyFieldsMemory (mem cd : ByteArray) (heap src : UInt256) : ByteArray :=
  writeWordSequence mem heap.toNat [calldataWord cd src.toNat,requestCopyWord cd src 32,
    requestCopyWord cd src 64,requestCopyWord cd src 96]

theorem easCopyRequestFields {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src heap stop ret : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+11 ≤ 1024) (hh : heap.toNat ≤ 2^64-1)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5369⟩ (stop::heap::ret::src::R) mem aw rdata σ k C) :
    if requestCopyFieldsValid ee.calldata src then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨5459⟩
        (requestCopyWord ee.calldata src 128::src::stop::heap::ret::heap::R)
        (requestCopyFieldsMemory mem ee.calldata heap src) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5369_packed (immWords := wordsOf (immStore v)) (by omega)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  have haddr := easCalldataAddress v (by simp only [List.length_cons]; omega)
    (by rw [easPatchedValidJumps v]; jump_dest) r1
  by_cases ha : (calldataWord ee.calldata src.toNat).toNat < EVM.addressModulus
  · rw [if_pos ha] at haddr
    obtain ⟨a2,k2,C2,r2⟩ := haddr
    by_cases he : requestCopyWord ee.calldata src 32 = UInt256.land (requestCopyWord ee.calldata src 32) easUint64Mask
    · obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_5380_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (u256_sub_eq_zero_iff_eq.mpr he) r2
      by_cases hb : requestCopyWord ee.calldata src 64 = UInt256.isZero (UInt256.isZero (requestCopyWord ee.calldata src 64))
      · obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_5405_fallthrough_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (u256_sub_eq_zero_iff_eq.mpr hb) r3
        by_cases ho : (requestCopyWord ee.calldata src 128).toNat ≤ 2^64-1
        · rw [if_pos ⟨ha,he,hb,ho⟩]
          obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_5424_fallthrough_packed (immWords := wordsOf (immStore v))
            (by simp only [List.length_cons]; omega) (ugt_zero ho) r4
          have hn (n : Nat) (hb : n ≤ 96) : (heap+UInt256.ofNat n).toNat = heap.toNat+n :=
            uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
          refine ⟨a5,k5,C5,?_⟩
          simpa only [easBlocks.eas_block_5424_fallthrough_stack,easBlocks.eas_block_5424_fallthrough_memory,
            easBlocks.eas_block_5405_fallthrough_memory,easBlocks.eas_block_5380_fallthrough_memory,
            requestCopyFieldsMemory,writeWordSequence,requestCopyWord,Reasoning.Theory.writeWord,
            hn 32 (by decide),hn 64 (by decide),hn 96 (by decide),Nat.add_assoc,Nat.reduceAdd] using r5
        · rw [if_neg (fun h => ho h.2.2.2)]
          obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_5424_taken_packed (immWords := wordsOf (immStore v))
            (by simp only [List.length_cons]; omega) (by rw [ugt_one (by change 18446744073709551615 < (requestCopyWord ee.calldata src 128).toNat; omega)]; decide)
            (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r4
          exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp only [easBlocks.eas_block_5424_taken_stack,List.length_cons]; omega) r5
      · rw [if_neg (fun h => hb h.2.2.1)]
        obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_5405_taken_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (u256_sub_ne_zero_of_ne hb)
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
        exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp only [easBlocks.eas_block_5405_taken_stack,List.length_cons]; omega) r4
    · rw [if_neg (fun h => he h.2.1)]
      obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_5380_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (u256_sub_ne_zero_of_ne he)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
      exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp only [easBlocks.eas_block_5380_taken_stack,List.length_cons]; omega) r3
  · rw [if_neg ha] at haddr
    rw [if_neg (fun h => ha h.1)]
    exact haddr

end Benchmarks.EAS.EAS
