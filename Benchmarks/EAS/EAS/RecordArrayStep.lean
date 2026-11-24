import Benchmarks.EAS.EAS.RecordMemory
import Benchmarks.EAS.EAS.ArrayEncoding

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- GENERALIZES Reasoning.WordArithmetic.lnot_zero_add from one to an arbitrary subtraction literal.
theorem u256_add_complement (word : UInt256) (n : Nat) (hn : 0 < n) (hle : n ≤ word.toNat) :
    word+UInt256.ofNat (UInt256.size-n) = UInt256.ofNat (word.toNat-n) := by
  have hw := word.val.isLt
  change word.toNat < UInt256.size at hw
  apply u256_inj
  rw [uadd_toNat, ulit_toNat' _ (by omega), ulit_toNat' _ (by omega)]
  rw [show word.toNat+(UInt256.size-n) = (word.toNat-n)+UInt256.size by omega,
    Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]

def recordArrayOffsetWord (base tail : UInt256) : UInt256 :=
  UInt256.sub tail base + UInt256.ofNat (UInt256.size-96)

theorem recordArrayOffsetWord_eq (base tail : UInt256) (h : base.toNat+96 ≤ tail.toNat) :
    recordArrayOffsetWord base tail = UInt256.ofNat (tail.toNat-base.toNat-96) := by
  unfold recordArrayOffsetWord
  rw [u256_add_complement _ 96 (by decide) (by rw [usub_toNat (by omega)]; omega), usub_toNat (by omega)]

def recordArrayStepMemory (mem : ByteArray) (head base tail src dataPtr : UInt256) : ByteArray :=
  attestationEncodedMemory (Reasoning.Theory.writeWord mem head.toNat (recordArrayOffsetWord base tail)) src tail dataPtr

theorem easEncodeRecordArrayStep {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {head base tail slot src dataPtr i len : UInt256} {a : AttestationRecord} {R : List UInt256}
    (v : EASImmutables) (limit : Nat) (hstack : R.length+23 ≤ 1024)
    (hi : i.toNat < len.toNat)
    (hview : AttestationMemoryView mem src dataPtr a)
    (hslotLow : 96 ≤ slot.toNat) (hslotIn : slot.toNat+32 ≤ mem.size)
    (hslot : slot.toNat+32 ≤ limit) (hload : memLoad slot mem = src)
    (hsrc : src.toNat+320 ≤ limit) (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ limit)
    (hhead : limit ≤ head.toNat) (htail : head.toNat+32 ≤ tail.toNat)
    (hbound : tail.toNat+384+32*((a.data.size+31)/32) < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨14292⟩ (head::i::len::slot::base::tail::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨14292⟩
      ((head+⟨32⟩)::(i+⟨1⟩)::len::(slot+⟨32⟩)::base::UInt256.ofNat (tail.toNat+a.encoding.size)::R)
      (recordArrayStepMemory mem head base tail src dataPtr) aw' rdata σ k' C' := by
  have rd1 := easBlocks.eas_block_14292_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [ult_one hi]; decide)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw1,k1,C1,rd2⟩ := easBlocks.eas_block_14362_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  let mid := Reasoning.Theory.writeWord mem head.toNat (recordArrayOffsetWord base tail)
  have hp : MemoryPrefix mem mid limit := memoryPrefix_sparse_writeWord mem head.toNat limit _ (Or.inl hhead)
  have hv : AttestationMemoryView mid src dataPtr a := hview.preserve hp hsrc hdata (by omega)
  have hm : memLoad slot mid = src := (memLoad_of_prefix hp slot hslotLow hslot hslotIn).trans hload
  change ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨14292⟩ _
    (attestationEncodedMemory mid src tail dataPtr) aw' rdata σ k' C'
  change RD fork (deployedRuntime v) ee g s0 ⟨4502⟩
    (memLoad slot mid::tail::⟨14421⟩::⟨32⟩::⟨32⟩::⟨1⟩::head::i::len::base::slot::R) mid aw1 rdata σ k1 C1 at rd2
  rw [hm] at rd2
  obtain ⟨aw2,k2,C2,rd3⟩ := easEncodeAttestation v (by simp only [List.length_cons]; omega)
    hv.sourceLow hv.dataLow (by omega) hv.sourceCovered (by omega) hv.dataCovered hv.pointer hv.length hbound
    (by rw [easPatchedValidJumps v]; jump_dest) rd2
  obtain ⟨aw3,k3,C3,rd4⟩ := easBlocks.eas_block_14421_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd3
  simpa only [easBlocks.eas_block_14421_stack, a.encoding_size, Nat.add_assoc] using
    (show ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨14292⟩ _
      (attestationEncodedMemory mid src tail dataPtr) aw' rdata σ k' C' from ⟨aw3,k3,C3,rd4⟩)

end Benchmarks.EAS.EAS
