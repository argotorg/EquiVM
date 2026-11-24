import Benchmarks.EAS.EAS.RecordArrayLoop

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def recordArrayInitialMemory (mem : ByteArray) (base : UInt256) (len : Nat) : ByteArray :=
  Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem base.toNat ⟨64⟩) (base.toNat+64) (UInt256.ofNat len)

theorem recordArrayInitialMemory_prefix (mem : ByteArray) (base : UInt256) (len : Nat) :
    MemoryPrefix mem (recordArrayInitialMemory mem base len) base.toNat :=
  (memoryPrefix_sparse_writeWord mem base.toNat base.toNat _ (Or.inl (le_refl _))).trans
    (memoryPrefix_sparse_writeWord _ (base.toNat+64) base.toNat _ (Or.inl (by omega)))

theorem recordArrayInitialMemory_view (mem : ByteArray) (base : UInt256) (ats : List AttestationRecord) (limit : Nat)
    (hbase : limit ≤ base.toNat) :
    RecordArrayLoopView mem (recordArrayInitialMemory mem base ats.length) base ats limit 0 := by
  refine ⟨by omega, (recordArrayInitialMemory_prefix mem base ats.length).mono hbase, ?_, ?_, Or.inl rfl, ?_, ?_, ?_⟩
  · simp only [recordArrayHead, Nat.mul_zero, Nat.add_zero, recordArrayInitialMemory, writeWord_sparse_size]
    omega
  · simp only [Nat.mul_zero, byteArray_readWithPadding_zero, attestationArrayHeads, List.take_zero,
      List.map_nil, dynamicOffsets, wordBytes]
  · rw [recordArrayInitialMemory, writeWord_sparse_read_preserved _ (base.toNat+64) base.toNat _
      (Or.inl ⟨by omega, by rw [writeWord_sparse_size]; omega⟩), writeWord_sparse_read_back]
    rfl
  · exact writeWord_sparse_read_back _ _ _
  · simp only [attestationArrayBodies, List.take_zero, List.map_nil, dynamicBodies, ByteArray.size_empty,
      byteArray_readWithPadding_zero]

theorem easEncodeRecordArrayStart {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {base array : UInt256} {ats : List AttestationRecord} {limit : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+8 ≤ 1024)
    (harray : AttestationArrayMemoryView mem array ats limit)
    (hbase : limit ≤ base.toNat)
    (hbound : base.toNat+128+attestationArrayOffset ats ats.length < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨14256⟩ (base::array::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨14292⟩ (recordArrayStack base array ats 0 R)
      (recordArrayInitialMemory mem base ats.length) aw' rdata σ k' C' := by
  have hp : MemoryPrefix mem (Reasoning.Theory.writeWord mem base.toNat ⟨64⟩) limit :=
    memoryPrefix_sparse_writeWord mem base.toNat limit _ (Or.inl hbase)
  have hl : memLoad array (Reasoning.Theory.writeWord mem base.toNat ⟨64⟩) = UInt256.ofNat ats.length :=
    (memLoad_of_prefix hp array harray.low (by have := harray.span; omega) (by have := harray.covered; omega)).trans harray.length
  have hlen : 32*ats.length < UInt256.size := by unfold attestationArrayOffset at hbound; omega
  have h64 : (base+UInt256.ofNat 64).toNat = base.toNat+64 := uadd_word_ofNat_toNat base 64 (by omega)
  have h96 : base+UInt256.ofNat 96 = UInt256.ofNat (base.toNat+96) := by
    apply u256_inj
    rw [uadd_word_ofNat_toNat base 96 (by omega), ulit_toNat' _ (by omega)]
  have ha32 : array+UInt256.ofNat 32 = UInt256.ofNat (array.toNat+32) := by
    apply u256_inj
    rw [uadd_word_ofNat_toNat array 32 (by have := harray.span; omega), ulit_toNat' _ (by have := harray.span; omega)]
  have htail : (base+UInt256.shiftLeft (UInt256.ofNat ats.length) (UInt256.ofNat 5))+UInt256.ofNat 96 =
      UInt256.ofNat (base.toNat+96+32*ats.length) := by
    change (base+UInt256.shiftLeft (UInt256.ofNat ats.length) ⟨5⟩)+UInt256.ofNat 96 = _
    rw [shiftLeft5_ofNat_eq hlen]
    have hs : (base+UInt256.ofNat (32*ats.length)).toNat = base.toNat+32*ats.length :=
      uadd_word_ofNat_toNat base _ (by unfold attestationArrayOffset at hbound; omega)
    apply u256_inj
    rw [uadd_word_ofNat_toNat _ 96 (by rw [hs]; unfold attestationArrayOffset at hbound; omega), hs,
      ulit_toNat' _ (by unfold attestationArrayOffset at hbound; omega)]
    omega
  obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14256_packed (immWords := wordsOf (immStore v)) hstack rd
  change memLoad array ((UInt256.ofNat 64).toByteArray.write 0 mem base.toNat 32) = _ at hl
  simp only [easBlocks.eas_block_14256_stack, easBlocks.eas_block_14256_memory, hl, h64, h96, ha32, htail] at rd1
  simpa only [recordArrayStack, recordArrayHead, recordArrayTail, attestationArrayOffset,
    attestationArrayBodies, List.take_zero, List.map_nil, dynamicBodies, ByteArray.size_empty,
    Nat.mul_zero, Nat.add_zero, recordArrayInitialMemory, Reasoning.Theory.writeWord] using
    (show ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨14292⟩ _ _ aw' rdata σ k' C' from ⟨aw1,k1,C1,rd1⟩)

theorem easEncodeRecordArray {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {base array : UInt256} {ats : List AttestationRecord} {limit : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+23 ≤ 1024)
    (harray : AttestationArrayMemoryView mem array ats limit)
    (hbase : limit ≤ base.toNat)
    (hbound : base.toNat+128+attestationArrayOffset ats ats.length < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨14256⟩ (base::array::R) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨14300⟩ (recordArrayStack base array ats ats.length R) mem' aw' rdata σ k' C' ∧
      RecordArrayLoopView mem mem' base ats limit ats.length := by
  obtain ⟨aw1,k1,C1,rd1⟩ := easEncodeRecordArrayStart v (by omega) harray hbase hbound rd
  exact easEncodeRecordArrayLoop v hstack harray (recordArrayInitialMemory_view mem base ats limit hbase) hbase hbound rd1

end Benchmarks.EAS.EAS
