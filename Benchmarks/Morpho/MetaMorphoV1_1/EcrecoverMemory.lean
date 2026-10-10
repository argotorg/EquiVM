import Benchmarks.Morpho.MetaMorphoV1_1.EcrecoverABI
import Benchmarks.Morpho.MetaMorphoV1_1.StructReturnMemory

/-! Fixed recovery buffers: four input words and a zeroed output word in scratch memory. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def ecrecoverCallMemory (mem : ByteArray) (free : Nat)
    (hash sigV sigR sigS : UInt256) : ByteArray :=
  writeWord (wordSequenceMemory mem free [hash, sigV, sigR, sigS]) 0 ⟨0⟩

def ecrecoverReturnMemory (mem out : ByteArray) : ByteArray := out.write 0 mem 0 out.size

theorem ecrecoverCallMemory_read (mem : ByteArray) (free : Nat)
    (hash sigV sigR sigS : UInt256) (hlo : 32 ≤ free) :
    (ecrecoverCallMemory mem free hash sigV sigR sigS).readWithPadding free 128 =
      ecrecoverInput hash sigV sigR sigS := by
  have hsize : free + 128 ≤ (wordSequenceMemory mem free [hash, sigV, sigR, sigS]).size := by
    rw [wordSequenceMemory_size_nonempty _ _ _ (by simp)]
    simp only [List.length_cons, List.length_nil]
    omega
  rw [ecrecoverCallMemory,
    writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hsize (.inr hlo)]
  exact wordSequenceMemory_read mem free [hash, sigV, sigR, sigS]

theorem ecrecoverCallMemory_zero (mem : ByteArray) (free : Nat)
    (hash sigV sigR sigS : UInt256) :
    memLoad ⟨0⟩ (ecrecoverCallMemory mem free hash sigV sigR sigS) = ⟨0⟩ :=
  memLoad_write_same _ _ _ _ rfl

theorem ecrecoverCallMemory_free (mem : ByteArray) (free : Nat)
    (hash sigV sigR sigS : UInt256) (hlo : 96 ≤ free) (hsize : 96 ≤ mem.size) :
    memLoad ⟨64⟩ (ecrecoverCallMemory mem free hash sigV sigR sigS) = memLoad ⟨64⟩ mem := by
  rw [ecrecoverCallMemory]
  rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
    (by rw [wordSequenceMemory_size_nonempty _ _ _ (by simp)]; exact le_trans hsize (by omega))
    (.inr (by decide))]
  exact wordSequenceMemory_load_below _ hsize hlo (by decide)

theorem ecrecoverReturnMemory_empty (mem : ByteArray) :
    ecrecoverReturnMemory mem ByteArray.empty = mem := by
  exact byteArray_write_len_zero _ _ _ _

theorem ecrecoverReturnMemory_full (mem : ByteArray) {out : ByteArray} (hsize : out.size = 32) :
    ecrecoverReturnMemory mem out = writeWord mem 0 (uInt256OfByteArray out) := by
  rw [ecrecoverReturnMemory, hsize, Reasoning.Theory.writeWord,
    toByteArray_uInt256OfByteArray_of_size32 hsize]

theorem ecrecoverReturnMemory_load {mem out : ByteArray} (hzero : memLoad ⟨0⟩ mem = ⟨0⟩)
    (hout : EcrecoverOutput out) :
    memLoad ⟨0⟩ (ecrecoverReturnMemory mem out) = uInt256OfByteArray out := by
  rcases hout with rfl | ⟨hsize, _⟩
  · rw [ecrecoverReturnMemory_empty]
    exact hzero
  · rw [ecrecoverReturnMemory_full mem hsize]
    exact memLoad_write_same _ _ _ _ rfl

theorem ecrecoverReturnMemory_free {mem out : ByteArray} (hsize : 96 ≤ mem.size)
    (hout : EcrecoverOutput out) :
    memLoad ⟨64⟩ (ecrecoverReturnMemory mem out) = memLoad ⟨64⟩ mem := by
  rcases hout with rfl | ⟨hfull, _⟩
  · rw [ecrecoverReturnMemory_empty]
  · rw [ecrecoverReturnMemory_full mem hfull]
    exact memLoad_write_disjoint _ _ _ _ hsize (.inr (by decide))

theorem ecrecoverSignerWord {out : ByteArray} (hout : EcrecoverOutput out) :
    UInt256.ofNat (ecrecoverSigner out).toNat = uInt256OfByteArray out := by
  rcases hout with rfl | ⟨_, hcanon⟩
  · rfl
  · change EVM.word (AccountAddress.ofNat (uInt256OfByteArray out).toNat).val = _
    rw [word_of_addressOfNat_eq_mask, solcAddrMask_clean hcanon]

end Benchmarks.Morpho.MetaMorphoV1_1
