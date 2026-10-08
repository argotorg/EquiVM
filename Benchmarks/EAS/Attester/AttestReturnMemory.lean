import Benchmarks.EAS.Attester.AttestMemory
import Reasoning.WordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

def attestOutputMemory (schema input : UInt256) (out : ByteArray) : ByteArray :=
  out.write 0 (attestMemory schema input) 448 (min 32 out.size)

theorem attestOutputMemory_size (schema input : UInt256) (out : ByteArray) :
    (attestOutputMemory schema input out).size = 836 := by
  rw [attestOutputMemory, byteArray_write_size_of_inBounds]
  · exact attestMemory_size schema input
  · exact Nat.min_le_right _ _
  · rw [attestMemory_size]; have := Nat.min_le_left 32 out.size; omega

theorem attestOutputMemory_freePtr (schema input : UInt256) (out : ByteArray) :
    memLoad (UInt256.ofNat 64) (attestOutputMemory schema input out) = ⟨448⟩ := by
  have hread : (attestMemory schema input).readWithPadding 64 32 =
      (⟨448⟩ : UInt256).toByteArray :=
    readWord_of_memLoad _ _ _ (by rw [attestMemory_size]; decide) (by decide)
      (attestMemory_freePtr schema input)
  apply mloadWordValue_of_readWithPadding
  · rw [attestOutputMemory_size]; decide
  · change (out.write 0 (attestMemory schema input) 448 (min 32 out.size)).readWithPadding 64 32 = _
    by_cases hz : min 32 out.size = 0
    · rw [hz, byteArray_write_len_zero]; exact hread
    rw [copyWindow_read_preserved out (attestMemory schema input) 0 448 (min 32 out.size) 64
      hz (by have := Nat.min_le_right 32 out.size; omega)
      (by rw [attestMemory_size]; decide) (by rw [attestMemory_size]; decide) (.inl (by decide))]
    exact hread

theorem attestOutputMemory_word {schema input : UInt256} {out : ByteArray}
    (hlen : 32 ≤ out.size) :
    memLoad (UInt256.ofNat 448) (attestOutputMemory schema input out) = calldataWord out 0 := by
  have hread : (attestOutputMemory schema input out).readWithPadding 448 32 =
      out.readWithPadding 0 32 := by
    simp only [attestOutputMemory, Nat.min_eq_left hlen]
    exact copyWindow_read_word out (attestMemory schema input) 0 448 32 0 (by decide)
      hlen (by rw [attestMemory_size]; decide) (by decide)
  have hw : calldataWord out 0 = uInt256OfByteArray (out.extract 0 32) := by
    change uInt256OfByteArray (out.readBytes 0 32) = _
    rw [← decode_word_at_eq out 0 hlen (by decide), List.drop_zero,
      bytesToWord_take32_eq_extract0_32, uInt256OfByteArray_eq]
  unfold memLoad
  rw [if_neg (by rw [attestOutputMemory_size]; decide)]
  change UInt256.ofNat (fromByteArrayBigEndian ((attestOutputMemory schema input
      out).readWithPadding 448 32)) = _
  rw [hread,
    readWithPadding_eq_extract out 0 hlen, hw, uInt256OfByteArray_eq]

def attestReturnPtr (out : ByteArray) : UInt256 :=
  ⟨448⟩ + UInt256.land (UInt256.ofNat out.size + ⟨31⟩) (UInt256.lnot ⟨31⟩)

theorem attestReturnPtr_bounds {out : ByteArray} (hhi : out.size < 2 ^ 255) :
    96 ≤ (attestReturnPtr out).toNat ∧ (attestReturnPtr out).toNat + 32 < UInt256.size := by
  have hsize : out.size < UInt256.size := by change out.size < 2 ^ 256; omega
  have hsum : (UInt256.ofNat out.size + ⟨31⟩).toNat = out.size + 31 := by
    rw [uadd_toNat, ulit_toNat' _ hsize]
    change (out.size + 31) % 2 ^ 256 = out.size + 31
    apply Nat.mod_eq_of_lt; omega
  have hr := longDataCutoff_toNat (UInt256.ofNat out.size + ⟨31⟩)
  rw [hsum] at hr
  have hle := Nat.div_mul_le_self (out.size + 31) 32
  unfold attestReturnPtr
  rw [uadd_toNat, hr]
  change 96 ≤ (448 + (out.size + 31) / 32 * 32) % 2 ^ 256 ∧
    (448 + (out.size + 31) / 32 * 32) % 2 ^ 256 + 32 < 2 ^ 256
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

def attestDecodedMemory (schema input : UInt256) (out : ByteArray) : ByteArray :=
  (attestReturnPtr out).toByteArray.write 0 (attestOutputMemory schema input out) 64 32

theorem attestDecodedMemory_size (schema input : UInt256) (out : ByteArray) :
    (attestDecodedMemory schema input out).size = 836 := by
  rw [attestDecodedMemory, wordWrite_size, attestOutputMemory_size]; rfl

theorem attestDecodedMemory_freePtr (schema input : UInt256) (out : ByteArray) :
    memLoad (UInt256.ofNat 64) (attestDecodedMemory schema input out) = attestReturnPtr out :=
  memLoad_write_same _ _ _ _ rfl

theorem attestDecodedMemory_word {schema input : UInt256} {out : ByteArray}
    (hlen : 32 ≤ out.size) :
    memLoad (UInt256.ofNat 448) (attestDecodedMemory schema input out) = calldataWord out 0 := by
  rw [attestDecodedMemory, memLoad_write_disjoint]
  · exact attestOutputMemory_word hlen
  · rw [attestOutputMemory_size]; decide
  · decide

end Benchmarks.EAS.Attester
