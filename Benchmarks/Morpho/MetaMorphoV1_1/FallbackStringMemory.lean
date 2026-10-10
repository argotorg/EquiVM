import Benchmarks.Morpho.MetaMorphoV1_1.StringMemoryRead
import Benchmarks.EAS.Attester.StructAllocMemory

/-! Storage-string copies at an arbitrary cursor, as used by the domain fallbacks. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def fallbackStringMemory (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (base header : UInt256) (free : Nat) : ByteArray :=
  let len := storageStringLength header
  let sized := writeWord mem free len
  if UInt256.land header ⟨1⟩ = ⟨0⟩ then
    writeWord sized (free + 32) (shortStringDataWord header)
  else wordSequenceMemory (writeWord sized 0 base) (free + 32)
    (stringStorageWords I σ (solidityBytesDataBaseSlot base) (stringWordCount len))

theorem fallbackStringMemory_size (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (base header : UInt256) (free : Nat) (hvalid : storageStringValid header) :
    free + 32 + 32 * stringWordCount (storageStringLength header) ≤
      (fallbackStringMemory I σ mem base header free).size := by
  unfold fallbackStringMemory
  split
  · have hl := storageStringShortLength header hvalid ‹_›
    simp only [writeWord_sparse_size]
    unfold stringWordCount
    omega
  · rw [wordSequenceMemory_size _ (by simp only [writeWord_sparse_size]; omega),
      stringStorageWords_length]
    exact Nat.le_max_right _ _

theorem fallbackStringMemory_length (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (base header : UInt256) (free : Nat) (hlo : 96 ≤ free) (hfit : free < UInt256.size) :
    memLoad (UInt256.ofNat free) (fallbackStringMemory I σ mem base header free) =
      storageStringLength header := by
  unfold fallbackStringMemory
  split
  · unfold Reasoning.Theory.writeWord
    rw [memLoad_write_disjoint _ _ _ _
      (by rw [UInt256.toNat_ofNat_of_lt hfit, wordWrite_size]; omega)
      (.inl (by rw [UInt256.toNat_ofNat_of_lt hfit]))]
    exact memLoad_write_same _ _ _ _ (UInt256.toNat_ofNat_of_lt hfit)
  · have hp := wordSequenceMemory_prefix
      (writeWord (writeWord mem free (storageStringLength header)) 0 base) (free + 32)
      (stringStorageWords I σ (solidityBytesDataBaseSlot base)
        (stringWordCount (storageStringLength header)))
    rw [hp.load_preserved hlo (le_refl _) (by simp only [writeWord_sparse_size]; omega) hfit]
    unfold Reasoning.Theory.writeWord
    rw [memLoad_write_disjoint _ _ _ _
      (by rw [UInt256.toNat_ofNat_of_lt hfit, wordWrite_size]; omega)
      (.inr (by rw [UInt256.toNat_ofNat_of_lt hfit]; omega))]
    exact memLoad_write_same _ _ _ _ (UInt256.toNat_ofNat_of_lt hfit)

theorem fallbackStringMemory_prefix (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (base header : UInt256) (free : Nat) :
    MemoryPrefix mem (fallbackStringMemory I σ mem base header free) free := by
  unfold fallbackStringMemory
  have hp := memoryPrefix_sparse_writeWord mem free free (storageStringLength header) (.inl rfl.le)
  split
  · exact hp.trans (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (by omega)))
  · exact (hp.trans (memoryPrefix_sparse_writeWord _ _ _ _ (.inr (by decide)))).trans
      ((wordSequenceMemory_prefix _ _ _).mono (by omega))

theorem fallbackStringMemory_free (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (base header : UInt256) (free : Nat) (hlo : 96 ≤ free) (hmem : 96 ≤ mem.size) :
    memLoad (UInt256.ofNat 64) (fallbackStringMemory I σ mem base header free) =
      memLoad (UInt256.ofNat 64) mem := by
  unfold fallbackStringMemory
  split
  · unfold Reasoning.Theory.writeWord
    rw [memLoad_write_disjoint _ _ _ _ (by rw [wordWrite_size]; change 96 ≤ _; omega)
      (.inl (by change 96 ≤ free + 32; omega)),
      memLoad_write_disjoint _ _ _ _ (by exact hmem) (.inl (by exact hlo))]
  · rw [wordSequenceMemory_load_below _ (by simp only [writeWord_sparse_size]; omega)
      (by omega) (by decide)]
    unfold Reasoning.Theory.writeWord
    rw [memLoad_write_disjoint _ _ _ _ (by rw [wordWrite_size]; change 96 ≤ _; omega)
      (.inr (by decide)),
      memLoad_write_disjoint _ _ _ _ (by exact hmem) (.inl (by exact hlo))]

theorem fallbackStringMemory_read (evm : State) (mem : ByteArray) (base : UInt256)
    (free : Nat) (hvalid : storageStringValid (storageStringHeader evm base)) :
    (fallbackStringMemory evm.executionEnv evm.accountMap mem base
      (storageStringHeader evm base) free).readWithPadding
        (free + 32) (storageStringLength (storageStringHeader evm base)).toNat =
      storageStringBytes evm base := by
  let len := storageStringLength (storageStringHeader evm base)
  have hcover : len.toNat ≤ 32 * stringWordCount len := by unfold stringWordCount; omega
  unfold fallbackStringMemory
  split
  · have hl := storageStringShortLength _ hvalid ‹_›
    change len.toNat < 32 at hl
    rw [storageStringBytes, if_pos hl]
    by_cases hz : len.toNat = 0
    · change _ = (storageStringHeader evm base).toByteArray.extract 0 len.toNat
      rw [hz, byteArray_readWithPadding_zero, byteArray_extract_empty_of_le _ (by omega)]
    · simpa only [Nat.add_zero, Nat.zero_add,
        shortStringDataWord_prefix _ _ (by omega : len.toNat ≤ 31)] using
        writeWord_sparse_read_window (writeWord mem free len) (free + 32) 0 len.toNat
          (shortStringDataWord (storageStringHeader evm base)) (by omega) (by omega) (by omega)
  · have hl := storageStringLongLength _ hvalid ‹_›
    rw [storageStringBytes, if_neg (Nat.not_lt.mpr hl)]
    let words := stringStorageWords evm.executionEnv evm.accountMap
      (solidityBytesDataBaseSlot base) (stringWordCount len)
    have hw : words.length = stringWordCount len := stringStorageWords_length _ _ _ _
    have hs : free + 32 + 32 * words.length ≤
        (wordSequenceMemory (writeWord (writeWord mem free len) 0 base) (free + 32) words).size :=
      by
      rw [wordSequenceMemory_size _ (by simp only [writeWord_sparse_size]; omega)]
      exact Nat.le_max_right _ _
    rw [← memoryRead_prefix _ (free + 32) (32 * words.length) len.toNat
      (by rw [hw]; exact hcover) hs, wordSequenceMemory_read]
    have hb := stringStorageWords_bytes evm base 0 (stringWordCount len)
    simp only [solidityBytesDataSlot, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
      u256_add_zero] at hb
    exact congrArg (fun bytes : ByteArray ↦ bytes.extract 0 len.toNat) hb

end Benchmarks.Morpho.MetaMorphoV1_1
