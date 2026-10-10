import Benchmarks.Morpho.MetaMorphoV1_1.StringCopyMemory

/-! Reads of the memory representation shared by the string getters. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: taking a prefix of an in-bounds memory read, including empty reads.
theorem memoryRead_prefix (mem : ByteArray) (off total len : Nat)
    (hlen : len ≤ total) (hin : off + total ≤ mem.size) :
    (mem.readWithPadding off total).extract 0 len = mem.readWithPadding off len := by
  by_cases hz : len = 0
  · subst len
    rw [byteArray_extract_empty_of_le _ (by omega), byteArray_readWithPadding_zero]
  · rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) hin,
      readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by omega), extract_extract_BA]
    congr 1 <;> omega

theorem stringCopyMemory_size (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (base header : UInt256) (hvalid : storageStringValid header) :
    160 + 32 * stringWordCount (storageStringLength header) ≤
      (stringCopyMemory I σ mem base header (storageStringLength header)).size := by
  unfold stringCopyMemory
  split
  · have hl := storageStringShortLength header hvalid ‹_›
    simp only [shortStringCopyMemory, writeWord_sparse_size]
    unfold stringWordCount
    omega
  · rw [longStringCopyMemory, wordSequenceMemory_size _ (by
      simp only [writeWord_sparse_size]; omega), stringStorageWords_length]
    exact Nat.le_max_right _ _

theorem stringCopyMemory_length (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (base header len : UInt256) :
    memLoad ⟨128⟩ (stringCopyMemory I σ mem base header len) = len := by
  unfold stringCopyMemory
  split
  · simp only [shortStringCopyMemory, Reasoning.Theory.writeWord]
    rw [memLoad_write_disjoint _ _ _ _ (by rw [wordWrite_size]; change 160 ≤ _; omega)
      (.inl (by decide))]
    exact memLoad_write_same mem 128 ⟨128⟩ len rfl
  · rw [longStringCopyMemory]
    have hp := (wordSequenceMemory_prefix
      (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem 128 len) 0 base) 160
      (stringStorageWords I σ (solidityBytesDataBaseSlot base) (stringWordCount len)))
    have hh := hp.load_preserved (off := 128) (by decide) (by decide)
      (by simp only [writeWord_sparse_size]; omega) (by decide)
    change memLoad ⟨128⟩ _ = memLoad ⟨128⟩ _ at hh
    rw [hh]
    simp only [Reasoning.Theory.writeWord]
    rw [memLoad_write_disjoint _ _ _ _ (by rw [wordWrite_size]; change 160 ≤ _; omega)
      (.inr (by decide))]
    exact memLoad_write_same mem 128 ⟨128⟩ len rfl

theorem shortStringCopyMemory_read (mem : ByteArray) (header len : UInt256)
    (hlen : len.toNat < 32) :
    (shortStringCopyMemory mem header len).readWithPadding 160 len.toNat =
      header.toByteArray.extract 0 len.toNat := by
  by_cases hz : len.toNat = 0
  · rw [hz, byteArray_readWithPadding_zero, byteArray_extract_empty_of_le _ (by omega)]
  · have hr := writeWord_sparse_read_window
      (Reasoning.Theory.writeWord mem 128 len) 160 0 len.toNat (shortStringDataWord header)
      (by omega) (by omega) (by omega)
    simpa only [Nat.add_zero, Nat.zero_add,
      shortStringDataWord_prefix header len.toNat (by omega)] using hr

theorem longStringCopyMemory_read (evm : State) (mem : ByteArray) (base len : UInt256) :
    (longStringCopyMemory evm.executionEnv evm.accountMap mem base len).readWithPadding
      160 len.toNat =
      (readSolidityBytesDataWordsFrom evm base 0 (stringWordCount len)).extract 0 len.toNat := by
  let words := stringStorageWords evm.executionEnv evm.accountMap
    (solidityBytesDataBaseSlot base) (stringWordCount len)
  have hwlen : words.length = stringWordCount len := stringStorageWords_length _ _ _ _
  have hs : 160 + 32 * words.length ≤
      (longStringCopyMemory evm.executionEnv evm.accountMap mem base len).size := by
    rw [longStringCopyMemory, wordSequenceMemory_size _ (by
      simp only [writeWord_sparse_size]; omega)]
    exact Nat.le_max_right _ _
  rw [← memoryRead_prefix _ 160 (32 * words.length) len.toNat
    (by rw [hwlen]; unfold stringWordCount; omega) hs]
  change ((wordSequenceMemory _ 160 words).readWithPadding 160 (32 * words.length)).extract
    0 len.toNat = _
  rw [wordSequenceMemory_read]
  have hk : solidityBytesDataSlot base 0 = solidityBytesDataBaseSlot base := by
    simp only [solidityBytesDataSlot, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
      u256_add_zero]
  have hb := stringStorageWords_bytes evm base 0 (stringWordCount len)
  rw [hk] at hb
  exact congrArg (fun bytes : ByteArray ↦ bytes.extract 0 len.toNat) hb

theorem stringCopyMemory_read (evm : State) (mem : ByteArray) (base : UInt256)
    (hvalid : storageStringValid (storageStringHeader evm base)) :
    (stringCopyMemory evm.executionEnv evm.accountMap mem base (storageStringHeader evm base)
      (storageStringLength (storageStringHeader evm base))).readWithPadding
        160 (storageStringLength (storageStringHeader evm base)).toNat =
      storageStringBytes evm base := by
  unfold stringCopyMemory
  split
  · have hl := storageStringShortLength _ hvalid ‹_›
    rw [shortStringCopyMemory_read _ _ _ hl]
    simp only [storageStringBytes, if_pos hl]
  · have hl := storageStringLongLength _ hvalid ‹_›
    rw [longStringCopyMemory_read]
    simp only [storageStringBytes, if_neg (Nat.not_lt.mpr hl),
      stringWordCount, solidityBytesDataWordCount]

end Benchmarks.Morpho.MetaMorphoV1_1
