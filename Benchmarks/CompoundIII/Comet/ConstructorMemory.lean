import Benchmarks.CompoundIII.Comet.ConstructorEntry

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem constructorEntryMemory_size : constructorEntryMemory.size = 96 := by native_decide

theorem constructorAllocatedMemory_size (c : ConstructorConfig) :
    (constructorAllocatedMemory c).size = 96 := by
  rw [constructorAllocatedMemory, writeWord_size _ _ _ (by
    rw [constructorEntryMemory_size]; exact lt_usize 0 (by decide)), constructorEntryMemory_size]
  rfl

def constructorCopiedMemory (c : ConstructorConfig) : ByteArray :=
  constructorAllocatedMemory c ++ ByteArray.zeroes 832 ++ c.encodedArgs.toByteArray

theorem constructorCodecopy (c : ConstructorConfig) :
    (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray).write 21425
      (constructorAllocatedMemory c) 928 c.encodedArgs.length = constructorCopiedMemory c := by
  rw [byteArray_write_from_ge_eq_no_gap_bound _ _ _ _ _
    (by rw [ConstructorConfig.encodedArgs_length]; omega)
    (by rw [ByteArray.size_append, cometCreationBytecode_size, List.size_toByteArray])
    (by rw [constructorAllocatedMemory_size]; decide)]
  rw [constructorAllocatedMemory_size]
  have he := extract_append_right cometWithExtendedAssetListCreationBytecode
    c.encodedArgs.toByteArray
  rw [cometCreationBytecode_size, List.size_toByteArray] at he
  rw [he]
  rfl

theorem constructorCopiedMemory_size (c : ConstructorConfig) :
    (constructorCopiedMemory c).size = 1664 + 224 * c.assetConfigs.length := by
  simp only [constructorCopiedMemory, ByteArray.size_append, constructorAllocatedMemory_size,
    ByteArray_zeroes_size, List.size_toByteArray, ConstructorConfig.encodedArgs_length]
  omega

/-- Every argument word is copied faithfully, including words in an arbitrarily long asset array. -/
theorem constructorCopiedMemory_read (c : ConstructorConfig) (off : Nat)
    (hoff : off + 32 ≤ c.encodedArgs.length) :
    (constructorCopiedMemory c).readWithPadding (928 + off) 32 =
      c.encodedArgs.toByteArray.readWithPadding off 32 := by
  have hp : (constructorAllocatedMemory c ++ ByteArray.zeroes 832).size = 928 := by
    rw [ByteArray.size_append, constructorAllocatedMemory_size, ByteArray_zeroes_size]
  have hl : c.encodedArgs.toByteArray.size = c.encodedArgs.length := List.size_toByteArray
  rw [readWithPadding_eq_extract _ _ (by
    rw [constructorCopiedMemory_size, ConstructorConfig.encodedArgs_length] at *; omega),
    readWithPadding_eq_extract _ _ (by omega), constructorCopiedMemory,
    extract_append_right_window _ _ _ _ (by rw [hp]; omega), hp]
  rw [show 928 + off - 928 = off by omega,
    show 928 + off + 32 - 928 = off + 32 by omega]

-- LIBRARY CANDIDATE: read one word from a list of ABI words.
theorem constructorWordBytes_read (ws : List UInt256) (i : Nat) (hi : i < ws.length) :
    (wordBytes ws).readWithPadding (32 * i) 32 = ws[i].toByteArray := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero =>
      rw [readWithPadding_eq_extract _ _ (by rw [wordBytes_size]; simp), wordBytes,
        extract_append_left _ _ _ _ (by rw [toByteArray_size])]
      exact toByteArray_extract_all _
    | succ i =>
      have hi' : i < ws.length := by simpa using hi
      rw [readWithPadding_eq_extract _ _ (by rw [wordBytes_size]; simp only [List.length_cons]; omega),
        wordBytes, extract_append_right_window _ _ _ _ (by rw [toByteArray_size]; omega),
        toByteArray_size]
      have hstart : 32 * (i + 1) - 32 = 32 * i := by omega
      have hend : 32 * (i + 1) + 32 - 32 = 32 * i + 32 := by omega
      rw [hstart, hend, ← readWithPadding_eq_extract _ _ (by rw [wordBytes_size]; omega)]
      exact ih i hi'

def ConstructorAsset.words (c : ConstructorAsset) : List UInt256 :=
  c.scalars.map ScalarReturn.word

def ConstructorConfig.argumentWords (c : ConstructorConfig) : List UInt256 :=
  [⟨32⟩] ++ c.scalars.map ScalarReturn.word ++ [⟨672⟩, UInt256.ofNat c.assetConfigs.length] ++
    c.assetConfigs.flatMap ConstructorAsset.words

theorem ConstructorConfig.encodedArgs_wordBytes (c : ConstructorConfig) :
    c.encodedArgs.toByteArray = wordBytes c.argumentWords := by
  rw [wordBytes_eq_list]
  apply congrArg List.toByteArray
  simp only [ConstructorConfig.encodedArgs, ConstructorConfig.argumentWords,
    ConstructorAsset.words, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.flatMap_map, List.flatMap_assoc, List.append_assoc]
  rfl

theorem constructorCopiedMemory_word (c : ConstructorConfig) (i : Nat)
    (hi : i < c.argumentWords.length) :
    (constructorCopiedMemory c).readWithPadding (928 + 32 * i) 32 =
      c.argumentWords[i].toByteArray := by
  have hlen : c.encodedArgs.length = 32 * c.argumentWords.length := by
    rw [← List.size_toByteArray, c.encodedArgs_wordBytes, wordBytes_size]
  rw [constructorCopiedMemory_read _ _ (by omega), c.encodedArgs_wordBytes]
  exact constructorWordBytes_read _ _ hi

theorem constructorCopiedMemory_load (c : ConstructorConfig) (i : Nat)
    (hi : i < c.argumentWords.length)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    memLoad (UInt256.ofNat (928 + 32 * i)) (constructorCopiedMemory c) = c.argumentWords[i] := by
  have hlen : 32 * c.argumentWords.length = 736 + 224 * c.assetConfigs.length := by
    have hh := congrArg ByteArray.size c.encodedArgs_wordBytes
    simpa only [List.size_toByteArray, ConstructorConfig.encodedArgs_length, wordBytes_size] using hh.symm
  have hoff : 928 + 32 * i < UInt256.size := by omega
  have hin : ¬ 928 + 32 * i ≥ (constructorCopiedMemory c).size := by
    rw [constructorCopiedMemory_size]; omega
  rw [memLoad, UInt256.toNat_ofNat_of_lt hoff, if_neg hin, constructorCopiedMemory_word c i hi,
    fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem constructorCopiedMemory_outerOffset (c : ConstructorConfig)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    memLoad ⟨928⟩ (constructorCopiedMemory c) = ⟨32⟩ := by
  have hi : 0 < c.argumentWords.length := by
    simp only [ConstructorConfig.argumentWords, List.length_append, List.length_cons, List.length_nil]
    omega
  exact constructorCopiedMemory_load c 0 hi hsize

theorem constructorCopiedMemory_free (c : ConstructorConfig) :
    memLoad (UInt256.ofNat 64) (constructorCopiedMemory c) =
      UInt256.ofNat (1664 + 224 * c.assetConfigs.length) := by
  apply mloadWordValue_of_readWithPadding
  · rw [constructorCopiedMemory_size]; change 64 < _; omega
  · change (constructorCopiedMemory c).readWithPadding 64 32 = _
    rw [readWithPadding_eq_extract _ _ (by rw [constructorCopiedMemory_size]; omega),
      constructorCopiedMemory, extract_append_left _ _ _ _ (by
        rw [ByteArray.size_append, constructorAllocatedMemory_size, ByteArray_zeroes_size]; decide),
      extract_append_left _ _ _ _ (by rw [constructorAllocatedMemory_size]),
      ← readWithPadding_eq_extract _ _ (by rw [constructorAllocatedMemory_size])]
    exact writeWord_sparse_read_back _ _ _

end Benchmarks.CompoundIII.Comet
