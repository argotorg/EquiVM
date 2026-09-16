import Examples.UniswapV2Pair.ConstructorMemory
import Examples.UniswapV2Pair.Trusted

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000

noncomputable def constructorDomainDataMem (typeHash thisWord : UInt256) : ByteArray :=
  writeCascade constructorLiteralMem [(288, typeHash), (320, constructorNameHashWord),
    (352, constructorVersionHashWord), (384, ⟨1⟩), (416, thisWord)]

theorem constructorDomainDataMem_size (typeHash thisWord : UInt256) :
    (constructorDomainDataMem typeHash thisWord).size = 448 := by
  apply writeCascade_size_of_base _ _ constructorLiteralMem_size
  · simp only [WriteGapsOk]; native_decide
  · rfl

theorem constructorDomainDataMem_read64 (typeHash thisWord : UInt256) :
    (constructorDomainDataMem typeHash thisWord).readWithPadding 64 32 =
      (⟨256⟩ : UInt256).toByteArray := by
  unfold constructorDomainDataMem
  rw [writeCascade_read_preserved_of_base _ _ constructorLiteralMem_size
    (by simp only [WindowDisjointFromWrites]; native_decide)]
  exact constructorLiteralMem_read64

theorem constructorDomainDataMem_eq (typeHash thisWord : UInt256) :
    constructorDomainDataMem typeHash thisWord = constructorLiteralMem ++ ffi.ByteArray.zeroes 32 ++
      typeHash.toByteArray ++ constructorNameHashWord.toByteArray ++
      constructorVersionHashWord.toByteArray ++ (⟨1⟩ : UInt256).toByteArray ++
      thisWord.toByteArray := by
  simp only [constructorDomainDataMem, writeCascade, Reasoning.Theory.writeWord]
  rw [toByteArray_write_eq _ _ 288
    (by rw [constructorLiteralMem_size]; decide)
    (by rw [constructorLiteralMem_size]; native_decide)]
  rw [toByteArray_write_eq _ _ 320
    (by simp only [ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size,
      constructorLiteralMem_size]; decide)
    (by simp only [ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size,
      constructorLiteralMem_size]; native_decide)]
  rw [toByteArray_write_eq _ _ 352
    (by simp only [ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size,
      constructorLiteralMem_size]; decide)
    (by simp only [ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size,
      constructorLiteralMem_size]; native_decide)]
  rw [toByteArray_write_eq _ _ 384
    (by simp only [ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size,
      constructorLiteralMem_size]; decide)
    (by simp only [ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size,
      constructorLiteralMem_size]; native_decide)]
  rw [toByteArray_write_eq _ _ 416
    (by simp only [ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size,
      constructorLiteralMem_size]; decide)
    (by simp only [ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size,
      constructorLiteralMem_size]; native_decide)]
  simp only [ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size,
    constructorLiteralMem_size]
  change _ ++ ffi.ByteArray.zeroes 0 ++ thisWord.toByteArray = _
  simp only [show ffi.ByteArray.zeroes 0 = ByteArray.empty by native_decide, ByteArray.append_empty]

def constructorDomainBytes (typeHash thisWord : UInt256) : ByteArray :=
  typeHash.toByteArray ++ constructorNameHashWord.toByteArray ++
    constructorVersionHashWord.toByteArray ++
    (⟨1⟩ : UInt256).toByteArray ++ thisWord.toByteArray

theorem constructorDomainDataMem_read288 (typeHash thisWord : UInt256) :
    (constructorDomainDataMem typeHash thisWord).readWithPadding 288 160 =
      constructorDomainBytes typeHash thisWord := by
  rw [readWithPadding_eq_extract' _ _ _ (by decide) (by decide)
    (by rw [constructorDomainDataMem_size]),
    constructorDomainDataMem_eq]
  have hs : (constructorLiteralMem ++ ffi.ByteArray.zeroes 32).size = 288 := by
    rw [ByteArray.size_append, constructorLiteralMem_size, ByteArray_zeroes_size]
  have hb : (constructorDomainBytes typeHash thisWord).size = 160 := by
    simp only [constructorDomainBytes, ByteArray.size_append, toByteArray_size]
  have h := extract_append_right (constructorLiteralMem ++ ffi.ByteArray.zeroes 32)
    (constructorDomainBytes typeHash thisWord)
  rw [hs, hb] at h
  simpa only [constructorDomainBytes, ByteArray.append_assoc] using h

noncomputable def constructorDomainMem (typeHash thisWord : UInt256) : ByteArray :=
  writeCascade (constructorDomainDataMem typeHash thisWord) [(256, ⟨160⟩), (64, ⟨448⟩)]

theorem constructorDomainMem_size (typeHash thisWord : UInt256) :
    (constructorDomainMem typeHash thisWord).size = 448 := by
  apply writeCascade_size_of_base _ _ (constructorDomainDataMem_size typeHash thisWord)
  · simp only [WriteGapsOk]; native_decide
  · rfl

theorem constructorDomainMem_read288 (typeHash thisWord : UInt256) :
    (constructorDomainMem typeHash thisWord).readWithPadding 288 160 =
      constructorDomainBytes typeHash thisWord := by
  unfold constructorDomainMem
  rw [writeCascade_read_preserved_len _ _ _ _
    (by rw [constructorDomainDataMem_size]; simp only [WindowDisjointFromWrites]; native_decide)
    (by decide) (by decide)]
  exact constructorDomainDataMem_read288 typeHash thisWord

theorem constructorDomainMem_read256 (typeHash thisWord : UInt256) :
    (constructorDomainMem typeHash thisWord).readWithPadding 256 32 =
      (⟨160⟩ : UInt256).toByteArray := by
  exact writeCascade_read_word_of_head_of_base _ _ _
    (constructorDomainDataMem_size typeHash thisWord)
    (by native_decide) (by simp only [WindowDisjointFromWrites]; native_decide)

end UniswapV2Pair
