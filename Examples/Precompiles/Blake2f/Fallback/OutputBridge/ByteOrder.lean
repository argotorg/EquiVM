import Examples.Precompiles.Blake2f.Fallback.OutputBridge.UInt256BitVec

/-!
# BLAKE2F byte-order bridge facts

This module factors the remaining zero-round byte-normal-form bridge into chunk-level obligations.
The fixed IV/final-flag chunks are discharged by computation; only the symbolic `t0`/`t1` chunks
need parser/endianness proofs.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

def bytecodeWordChunk (w : UInt256) : ByteArray :=
  returnWordBytes (UInt256.shiftLeft (evmSwap64 w) ⟨192⟩)

def modelWordChunk (w : UInt64) : ByteArray :=
  Model.writeLE64 ByteArray.empty w

theorem returnWordBytes_toList (w : UInt256) :
    (returnWordBytes w).data.toList =
      [UInt8.ofNat (w.toNat >>> 248),
       UInt8.ofNat (w.toNat >>> 240),
       UInt8.ofNat (w.toNat >>> 232),
       UInt8.ofNat (w.toNat >>> 224),
       UInt8.ofNat (w.toNat >>> 216),
       UInt8.ofNat (w.toNat >>> 208),
       UInt8.ofNat (w.toNat >>> 200),
       UInt8.ofNat (w.toNat >>> 192)] := by
  unfold returnWordBytes
  rw [toByteArray_eq_toBytesBE]
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  simp only [List.drop_zero]
  have h0 := word_toBytesBE_getD w 0 (by decide)
  have h1 := word_toBytesBE_getD w 1 (by decide)
  have h2 := word_toBytesBE_getD w 2 (by decide)
  have h3 := word_toBytesBE_getD w 3 (by decide)
  have h4 := word_toBytesBE_getD w 4 (by decide)
  have h5 := word_toBytesBE_getD w 5 (by decide)
  have h6 := word_toBytesBE_getD w 6 (by decide)
  have h7 := word_toBytesBE_getD w 7 (by decide)
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    rw [word_toBytesBE_reverse, List.length_reverse]
    unfold EVM.Word.toBytesLE
    have _hb := Ethereum.toBytes'_le (k := 32) w.val.isLt
    simp
    omega
  apply List.ext_getElem
  · rw [List.length_take, hlen]
    norm_num
  · intro i h₁ h₂
    have hi : i < 8 := by
      simpa using h₂
    rw [List.getElem_take]
    interval_cases i
    · rw [← List.getD_eq_getElem (EVM.Word.toBytesBE w) (0 : UInt8) (by rw [hlen]; decide)]
      simpa using h0
    · rw [← List.getD_eq_getElem (EVM.Word.toBytesBE w) (0 : UInt8) (by rw [hlen]; decide)]
      simpa using h1
    · rw [← List.getD_eq_getElem (EVM.Word.toBytesBE w) (0 : UInt8) (by rw [hlen]; decide)]
      simpa using h2
    · rw [← List.getD_eq_getElem (EVM.Word.toBytesBE w) (0 : UInt8) (by rw [hlen]; decide)]
      simpa using h3
    · rw [← List.getD_eq_getElem (EVM.Word.toBytesBE w) (0 : UInt8) (by rw [hlen]; decide)]
      simpa using h4
    · rw [← List.getD_eq_getElem (EVM.Word.toBytesBE w) (0 : UInt8) (by rw [hlen]; decide)]
      simpa using h5
    · rw [← List.getD_eq_getElem (EVM.Word.toBytesBE w) (0 : UInt8) (by rw [hlen]; decide)]
      simpa using h6
    · rw [← List.getD_eq_getElem (EVM.Word.toBytesBE w) (0 : UInt8) (by rw [hlen]; decide)]
      simpa using h7

theorem modelWordChunk_toList (w : UInt64) :
    (modelWordChunk w).data.toList =
      [UInt8.ofNat (w.toNat >>> 0),
       UInt8.ofNat (w.toNat >>> 8),
       UInt8.ofNat (w.toNat >>> 16),
       UInt8.ofNat (w.toNat >>> 24),
       UInt8.ofNat (w.toNat >>> 32),
       UInt8.ofNat (w.toNat >>> 40),
       UInt8.ofNat (w.toNat >>> 48),
       UInt8.ofNat (w.toNat >>> 56)] := by
  have u8_mask255 (x : UInt8) : x &&& (255 : UInt8) = x := by
    cases x with
    | ofBitVec xb =>
      apply UInt8.eq_of_toBitVec_eq
      simp
      bv_decide
  cases w with
  | ofBitVec wb =>
    simp [modelWordChunk, Model.writeLE64, List.range', u8_mask255]
    repeat constructor <;> first | rfl | (rw [← UInt8.toNat_inj]; simp [UInt8.ofNat])

private theorem u256bv_shiftLeft_evmSwap64_of_u64 (wb : BitVec 64) :
    u256bv (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩) =
      (bvSwap64In256 (BitVec.setWidth 256 wb)) <<< 192 := by
  rw [show (⟨192⟩ : UInt256) = UInt256.ofNat 192 by native_decide]
  rw [u256bv_shl _ 192 (by decide)]
  rw [u256bv_evmSwap64]
  rw [u256bv_ofNat]
  rw [bitvec_ofNat_toNat_eq_setWidth]

private theorem swapped_shifted_extract0 (wb : BitVec 64) :
    BitVec.extractLsb' 248 8 ((bvSwap64In256 (BitVec.setWidth 256 wb)) <<< 192) =
      BitVec.extractLsb' 0 8 wb := by
  unfold bvSwap64In256 swapStep32B swapStep16B swapStep8B
  bv_decide

private theorem swapped_shifted_extract1 (wb : BitVec 64) :
    BitVec.extractLsb' 240 8 ((bvSwap64In256 (BitVec.setWidth 256 wb)) <<< 192) =
      BitVec.extractLsb' 8 8 wb := by
  unfold bvSwap64In256 swapStep32B swapStep16B swapStep8B
  bv_decide

private theorem swapped_shifted_extract2 (wb : BitVec 64) :
    BitVec.extractLsb' 232 8 ((bvSwap64In256 (BitVec.setWidth 256 wb)) <<< 192) =
      BitVec.extractLsb' 16 8 wb := by
  unfold bvSwap64In256 swapStep32B swapStep16B swapStep8B
  bv_decide

private theorem swapped_shifted_extract3 (wb : BitVec 64) :
    BitVec.extractLsb' 224 8 ((bvSwap64In256 (BitVec.setWidth 256 wb)) <<< 192) =
      BitVec.extractLsb' 24 8 wb := by
  unfold bvSwap64In256 swapStep32B swapStep16B swapStep8B
  bv_decide

private theorem swapped_shifted_extract4 (wb : BitVec 64) :
    BitVec.extractLsb' 216 8 ((bvSwap64In256 (BitVec.setWidth 256 wb)) <<< 192) =
      BitVec.extractLsb' 32 8 wb := by
  unfold bvSwap64In256 swapStep32B swapStep16B swapStep8B
  bv_decide

private theorem swapped_shifted_extract5 (wb : BitVec 64) :
    BitVec.extractLsb' 208 8 ((bvSwap64In256 (BitVec.setWidth 256 wb)) <<< 192) =
      BitVec.extractLsb' 40 8 wb := by
  unfold bvSwap64In256 swapStep32B swapStep16B swapStep8B
  bv_decide

private theorem swapped_shifted_extract6 (wb : BitVec 64) :
    BitVec.extractLsb' 200 8 ((bvSwap64In256 (BitVec.setWidth 256 wb)) <<< 192) =
      BitVec.extractLsb' 48 8 wb := by
  unfold bvSwap64In256 swapStep32B swapStep16B swapStep8B
  bv_decide

private theorem swapped_shifted_extract7 (wb : BitVec 64) :
    BitVec.extractLsb' 192 8 ((bvSwap64In256 (BitVec.setWidth 256 wb)) <<< 192) =
      BitVec.extractLsb' 56 8 wb := by
  unfold bvSwap64In256 swapStep32B swapStep16B swapStep8B
  bv_decide

private theorem bytecodeWordChunk_u64_byte0 (wb : BitVec 64) :
    UInt8.ofNat ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat (UInt64.ofBitVec wb).toNat))
        ⟨192⟩).toNat >>> 248) =
      UInt8.ofNat ((UInt64.ofBitVec wb).toNat >>> 0) := by
  apply UInt8.eq_of_toBitVec_eq
  simp [UInt8.ofNat]
  rw [show ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩).toNat) =
      (u256bv (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩)).toNat by
    rw [u256bv_toNat]]
  rw [bitvec_ofNat_shiftRight_to_extract_256]
  rw [u256bv_shiftLeft_evmSwap64_of_u64]
  rw [show BitVec.setWidth 8 wb = BitVec.extractLsb' 0 8 wb by rfl]
  exact swapped_shifted_extract0 wb

private theorem bytecodeWordChunk_u64_byte1 (wb : BitVec 64) :
    UInt8.ofNat ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat (UInt64.ofBitVec wb).toNat))
        ⟨192⟩).toNat >>> 240) =
      UInt8.ofNat ((UInt64.ofBitVec wb).toNat >>> 8) := by
  apply UInt8.eq_of_toBitVec_eq
  simp [UInt8.ofNat]
  rw [show ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩).toNat) =
      (u256bv (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩)).toNat by
    rw [u256bv_toNat]]
  rw [bitvec_ofNat_shiftRight_to_extract_256]
  rw [bitvec_ofNat_shiftRight_to_extract_64]
  rw [u256bv_shiftLeft_evmSwap64_of_u64]
  exact swapped_shifted_extract1 wb

private theorem bytecodeWordChunk_u64_byte2 (wb : BitVec 64) :
    UInt8.ofNat ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat (UInt64.ofBitVec wb).toNat))
        ⟨192⟩).toNat >>> 232) =
      UInt8.ofNat ((UInt64.ofBitVec wb).toNat >>> 16) := by
  apply UInt8.eq_of_toBitVec_eq
  simp [UInt8.ofNat]
  rw [show ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩).toNat) =
      (u256bv (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩)).toNat by
    rw [u256bv_toNat]]
  rw [bitvec_ofNat_shiftRight_to_extract_256]
  rw [bitvec_ofNat_shiftRight_to_extract_64]
  rw [u256bv_shiftLeft_evmSwap64_of_u64]
  exact swapped_shifted_extract2 wb

private theorem bytecodeWordChunk_u64_byte3 (wb : BitVec 64) :
    UInt8.ofNat ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat (UInt64.ofBitVec wb).toNat))
        ⟨192⟩).toNat >>> 224) =
      UInt8.ofNat ((UInt64.ofBitVec wb).toNat >>> 24) := by
  apply UInt8.eq_of_toBitVec_eq
  simp [UInt8.ofNat]
  rw [show ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩).toNat) =
      (u256bv (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩)).toNat by
    rw [u256bv_toNat]]
  rw [bitvec_ofNat_shiftRight_to_extract_256]
  rw [bitvec_ofNat_shiftRight_to_extract_64]
  rw [u256bv_shiftLeft_evmSwap64_of_u64]
  exact swapped_shifted_extract3 wb

private theorem bytecodeWordChunk_u64_byte4 (wb : BitVec 64) :
    UInt8.ofNat ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat (UInt64.ofBitVec wb).toNat))
        ⟨192⟩).toNat >>> 216) =
      UInt8.ofNat ((UInt64.ofBitVec wb).toNat >>> 32) := by
  apply UInt8.eq_of_toBitVec_eq
  simp [UInt8.ofNat]
  rw [show ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩).toNat) =
      (u256bv (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩)).toNat by
    rw [u256bv_toNat]]
  rw [bitvec_ofNat_shiftRight_to_extract_256]
  rw [bitvec_ofNat_shiftRight_to_extract_64]
  rw [u256bv_shiftLeft_evmSwap64_of_u64]
  exact swapped_shifted_extract4 wb

private theorem bytecodeWordChunk_u64_byte5 (wb : BitVec 64) :
    UInt8.ofNat ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat (UInt64.ofBitVec wb).toNat))
        ⟨192⟩).toNat >>> 208) =
      UInt8.ofNat ((UInt64.ofBitVec wb).toNat >>> 40) := by
  apply UInt8.eq_of_toBitVec_eq
  simp [UInt8.ofNat]
  rw [show ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩).toNat) =
      (u256bv (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩)).toNat by
    rw [u256bv_toNat]]
  rw [bitvec_ofNat_shiftRight_to_extract_256]
  rw [bitvec_ofNat_shiftRight_to_extract_64]
  rw [u256bv_shiftLeft_evmSwap64_of_u64]
  exact swapped_shifted_extract5 wb

private theorem bytecodeWordChunk_u64_byte6 (wb : BitVec 64) :
    UInt8.ofNat ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat (UInt64.ofBitVec wb).toNat))
        ⟨192⟩).toNat >>> 200) =
      UInt8.ofNat ((UInt64.ofBitVec wb).toNat >>> 48) := by
  apply UInt8.eq_of_toBitVec_eq
  simp [UInt8.ofNat]
  rw [show ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩).toNat) =
      (u256bv (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩)).toNat by
    rw [u256bv_toNat]]
  rw [bitvec_ofNat_shiftRight_to_extract_256]
  rw [bitvec_ofNat_shiftRight_to_extract_64]
  rw [u256bv_shiftLeft_evmSwap64_of_u64]
  exact swapped_shifted_extract6 wb

private theorem bytecodeWordChunk_u64_byte7 (wb : BitVec 64) :
    UInt8.ofNat ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat (UInt64.ofBitVec wb).toNat))
        ⟨192⟩).toNat >>> 192) =
      UInt8.ofNat ((UInt64.ofBitVec wb).toNat >>> 56) := by
  apply UInt8.eq_of_toBitVec_eq
  simp [UInt8.ofNat]
  rw [show ((UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩).toNat) =
      (u256bv (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat wb.toNat)) ⟨192⟩)).toNat by
    rw [u256bv_toNat]]
  rw [bitvec_ofNat_shiftRight_to_extract_256]
  rw [bitvec_ofNat_shiftRight_to_extract_64]
  rw [u256bv_shiftLeft_evmSwap64_of_u64]
  exact swapped_shifted_extract7 wb

theorem bytecodeWordChunk_of_u64 (w : UInt64) :
    bytecodeWordChunk (UInt256.ofNat w.toNat) = modelWordChunk w := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  unfold bytecodeWordChunk
  rw [returnWordBytes_toList, modelWordChunk_toList]
  cases w with
  | ofBitVec wb =>
    rw [bytecodeWordChunk_u64_byte0 wb]
    rw [bytecodeWordChunk_u64_byte1 wb]
    rw [bytecodeWordChunk_u64_byte2 wb]
    rw [bytecodeWordChunk_u64_byte3 wb]
    rw [bytecodeWordChunk_u64_byte4 wb]
    rw [bytecodeWordChunk_u64_byte5 wb]
    rw [bytecodeWordChunk_u64_byte6 wb]
    rw [bytecodeWordChunk_u64_byte7 wb]

theorem bytecodeWordChunk_iv0 :
    bytecodeWordChunk (UInt256.ofNat 7640891576956012808) =
      modelWordChunk (UInt64.ofNat 7640891576956012808) := by
  native_decide

theorem bytecodeWordChunk_iv1 :
    bytecodeWordChunk (UInt256.ofNat 13503953896175478587) =
      modelWordChunk (UInt64.ofNat 13503953896175478587) := by
  native_decide

theorem bytecodeWordChunk_iv2 :
    bytecodeWordChunk (UInt256.ofNat 4354685564936845355) =
      modelWordChunk (UInt64.ofNat 4354685564936845355) := by
  native_decide

theorem bytecodeWordChunk_iv3 :
    bytecodeWordChunk (UInt256.ofNat 11912009170470909681) =
      modelWordChunk (UInt64.ofNat 11912009170470909681) := by
  native_decide

theorem bytecodeWordChunk_iv6_zeroFlag :
    bytecodeWordChunk (UInt256.ofNat 2270897969802886507) =
      modelWordChunk (UInt64.ofNat 2270897969802886507) := by
  native_decide

theorem bytecodeWordChunk_iv6_oneFlag :
    bytecodeWordChunk (UInt256.ofNat 16175846103906665108) =
      modelWordChunk (UInt64.ofNat 16175846103906665108) := by
  native_decide

theorem bytecodeWordChunk_iv7 :
    bytecodeWordChunk (UInt256.ofNat 6620516959819538809) =
      modelWordChunk (UInt64.ofNat 6620516959819538809) := by
  native_decide

end Blake2f
