import Examples.UniswapV2Pair.SkimCommon
import Reasoning.MemCascade
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
set_option maxRecDepth 2000000

namespace UniswapV2Pair

-- LIBRARY CANDIDATE: Reasoning/
theorem safeTransferCalldata_write32_size_of_le
    (base : ByteArray) (word : UInt256) (off baseSize finalSize : Nat)
    (hbase : base.size = baseSize) (hoff : off ≤ base.size)
    (hfinal : max baseSize (off + 32) = finalSize) :
    ((UInt256.toByteArray word).write 0 base off 32).size = finalSize := by
  rw [write32_eq _ _ off (by rw [toByteArray_size]) hoff, ByteArray.size_append,
    ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, hbase, toByteArray_size]
  rw [← hfinal]; omega

-- LIBRARY CANDIDATE: Reasoning/
theorem safeTransferCalldata_toByteArray_write_size_of_ge
    (base : ByteArray) (word : UInt256) (off baseSize finalSize : Nat)
    (hbase : base.size = baseSize) (hoff : baseSize ≤ off)
    (hgap : off - baseSize < USize.size) (hfinal : off + 32 = finalSize) :
    ((UInt256.toByteArray word).write 0 base off 32).size = finalSize := by
  rw [toByteArray_write_eq word base off (by rw [hbase]; exact hoff) (by rwa [hbase]),
    ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
    hbase, USize.toNat_ofNat_of_lt' hgap, toByteArray_size]
  omega

-- LIBRARY CANDIDATE: Reasoning/
theorem safeTransferCalldata_writeCascade_size
    (base : ByteArray) (writes : List (Nat × UInt256)) (baseSize finalSize : Nat)
    (hbase : base.size = baseSize) (hgaps : WriteGapsOk base.size writes)
    (hwritesSize : writeCascadeSize baseSize writes = finalSize) :
    (writeCascade base writes).size = finalSize := by
  rw [writeCascade_size base writes hgaps, hbase]
  exact hwritesSize

-- LIBRARY CANDIDATE: Reasoning/
theorem safeTransferCalldata_write32_read_back
    (base : ByteArray) (word : UInt256) (off : Nat) (hoff : off ≤ base.size) :
    ((UInt256.toByteArray word).write 0 base off 32).readWithPadding off 32 =
      UInt256.toByteArray word := by
  rw [write32_read_back _ _ off (by rw [toByteArray_size]) hoff]
  rw [toByteArray_extract_all]

-- LIBRARY CANDIDATE: Reasoning/
theorem safeTransferCalldata_mload_as_read_of_size
    (mem : ByteArray) (aw off : UInt256) (memSize : Nat)
    (hsize : mem.size = memSize) (hmem : off.toNat < memSize)
    (haw : ¬ off ≥ aw * ⟨32⟩) :
    (if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off.toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off.toNat 32)) := by
  rw [if_neg (not_or.mpr ⟨by rw [hsize]; omega, haw⟩)]

-- LIBRARY CANDIDATE: Reasoning/
theorem safeTransferCalldata_read_boundary_word
    (mem : ByteArray) (leftWord rightWord : UInt256) (writeOff : Nat)
    (hlo : 4 ≤ writeOff) (hmem : mem.size = writeOff)
    (hleft :
      mem.readWithPadding (writeOff - 4) 4 =
        (UInt256.toByteArray leftWord).extract 28 32) :
    ((UInt256.toByteArray rightWord).write 0 mem writeOff 32).readWithPadding
        (writeOff - 4) 32 =
      (UInt256.toByteArray leftWord).extract 28 32 ++
        (UInt256.toByteArray rightWord).extract 0 28 := by
  let out := (UInt256.toByteArray rightWord).write 0 mem writeOff 32
  have hsize : out.size = writeOff + 32 := by
    dsimp [out]
    exact safeTransferCalldata_toByteArray_write_size_of_ge mem rightWord writeOff writeOff
      (writeOff + 32) hmem (by omega)
      (by rw [Nat.sub_self]; exact lt_usize 0 (by norm_num)) rfl
  have hleftExtract :
      out.extract (writeOff - 4) writeOff =
        (UInt256.toByteArray leftWord).extract 28 32 := by
    rw [show out.extract (writeOff - 4) writeOff =
        out.extract (writeOff - 4) ((writeOff - 4) + 4) by
      rw [show (writeOff - 4) + 4 = writeOff by omega]]
    rw [← readWithPadding_eq_extract' out (writeOff - 4) 4 (by norm_num) (by norm_num)
      (by rw [hsize]; omega)]
    dsimp [out]
    rw [write32_read_below_len _ _ writeOff (writeOff - 4) 4 (by rw [toByteArray_size])
      (by rw [hmem]) (by omega) (by rw [hmem]; omega) (by norm_num) (by norm_num)]
    exact hleft
  have hrightExtract :
      out.extract writeOff (writeOff + 28) =
        (UInt256.toByteArray rightWord).extract 0 28 := by
    rw [← readWithPadding_eq_extract' out writeOff 28 (by norm_num) (by norm_num)
      (by rw [hsize]; omega)]
    dsimp [out]
    exact toByteArray_write_read_window_of_gap rightWord mem writeOff 0 28
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [hmem, Nat.sub_self]; exact lt_usize 0 (by norm_num))
  rw [readWithPadding_eq_extract' out (writeOff - 4) 32 (by norm_num) (by norm_num)
    (by rw [hsize]; omega)]
  rw [show (writeOff - 4) + 32 = writeOff + 28 by omega]
  rw [show out.extract (writeOff - 4) (writeOff + 28) =
      out.extract (writeOff - 4) writeOff ++ out.extract writeOff (writeOff + 28) by
    rw [ByteArray.extract_append_extract]
    congr <;> omega]
  rw [hleftExtract, hrightExtract]
end UniswapV2Pair
