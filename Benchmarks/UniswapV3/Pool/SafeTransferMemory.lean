import Benchmarks.UniswapV3.Pool.SafeTransferSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: combine a four-byte word prefix with another word's suffix.
def spliceWord4 (first rest : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land first (UInt256.lnot (UInt256.ofNat (2 ^ 224 - 1))))
    (UInt256.land rest (UInt256.ofNat (2 ^ 224 - 1)))

theorem spliceWord4_toNat (first rest : UInt256) :
    (spliceWord4 first rest).toNat =
      first.toNat / 2 ^ 224 * 2 ^ 224 + rest.toNat % 2 ^ 224 := by
  have hh : (UInt256.land first (UInt256.lnot (UInt256.ofNat (2 ^ 224 - 1)))).toNat =
      first.toNat / 2 ^ 224 * 2 ^ 224 := by
    rw [show UInt256.lnot (UInt256.ofNat (2 ^ 224 - 1)) =
      UInt256.ofNat (2 ^ 256 - 2 ^ 224) from by decide +kernel, u256_land_comm]
    exact u256_land_high_mask_toNat first 224 (by decide)
  have hl : (UInt256.land rest (UInt256.ofNat (2 ^ 224 - 1))).toNat =
      rest.toNat % 2 ^ 224 := by
    rw [uland_toNat, ulit_toNat' _ (by decide)]
    exact nat_land_mask_eq_mod _ _
  rw [spliceWord4, u256_lor_toNat_exact, hh, hl]
  change Nat.lor _ _ = _
  rw [nat_lor_comm, nat_lor_shift_add _ _ _ (Nat.mod_lt _ (by positivity)), Nat.add_comm]

theorem spliceWord4_toByteArray (first rest : UInt256) :
    (spliceWord4 first rest).toByteArray =
      first.toByteArray.extract 0 4 ++ rest.toByteArray.extract 4 32 := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [← byteArray_toList_eq, ← byteArray_toList_eq]
  apply fromBytesBigEndian_inj_of_length
  · simp only [byteArray_toList_eq, Array.length_toList]
    change (spliceWord4 first rest).toByteArray.size = (_ : ByteArray).size
    simp only [ByteArray.size_append, ByteArray.size_extract, toByteArray_size]
    decide
  · change fromByteArrayBigEndian _ = fromByteArrayBigEndian _
    rw [fromByteArrayBigEndian_toByteArray, spliceWord4_toNat,
      fromByteArrayBigEndian_append, fromByteArrayBigEndian_toByteArray_extract0_4,
      fromByteArrayBigEndian_toByteArray_extract4_32, ByteArray.size_extract, toByteArray_size]
    norm_num

theorem spliceWord4_prefix (first rest : UInt256) :
    (spliceWord4 first rest).toByteArray.extract 0 4 = first.toByteArray.extract 0 4 := by
  rw [spliceWord4_toByteArray, extract_append_left _ _ _ _ (by
    rw [ByteArray.size_extract, toByteArray_size]; decide)]
  rw [extract_extract_BA]
  rfl

theorem memLoad_toByteArray_window (mem : ByteArray) (off : UInt256) (start len : Nat)
    (hfull : off.toNat + 32 ≤ mem.size) (hwithin : start + len ≤ 32) (hpos : 0 < len) :
    (memLoad off mem).toByteArray.extract start (start + len) =
      mem.readWithPadding (off.toNat + start) len := by
  rw [memLoad, if_neg (by omega)]
  exact toByteArray_readWord_extract mem off.toNat start len hfull hwithin hpos

theorem memLoad_toByteArray (mem : ByteArray) (off : UInt256)
    (hfull : off.toNat + 32 ≤ mem.size) :
    (memLoad off mem).toByteArray = mem.readWithPadding off.toNat 32 := by
  simpa only [Nat.add_zero, Nat.zero_add, toByteArray_extract_all] using
    memLoad_toByteArray_window mem off 0 32 hfull (by decide) (by decide)

theorem safeTransferSelectorPatch (old : UInt256) :
    (UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 2835717307) ⟨224⟩)
      (UInt256.land (UInt256.ofNat (2 ^ 224 - 1)) old)).toByteArray =
      selectorBytes 0xa9 0x05 0x9c 0xbb ++ old.toByteArray.extract 4 32 := by
  have hmask : UInt256.land (UInt256.shiftLeft (UInt256.ofNat 2835717307) ⟨224⟩)
      (UInt256.lnot (UInt256.ofNat (2 ^ 224 - 1))) =
      UInt256.shiftLeft (UInt256.ofNat 2835717307) ⟨224⟩ := by decide +kernel
  have hs := spliceWord4_toByteArray (UInt256.shiftLeft (UInt256.ofNat 2835717307) ⟨224⟩) old
  rw [spliceWord4, hmask, u256_land_comm old] at hs
  rw [hs]
  exact congrArg (fun x : ByteArray ↦ x ++ old.toByteArray.extract 4 32) (by decide +kernel)

-- LIBRARY CANDIDATE: arbitrary-size sparse word stores preserve disjoint byte windows.
theorem writeWord_sparse_read_preserved_len (mem : ByteArray) (off read len : Nat)
    (word : UInt256)
    (hdisj : (read + len ≤ off ∧ read + len ≤ mem.size) ∨
      (off + 32 ≤ read ∧ read + len ≤ mem.size))
    (hpos : 0 < len) (hlen : len < 2 ^ 64) :
    (writeWord mem off word).readWithPadding read len = mem.readWithPadding read len := by
  by_cases hle : off ≤ mem.size
  · exact writeWord_read_preserved_len mem off read len word
      (by have hu := lt_usize 0 (by decide); omega) hdisj hpos hlen
  · have hin := hdisj.elim And.right And.right
    rw [writeWord_sparse_eq mem off word (by omega)]
    rw [readWithPadding_eq_extract' _ read len hpos hlen (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, ByteArray_zeroes_size]; omega), extract_append_left _ _ _ _ hin]
    exact (readWithPadding_eq_extract' mem read len hpos hlen hin).symm

def transferSelectorPatchedWord (old : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 2835717307) ⟨224⟩)
    (UInt256.land (UInt256.ofNat (2 ^ 224 - 1)) old)

theorem transferSelectorPatch_read (mem : ByteArray) (p : UInt256) (recipientWord value : UInt256)
    (hbound : p.toNat + 100 < UInt256.size) (hmem : p.toNat + 100 ≤ mem.size)
    (hto : mem.readWithPadding (p.toNat + 36) 32 = recipientWord.toByteArray)
    (hvalue : mem.readWithPadding (p.toNat + 68) 32 = value.toByteArray) :
    (writeWord mem (p.toNat + 32) (transferSelectorPatchedWord (memLoad (p + ⟨32⟩) mem))).readWithPadding (p.toNat + 32) 68 =
      selectorBytes 0xa9 0x05 0x9c 0xbb ++ recipientWord.toByteArray ++ value.toByteArray := by
  have hp32 : (p + (⟨32⟩ : UInt256)).toNat = p.toNat + 32 :=
    uadd_word_ofNat_toNat p 32 (by omega)
  have hsize := writeWord_sparse_size mem (p.toNat + 32)
    (transferSelectorPatchedWord (memLoad (p + ⟨32⟩) mem))
  rw [show 68 = 32 + 36 from rfl, byteArray_readWithPadding_split _ _ 32 36
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega),
    writeWord_sparse_read_back, transferSelectorPatchedWord, safeTransferSelectorPatch]
  rw [memLoad_toByteArray_window mem (p + ⟨32⟩) 4 28 (by rw [hp32]; omega)
    (by decide) (by decide), hp32]
  rw [writeWord_sparse_read_preserved_len _ _ _ 36 _
    (Or.inr ⟨by omega, by omega⟩) (by decide) (by decide)]
  rw [show p.toNat + 32 + 4 = p.toNat + 36 by omega,
    show p.toNat + 32 + 32 = p.toNat + 64 by omega, ByteArray.append_assoc]
  rw [show p.toNat + 64 = (p.toNat + 36) + 28 by omega,
    ← byteArray_readWithPadding_split mem (p.toNat + 36) 28 36
      (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 28 + 36 = 32 + 32 from rfl, byteArray_readWithPadding_split mem (p.toNat + 36) 32 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show p.toNat + 36 + 32 = p.toNat + 68 by omega, hto, hvalue, ByteArray.append_assoc]

end Benchmarks.UniswapV3.Pool
