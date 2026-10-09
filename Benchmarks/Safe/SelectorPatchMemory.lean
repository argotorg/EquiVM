import Benchmarks.Safe.ByteCopy
import Benchmarks.Safe.MemoryBytesDecoded

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: replace a word's first four bytes, preserving its remaining 28 bytes.
def replaceSelectorWord (old selector : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.ofNat (2 ^ 224 - 1)))
    (UInt256.land (UInt256.ofNat (2 ^ 256 - 2 ^ 224)) selector)

theorem replaceSelectorWord_toNat (old selector : UInt256) :
    (replaceSelectorWord old selector).toNat =
      old.toNat % 2 ^ 224 + selector.toNat / 2 ^ 224 * 2 ^ 224 := by
  have hlo : old.toNat % 2 ^ 224 < 2 ^ 224 := Nat.mod_lt _ (by decide)
  have hhi : selector.toNat < 2 ^ 256 := selector.val.isLt
  have hb : old.toNat % 2 ^ 224 + selector.toNat / 2 ^ 224 * 2 ^ 224 < UInt256.size := by
    change _ < 2 ^ 256
    omega
  rw [replaceSelectorWord, u256_lor_toNat, u256_land_high_mask_toNat _ 224 (by decide),
    u256_land_toNat, ulit_toNat' (2 ^ 224 - 1) (by decide), nat_land_mask_eq_mod,
    Nat.mod_eq_of_lt (show old.toNat % 2 ^ 224 < UInt256.size by
      change _ < 2 ^ 256; omega), nat_lor_shift_add _ _ _ hlo, Nat.mod_eq_of_lt hb]

theorem replaceSelectorWord_bytes (old selector : UInt256) :
    (replaceSelectorWord old selector).toByteArray =
      selector.toByteArray.extract 0 4 ++ old.toByteArray.extract 4 32 := by
  have hbytes : EVM.Word.toBytesBE (replaceSelectorWord old selector) =
      (selector.toByteArray.extract 0 4 ++ old.toByteArray.extract 4 32).toList := by
    apply fromBytesBigEndian_inj_of_length
    · rw [word_toBytesBE_length_32, byteArray_toList_eq, Array.length_toList]
      change 32 = (selector.toByteArray.extract 0 4 ++ old.toByteArray.extract 4 32).size
      simp only [ByteArray.size_append, ByteArray.size_extract, toByteArray_size]
      rfl
    · rw [fromBytesBE_word, replaceSelectorWord_toNat]
      change _ = fromByteArrayBigEndian _
      rw [fromByteArrayBigEndian_append, fromByteArrayBigEndian_toByteArray_extract4_32,
        fromByteArrayBigEndian_toByteArray_extract0_4]
      simp only [ByteArray.size_extract, toByteArray_size]
      change _ + _ * 2 ^ 224 = _ * 2 ^ 224 + _
      omega
  rw [toByteArray_eq_toBytesBE, hbytes]
  exact byteArray_mk_toArray_eq_toByteArray _ |>.trans (byteArray_toList_toByteArray _)

-- LIBRARY CANDIDATE: a masked selector MSTORE is a four-byte prefix copy into existing memory.
theorem replaceSelectorStore (mem : ByteArray) (dst : Nat) (old selector : UInt256)
    (hin : dst + 32 ≤ mem.size)
    (hread : old.toByteArray = mem.readWithPadding dst 32) :
    writeWord mem dst (replaceSelectorWord old selector) =
      selector.toByteArray.write 0 mem dst 4 := by
  have hread' : old.toByteArray = mem.extract dst (dst + 32) :=
    hread.trans (readWithPadding_eq_extract mem dst hin)
  have hs : (selector.toByteArray.extract 0 4).size = 4 := by simp
  unfold Reasoning.Theory.writeWord
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    replaceSelectorWord_bytes, hread', extract_extract_BA]
  simp only [Nat.add_zero, show min (dst + 32) (dst + 32) = dst + 32 from min_self _]
  rw [show (selector.toByteArray.extract 0 4 ++ mem.extract (dst + 4) (dst + 32)).extract
      0 32 = selector.toByteArray.extract 0 4 ++ mem.extract (dst + 4) (dst + 32) by
        have hsize : (selector.toByteArray.extract 0 4 ++
            mem.extract (dst + 4) (dst + 32)).size = 32 := by
          simp only [ByteArray.size_append, hs, ByteArray.size_extract]
          omega
        simpa only [hsize] using byteArray_extract_self
          (selector.toByteArray.extract 0 4 ++ mem.extract (dst + 4) (dst + 32))]
  rw [ByteArray.append_assoc, ByteArray.append_assoc,
    ByteArray.extract_append_extract, Nat.min_eq_left (by omega), Nat.max_eq_right hin,
    copyWindow_eq _ _ _ _ _ (by decide) (by simp) (by omega)]
  simp only [Nat.zero_add, ByteArray.append_assoc]

end Benchmarks.Safe
