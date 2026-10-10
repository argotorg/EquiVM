import Benchmarks.Morpho.MetaMorphoV1_1.MarketABI
import Benchmarks.EAS.Attester.Memory

/-! Recover arbitrary word windows from a contiguous sequence of decoded ABI words. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: aligned loads determine the complete contiguous byte window.
theorem wordWindowRead_of_fields {mem out : ByteArray} {src : UInt256} {count : Nat}
    (hl : 32 * count ≤ out.size) (hm : src.toNat + 32 * count ≤ mem.size)
    (hfit : src.toNat + 32 * count < UInt256.size)
    (hfields : ∀ i, i < count → memLoad (src + UInt256.ofNat (32 * i)) mem =
      calldataWord out (32 * i)) :
    mem.readWithPadding src.toNat (32 * count) = out.readWithPadding 0 (32 * count) := by
  let words := List.ofFn (fun i : Fin count ↦ calldataWord out (32 * i.val))
  have hlen : words.length = count := List.length_ofFn
  have hword (i : Fin words.length) : words[i] = calldataWord out (32 * i.val) := by
    change words[i.val] = _
    simp only [words, List.getElem_ofFn]
  have hout : out.readWithPadding 0 (32 * words.length) =
      (words.map UInt256.toByteArray).foldr (· ++ ·) ByteArray.empty :=
    readWithPadding_words out 0 words (by rw [hlen]; omega) (by
      intro i
      have hi : i.val < count := by simpa only [hlen] using i.isLt
      rw [hword i, Nat.zero_add, calldataWord_bytes_at (by omega)]
      exact readWithPadding_eq_extract _ _ (by omega))
  have hmem : mem.readWithPadding src.toNat (32 * words.length) =
      (words.map UInt256.toByteArray).foldr (· ++ ·) ByteArray.empty :=
    readWithPadding_words mem src.toNat words (by rw [hlen]; exact hm) (by
      intro i
      have hi : i.val < count := by simpa only [hlen] using i.isLt
      rw [hword i]
      apply readWord_of_memLoad _ _ _ (by omega) (by omega)
      have he : UInt256.ofNat (src.toNat + 32 * i.val) = src + UInt256.ofNat (32 * i.val) := by
        apply u256_inj
        rw [UInt256.toNat_ofNat_of_lt (by omega), uadd_word_ofNat_toNat _ _ (by omega)]
      rw [he]
      exact hfields i.val hi)
  simpa only [hlen] using hmem.trans hout.symm

-- LIBRARY CANDIDATE: a copied byte window preserves unaligned as well as aligned MLOADs.
theorem wordWindowLoad_of_read {mem out : ByteArray} {src : UInt256} {len : Nat}
    (hl : len ≤ out.size) (hm : src.toNat + len ≤ mem.size)
    (hfit : src.toNat + len < UInt256.size)
    (hread : mem.readWithPadding src.toNat len = out.readWithPadding 0 len)
    (off : Nat) (hoff : off + 32 ≤ len) :
    memLoad (src + UInt256.ofNat off) mem = calldataWord out off := by
  have hadd : (src + UInt256.ofNat off).toNat = src.toNat + off :=
    uadd_word_ofNat_toNat src off (by omega)
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) hm,
    readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by omega)] at hread
  have he := congrArg (fun bytes : ByteArray ↦ bytes.extract off (off + 32)) hread
  simp only [ByteArray.extract_extract, Nat.zero_add] at he
  rw [Nat.min_eq_left (by omega), Nat.min_eq_left hoff] at he
  apply loadedWord_of_read
  · rw [hadd]; omega
  · rw [hadd, readWithPadding_eq_extract _ _ (by omega), Nat.add_assoc, he,
      calldataWord_bytes_at (by omega)]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
