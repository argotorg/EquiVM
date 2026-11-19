import Benchmarks.Midnight.CollateralDecode
import Benchmarks.Midnight.CalldataWordCopies

/-! Collateral decoding is unchanged by copying the bounded input region. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES Reasoning.Theory.calldataWord_extract_zero to a word within the slice.
theorem calldataWord_extract {bytes : ByteArray} {start finish off : Nat}
    (hword : start + off + 32 ≤ finish) (hfinish : finish ≤ bytes.size) :
    calldataWord (bytes.extract start finish) off = calldataWord bytes (start + off) := by
  have hlen : off + 32 ≤ (bytes.extract start finish).size := by
    rw [ByteArray.size_extract]
    omega
  have hw : bytesToWord (((bytes.extract start finish).toList.drop off).take 32) =
      calldataWord (bytes.extract start finish) off :=
    decode_word_at_eq_any (bytes.extract start finish) off hlen
  rw [← hw]
  rw [extract_toList, List.drop_take, List.drop_drop, List.take_take]
  have hm : min 32 (finish - start - off) = 32 := Nat.min_eq_left (by omega)
  rw [hm, decode_word_at_eq_any bytes (start + off) (by omega)]

theorem CollateralData.at_extract {bytes : ByteArray} {start finish off : Nat}
    (hword : start + off + 128 ≤ finish) (hfinish : finish ≤ bytes.size) :
    CollateralData.at (bytes.extract start finish) off =
      CollateralData.at bytes (start + off) := by
  simp only [CollateralData.at,
    calldataWord_extract (start := start) (off := off) (by omega) hfinish,
    calldataWord_extract (start := start) (off := off + 32) (by omega) hfinish,
    calldataWord_extract (start := start) (off := off + 64) (by omega) hfinish,
    calldataWord_extract (start := start) (off := off + 96) (by omega) hfinish, Nat.add_assoc]

theorem CollateralData.canonicalAt_extract {bytes : ByteArray} {start finish off : Nat}
    (hword : start + off + 128 ≤ finish) (hfinish : finish ≤ bytes.size) :
    CollateralData.canonicalAt (bytes.extract start finish) off ↔
      CollateralData.canonicalAt bytes (start + off) := by
  simp only [CollateralData.canonicalAt,
    calldataWord_extract (start := start) (off := off) (by omega) hfinish,
    calldataWord_extract (start := start) (off := off + 96) (by omega) hfinish, Nat.add_assoc]

theorem decodeCollateralElements_extract {bytes : ByteArray} {start finish off n : Nat}
    (hbound : start + off + 128 * n ≤ finish) (hfinish : finish ≤ bytes.size) :
    decodeCollateralElements n (bytes.extract start finish) off =
      decodeCollateralElements n bytes (start + off) := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih =>
    have hx : off + 128 ≤ (bytes.extract start finish).size := by
      rw [ByteArray.size_extract]
      omega
    have hb : start + off + 128 ≤ bytes.size := by omega
    simp only [decodeCollateralElements, hx, hb, true_and,
      CollateralData.canonicalAt_extract (start := start) (off := off) (by omega) hfinish,
      CollateralData.at_extract (start := start) (off := off) (by omega) hfinish]
    rw [ih (by omega), Nat.add_assoc]

theorem decodeCollateralWords {bytes : ByteArray} {start n : Nat}
    (hbound : start + 128 * n ≤ bytes.size) (hsize : bytes.size < EVM.wordModulus) :
    ABI.decodeABIArrayStaticElems? Model.collateralABI n 128
        (ABI.Solc08Calldata.solcReadWords bytes.toList start (4 * n)) 0 =
      (decodeCollateralElements n bytes start).map
        (fun values ↦ (values.map CollateralData.value, 128 * n)) := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  rw [solcReadWords_bounded (by rw [hl]; omega) (by rw [hl]; exact hsize)]
  have he : (bytes.toList.drop start).take (32 * (4 * n)) =
      (bytes.extract start (start + 128 * n)).toList := by
    rw [extract_toList]
    congr 1
    omega
  rw [he, decodeCollateralElements_eq, decodeCollateralElements_extract (by omega) hbound]
  simp only [Nat.add_zero, Nat.zero_add]

end Benchmarks.Midnight
