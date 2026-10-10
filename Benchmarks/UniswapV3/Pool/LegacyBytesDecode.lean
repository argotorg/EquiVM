import Benchmarks.UniswapV3.Pool.ScalarPrefixDecode
import Benchmarks.UniswapV3.Pool.LegacyScalarsBytes

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: the exact legacy dynamic-bytes decoder, with every failure branch.
theorem decodeABIValue_legacyBytes_eq (cd : ByteArray) (start : Nat) :
    decodeABIValue? abiBytes (cd.toList.drop 4) start .legacySolc05 =
      let len := (calldataWord cd (4 + start)).toNat
      if cd.size < 4 + start + 32 then none else
      if 2 ^ 32 < len then none else
      if cd.size < 4 + start + 32 + len then none else
      some (.bytes (cd.extract (4 + start + 32) (4 + start + 32 + len)),
        start + 32 + paddedSize len) := by
  dsimp only
  have htlen : (cd.toList.drop 4).length = cd.size - 4 := by
    rw [List.length_drop, byteArray_toList_eq, Array.length_toList]; rfl
  by_cases hshort : cd.size < 4 + start + 32
  · rw [if_pos hshort]
    apply decodeABIValue_legacyBytes_none_length_short
    unfold readNat? readWord? readBytes?
    rw [if_neg (by rw [List.length_take, List.length_drop, htlen]; omega)]
    rfl
  rw [if_neg hshort]
  have hr := readNat_drop4_at_eq_calldataWord (cd := cd) start (by omega)
  by_cases hhuge : 2 ^ 32 < (calldataWord cd (4 + start)).toNat
  · rw [if_pos hhuge]
    exact decodeABIValue_legacyBytes_none_length_huge hr hhuge
  rw [if_neg hhuge]
  by_cases hpayload : cd.size < 4 + start + 32 + (calldataWord cd (4 + start)).toNat
  · rw [if_pos hpayload]
    exact decodeABIValue_legacyBytes_none_payload_short hr hhuge (by
      rw [List.length_take, List.length_drop, htlen]; omega)
  rw [if_neg hpayload]
  rw [decodeABIValue_legacyBytes_ok hr hhuge (by
    rw [List.length_take, List.length_drop, htlen]; omega)]
  congr 3
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    byteArray_toList_eq, List.drop_drop, Nat.add_assoc]
  congr 1
  omega

-- LIBRARY CANDIDATE: a legacy address/uint256/uint256/bytes tuple head.
theorem decodeCalldata_legacyAddressUintUintBytes_head (cd : ByteArray) (a b c d : Ident) :
    decodeCalldataWithMode .legacySolc05 [a,b,c,d] [abiAddress,abiUInt256,abiUInt256,abiBytes] cd =
      if cd.size < 132 then none else
      if 2 ^ 32 < (calldataWord cd 100).toNat then none else
      match decodeABIValue? abiBytes (cd.toList.drop 4) (calldataWord cd 100).toNat .legacySolc05 with
      | none => none
      | some (value, _) => some (((((∅ : Store).insert a
          (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert b
          (.int (Int.ofNat (calldataWord cd 36).toNat))).insert c
          (.int (Int.ofNat (calldataWord cd 68).toNat))).insert d value) := by
  change decodeCalldataWithMode .legacySolc05 [a,b,c,d]
    ([abiAddress,abiUInt256,abiUInt256] ++ [abiBytes]) cd = _
  rw [decodeCalldata_legacyScalarsBytes_head _ _ _ (by decide)]
  by_cases hshort : cd.size < 132
  · simp only [List.length_cons, List.length_nil, if_pos hshort]
  rw [if_neg (by exact hshort), if_neg hshort]
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake (n : Nat) (hn : n ≤ 64) : (((cd.toList.drop 4).drop n).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have hword (n : Nat) (hn : n ≤ 64) :
      bytesToWord (((cd.toList.drop 4).drop n).take 32) = calldataWord cd (4 + n) := by
    rw [List.drop_drop]; exact decode_word_at_eq_any cd (4 + n) (by omega)
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyAddress_ok (htake 0 (by decide)),
    decodeScalarWordWithMode_uint256_ok (htake 32 (by decide)),
    decodeScalarWordWithMode_uint256_ok (htake 64 (by decide)),
    hword 0 (by decide), hword 32 (by decide), hword 64 (by decide)]
  simp only [bind, Option.bind, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, decodeCalldata.insertValues,
    show (4 + 0 : Nat) = 4 from rfl, show (4 + 32 : Nat) = 36 from rfl,
    show (4 + 64 : Nat) = 68 from rfl]
  rw [show (4 + 32 * (0 + 1 + 1 + 1) : Nat) = 100 from rfl]
  by_cases hoff : 2 ^ 32 < (calldataWord cd 100).toNat
  · simp only [if_pos hoff]
  simp only [if_neg hoff]
  cases decodeABIValue? abiBytes (cd.toList.drop 4) (calldataWord cd 100).toNat .legacySolc05 with
  | none => rfl
  | some result => rcases result with ⟨value, stop⟩; rfl

end Benchmarks.UniswapV3.Pool
