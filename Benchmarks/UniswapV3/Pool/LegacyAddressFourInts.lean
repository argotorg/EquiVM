import Benchmarks.UniswapV3.Pool.LegacyAddressInts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a uniform short-calldata bound for every legacy scalar tuple.
theorem decodeCalldata_legacyScalarWords_none_short {cd : ByteArray} {names : List Ident}
    {types : List ABIType} (hscalar : types.all isABIScalarWordType = true)
    (hshort : cd.size < 4 + 32 * types.length) :
    decodeCalldataWithMode .legacySolc05 names types cd = none := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq hscalar]
  split
  · rfl
  · cases hdec : decodeScalarWordsWithMode? .legacySolc05 types (cd.toList.drop 4) 0 with
    | none => rfl
    | some values =>
        have hb := decodeScalarWordsWithMode?_some_length (Nat.zero_le _) hdec
        rw [List.length_drop, htlen] at hb
        omega

-- GENERALIZES the address-and-two-integer decoder to four arbitrary integer types.
theorem decodeCalldata_legacyAddress_fourInts_ok (ty0 ty1 ty2 ty3 : ABI.IntType)
    {cd : ByteArray} {x y z u w : Ident} (hlen : 164 ≤ cd.size) :
    decodeCalldataWithMode .legacySolc05 [x, y, z, u, w]
      [abiAddress, .elem (.int ty0), .elem (.int ty1), .elem (.int ty2), .elem (.int ty3)] cd =
      some ((((((∅ : Store).insert x (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (normalizeInt ty0 (Int.ofNat (calldataWord cd 36).toNat)))).insert z
        (.int (normalizeInt ty1 (Int.ofNat (calldataWord cd 68).toNat)))).insert u
        (.int (normalizeInt ty2 (Int.ofNat (calldataWord cd 100).toNat)))).insert w
        (.int (normalizeInt ty3 (Int.ofNat (calldataWord cd 132).toNat)))) := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake (n : Nat) (hn : n ≤ 128) :
      (((cd.toList.drop 4).drop n).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have hword (n : Nat) (hn : n ≤ 128) :
      ABI.bytesToWord (((cd.toList.drop 4).drop n).take 32) = calldataWord cd (4 + n) := by
    simpa only [List.drop_drop] using decode_word_at_eq_any cd (4 + n) (by omega)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (by
    cases ty0 <;> cases ty1 <;> cases ty2 <;> cases ty3 <;> rfl),
    if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) (start := 0) (htake 0 (by decide)),
    decodeScalarWord_legacyInt_ok ty0 (htake 32 (by decide)),
    decodeScalarWord_legacyInt_ok ty1 (htake 64 (by decide)),
    decodeScalarWord_legacyInt_ok ty2 (htake 96 (by decide)),
    decodeScalarWord_legacyInt_ok ty3 (htake 128 (by decide))]
  change decodeCalldata.insertValues [x, y, z, u, w]
    [.address (AccountAddress.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 0).take 32)).toNat),
     .int (normalizeInt ty0 (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat)),
     .int (normalizeInt ty1 (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat)),
     .int (normalizeInt ty2 (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32)).toNat)),
     .int (normalizeInt ty3 (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 128).take 32)).toNat))] ∅ = _
  rw [hword 0 (by decide), hword 32 (by decide), hword 64 (by decide),
    hword 96 (by decide), hword 128 (by decide)]
  rfl

end Benchmarks.UniswapV3.Pool
