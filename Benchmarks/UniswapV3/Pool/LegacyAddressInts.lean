import Benchmarks.UniswapV3.Pool.Calldata

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- GENERALIZES Reasoning.ABIComposite.decodeCalldata_legacyAddress_uint256_uint256_ok.
theorem decodeCalldata_legacyAddress_int_int_ok (ty0 ty1 : ABI.IntType)
    {cd : ByteArray} {x y z : Ident} (hsz : 100 ≤ cd.size) :
    decodeCalldataWithMode .legacySolc05 [x, y, z]
      [abiAddress, .elem (.int ty0), .elem (.int ty1)] cd =
      some ((((∅ : Store).insert x (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (normalizeInt ty0 (Int.ofNat (calldataWord cd 36).toNat)))).insert z
        (.int (normalizeInt ty1 (Int.ofNat (calldataWord cd 68).toNat)))) := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have htake68 : (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have hw4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq_any cd 4 (by omega)
  have hw36 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) = calldataWord cd 36 := by
    simpa only [List.drop_drop] using decode_word_at_eq_any cd 36 (by omega)
  have hw68 : ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) = calldataWord cd 68 := by
    simpa only [List.drop_drop] using decode_word_at_eq_any cd 68 (by omega)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (by cases ty0 <;> cases ty1 <;> rfl),
    if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) (start := 0) htake4, decodeScalarWord_legacyInt_ok ty0 htake36,
    decodeScalarWord_legacyInt_ok ty1 htake68]
  change decodeCalldata.insertValues [x, y, z]
    [.address (AccountAddress.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
     .int (normalizeInt ty0 (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat)),
     .int (normalizeInt ty1 (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat))] ∅ = _
  rw [hw4, hw36, hw68]
  rfl

-- GENERALIZES the short-input branch to both arbitrary integer widths.
theorem decodeCalldata_legacyAddress_int_int_none_short (ty0 ty1 : ABI.IntType)
    {cd : ByteArray} {x y z : Ident} (hsz : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldataWithMode .legacySolc05 [x, y, z]
      [abiAddress, .elem (.int ty0), .elem (.int ty1)] cd = none := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (by cases ty0 <;> cases ty1 <;> rfl),
    if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  by_cases hfirst : 36 ≤ cd.size
  · have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, htlen]; omega
    rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) (start := 0) htake4]
    by_cases hsecond : 68 ≤ cd.size
    · have htake36 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
      have htake68 : ¬ (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
      rw [decodeScalarWord_legacyInt_ok ty0 htake36, decodeScalarWord_legacyInt_none_short ty1 htake68]
      rfl
    · have htake36 : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
      rw [decodeScalarWord_legacyInt_none_short ty0 htake36]
      rfl
  · have htake4 : ¬ (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]; omega
    rw [decodeScalarWord_legacyAddress_none_short (bytes := cd.toList.drop 4) (start := 0) htake4]
    rfl

end Benchmarks.UniswapV3.Pool
