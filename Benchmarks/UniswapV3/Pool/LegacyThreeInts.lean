import Benchmarks.UniswapV3.Pool.Calldata

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- GENERALIZES Reasoning.ABIComposite.decodeCalldata_legacyUint256_uint256_uint256_ok
-- — lift by parameterizing over the three integer types.
theorem decodeCalldata_legacyThreeInts_ok (ty0 ty1 ty2 : ABI.IntType)
    {cd : ByteArray} {x y z : Ident} (hsz : 100 ≤ cd.size) :
    decodeCalldataWithMode .legacySolc05 [x, y, z]
      [.elem (.int ty0), .elem (.int ty1), .elem (.int ty2)] cd =
      some ((((∅ : Store).insert x
        (.int (normalizeInt ty0 (Int.ofNat (calldataWord cd 4).toNat)))).insert y
        (.int (normalizeInt ty1 (Int.ofNat (calldataWord cd 36).toNat)))).insert z
        (.int (normalizeInt ty2 (Int.ofNat (calldataWord cd 68).toNat)))) := by
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
  rw [decodeCalldataWithMode_legacyScalarWords_eq
      (by cases ty0 <;> cases ty1 <;> cases ty2 <;> rfl),
    if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyInt_ok ty0 (bytes := cd.toList.drop 4) (start := 0)
      (by simpa only [List.drop_zero] using htake4),
    decodeScalarWord_legacyInt_ok ty1 htake36, decodeScalarWord_legacyInt_ok ty2 htake68]
  change decodeCalldata.insertValues [x, y, z]
    [.int (normalizeInt ty0 (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)),
     .int (normalizeInt ty1 (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat)),
     .int (normalizeInt ty2 (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat))] ∅ = _
  rw [hw4, hw36, hw68]
  rfl

end Benchmarks.UniswapV3.Pool
