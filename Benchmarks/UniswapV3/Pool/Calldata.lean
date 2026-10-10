import Reasoning.ABIComposite
import Benchmarks.UniswapV3.Pool.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3.Pool

-- GENERALIZES the legacy uint8/uint48/uint96/int256 decoder facts to all integer widths.
theorem decodeScalarWord_legacyInt_ok (ty : ABI.IntType) {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? .legacySolc05 (.elem (.int ty)) bytes start =
      some (.int (normalizeInt ty (Int.ofNat
        (ABI.bytesToWord ((bytes.drop start).take 32)).toNat)), start + 32) := by
  cases ty <;> simp only [decodeScalarWordWithMode?, readWord?, readBytes?, decodeABIWord?,
    bind, Option.bind, if_pos hlen]
  all_goals rename_i width
  all_goals rw [if_neg (Nat.ne_of_gt width.property.1)]; rfl

-- LIBRARY CANDIDATE: Reasoning.ABI, short legacy integer calldata.
theorem decodeScalarWord_legacyInt_none_short (ty : ABI.IntType) {bytes : List UInt8} {start : Nat}
    (hshort : ¬ ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? .legacySolc05 (.elem (.int ty)) bytes start = none := by
  simp only [decodeScalarWordWithMode?, readWord?, readBytes?, if_neg hshort, bind, Option.bind]

-- LIBRARY CANDIDATE: Reasoning.ABI, a single legacy integer argument at any width.
theorem decodeCalldata_legacyInt_ok (ty : ABI.IntType) {cd : ByteArray} {x : Solm.Ident}
    (hsz : 36 ≤ cd.size) :
    decodeCalldataWithMode .legacySolc05 [x] [.elem (.int ty)] cd =
      some ((∅ : Store).insert x (.int (normalizeInt ty (Int.ofNat (calldataWord cd 4).toNat)))) := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (by cases ty <;> rfl),
    if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyInt_ok ty (by simpa only [List.drop_zero] using htake)]
  change decodeCalldata.insertValues [x]
      [.int (normalizeInt ty (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat))] ∅ = _
  rw [hword]
  simp only [decodeCalldata.insertValues]

-- LIBRARY CANDIDATE: Reasoning.ABI, a short single legacy integer argument at any width.
theorem decodeCalldata_legacyInt_none_short (ty : ABI.IntType) {cd : ByteArray} {x : Solm.Ident}
    (hsz : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode .legacySolc05 [x] [.elem (.int ty)] cd = none := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  rw [decodeCalldataWithMode_legacyScalarWords_eq (by cases ty <;> rfl),
    if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyInt_none_short ty (by simpa only [List.drop_zero] using htake)]
  rfl

-- GENERALIZES Reasoning.Solc.solcDecodeLenCheckShort to unsigned guards.
theorem solcDecodeLenCheckShortUnsigned {sz : Nat} {head need : UInt256}
    (hhead : head.toNat ≤ sz) (hshort : sz < head.toNat + need.toNat)
    (hsz : sz < UInt256.size) :
    UInt256.lt (UInt256.sub (UInt256.ofNat sz) head) need = ⟨1⟩ := by
  apply ult_one
  rw [usub_ofNat_word_toNat hhead hsz]
  omega


-- LIBRARY CANDIDATE: Reasoning.ABIComposite, bytes32 calldata expressed as a word's bytes.
theorem decodeCalldata_legacyBytes32Word_ok {cd : ByteArray} {x : Ident} (hsz : 36 ≤ cd.size) :
    decodeCalldataWithMode .legacySolc05 [x] [abiBytes32] cd =
      some ((∅ : Store).insert x (.fixedBytes abiBytes32Width
        (EVM.Word.toBytesBE (calldataWord cd 4)))) := by
  have htake : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min 32 (cd.size - 4) = 32
    omega
  have hw := toBytesBE_bytesToWord_of_length htake
  rw [decode_word_at_eq_any cd 4 hsz] at hw
  rw [decodeCalldataWithMode_legacyBytes32_ok hsz, hw]

-- LIBRARY CANDIDATE: two legacy integer arguments of arbitrary widths.
theorem decodeCalldata_legacyIntPair_ok (ty₀ ty₁ : ABI.IntType)
    {cd : ByteArray} {x y : Ident} (hsz : 68 ≤ cd.size) :
    decodeCalldataWithMode .legacySolc05 [x, y] [.elem (.int ty₀), .elem (.int ty₁)] cd =
      some (((∅ : Store).insert x
        (.int (normalizeInt ty₀ (Int.ofNat (calldataWord cd 4).toNat)))).insert y
        (.int (normalizeInt ty₁ (Int.ofNat (calldataWord cd 36).toNat)))) := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq_any cd 4 (by omega)
  have hword36 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 := by
    simpa only [List.drop_drop] using decode_word_at_eq_any cd 36 (by omega)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (by cases ty₀ <;> cases ty₁ <;> rfl),
    if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyInt_ok ty₀ (by simpa only [List.drop_zero] using htake4),
    decodeScalarWord_legacyInt_ok ty₁ htake36]
  change decodeCalldata.insertValues [x, y]
      [.int (normalizeInt ty₀ (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)),
       .int (normalizeInt ty₁
         (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat))] ∅ = _
  rw [hword4, hword36]
  simp only [decodeCalldata.insertValues]

-- LIBRARY CANDIDATE: a short pair of legacy integer arguments at arbitrary widths.
theorem decodeCalldata_legacyIntPair_none_short (ty₀ ty₁ : ABI.IntType)
    {cd : ByteArray} {x y : Ident} (hsz : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode .legacySolc05 [x, y] [.elem (.int ty₀), .elem (.int ty₁)] cd = none := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (by cases ty₀ <;> cases ty₁ <;> rfl),
    if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  by_cases hfirst : 36 ≤ cd.size
  · have htake4 : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]; omega
    have htake36 : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
    rw [decodeScalarWord_legacyInt_ok ty₀ htake4,
      decodeScalarWord_legacyInt_none_short ty₁ htake36]
    rfl
  · have htake4 : ¬ (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]; omega
    rw [decodeScalarWord_legacyInt_none_short ty₀ htake4]
    rfl

end Benchmarks.UniswapV3.Pool
