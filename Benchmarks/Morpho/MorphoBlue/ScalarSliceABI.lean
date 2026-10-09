import Benchmarks.Morpho.MorphoBlue.StaticABIValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: discard extent metadata when decoding a single static return value.
theorem decodeReturnValue_static {ty : ABIType} {bytes : ByteArray} {size : Nat}
    {result : Option Value}
    (hd : isDynamicABIType ty = false) (hs : staticABIEncodedSize? ty = some size)
    (hb : bytes.size < 2 ^ 255)
    (hv : decodeABIValue? ty bytes.toList 0 = result.map (fun value ↦ (value, size))) :
    decodeReturnValueWithMode? .modern ty bytes =
      result := by
  have hl : bytes.toList.length = bytes.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [decodeReturnValueWithMode?, decodeReturnValue?, decodeReturnValues?,
    List.isEmpty_cons, true_and, hl, not_le.mpr hb, ↓reduceIte,
    abiTupleHeadSize?, hd, Bool.false_eq_true, hs, bind, Option.bind, pure, Nat.add_zero]
  rw [decodeABIValues_static_cons hd hs]
  simp only [Nat.zero_add, hv]
  cases result with
  | none => rfl
  | some value => simp [decodeABIValues?]

-- LIBRARY CANDIDATE: scalar decoding within a bounded byte-array slice.
theorem decodeScalarWord_extract {ty : ABIType} {cd : ByteArray} {start stop off : Nat}
    (hs : start + off + 32 ≤ stop) (he : stop ≤ cd.size) :
    decodeScalarWord? ty (cd.extract start stop).toList off =
      (decodeABIWord? ty (calldataWord cd (start + off))).map
        (fun value ↦ (value, off + 32)) := by
  have hslice : (((cd.extract start stop).toList.drop off).take 32) =
      (cd.toList.drop (start + off)).take 32 := by
    rw [extract_toList, List.drop_take, List.drop_drop, List.take_take]
    rw [Nat.min_eq_left (by omega)]
  have hl : (((cd.extract start stop).toList.drop off).take 32).length = 32 := by
    rw [hslice, List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min 32 (cd.size - (start + off)) = 32
    omega
  simp only [decodeScalarWord?, readWord?, readBytes?, hl, ↓reduceIte, bind, Option.bind]
  rw [hslice, decode_word_at_eq_any cd (start + off) (by omega)]
  cases decodeABIWord? ty (calldataWord cd (start + off)) <;> rfl

-- LIBRARY CANDIDATE: canonical boolean-word decoding, including its failure result.
theorem decodeABIWord_bool_result (w : UInt256) :
    decodeABIWord? abiBool w =
      if w = ⟨0⟩ ∨ w = ⟨1⟩ then some (.bool (decide (w ≠ ⟨0⟩))) else none := by
  have h0 : w.val.val = 0 ↔ w = ⟨0⟩ :=
    ⟨uint256_toNat_eq_zero, by rintro rfl; rfl⟩
  have h1 : w.val.val = 1 ↔ w = ⟨1⟩ :=
    ⟨uInt256_toNat_eq_one, by rintro rfl; rfl⟩
  by_cases hz : w = ⟨0⟩
  · subst w; rfl
  · by_cases ho : w = ⟨1⟩
    · subst w; rfl
    · simp only [decodeABIWord?, h0, h1, hz, ho, or_self, ↓reduceIte]

end Benchmarks.Morpho.MorphoBlue
