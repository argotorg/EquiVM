import Benchmarks.Morpho.MetaMorphoV1_1.Common
import Reasoning.ABI

/-! Scalar tuple return decoding shared by the two Morpho struct readers. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: static size and dynamic flag of a scalar tuple.
theorem scalarTupleShape {types : List ABIType}
    (hscalar : types.all isABIScalarWordType = true) :
    isDynamicABIType (.tuple types) = false ∧
      staticABIEncodedSize? (.tuple types) = some (32 * types.length) := by
  have hdyn : isDynamicABITypeList types = false := by
    induction types with
    | nil => rfl
    | cons ty types ih =>
        simp only [List.all_cons, Bool.and_eq_true] at hscalar
        simp only [isDynamicABITypeList, isABIScalarWordType_dynamic hscalar.1,
          ih hscalar.2, Bool.false_or]
  have hsize (offset : Nat) :
      staticABIEncodedSizeList? types offset = some (offset + 32 * types.length) := by
    clear hdyn
    induction types generalizing offset with
    | nil => simp [staticABIEncodedSizeList?]
    | cons ty types ih =>
        simp only [List.all_cons, Bool.and_eq_true] at hscalar
        rw [staticABIEncodedSizeList?, isABIScalarWordType_size hscalar.1]
        simp only [bind, Option.bind]
        rw [ih hscalar.2]
        simp only [List.length_cons]
        congr 1
        omega
  exact ⟨hdyn, by simpa only [staticABIEncodedSize?, Nat.zero_add] using hsize 0⟩

-- LIBRARY CANDIDATE: flattening a static tuple at the start of an ABI buffer.
theorem scalarTupleValueDecode {bytes : List UInt8} {types : List ABIType}
    (hscalar : types.all isABIScalarWordType = true) :
    decodeABIValue? (.tuple types) bytes 0 =
      (decodeScalarWords? types bytes 0).map
        (fun vs ↦ (.tuple vs, 32 * types.length)) := by
  rw [decodeABIValue?, abiTupleHeadSize_scalarWords_eq hscalar]
  simp only [bind, Option.bind, Nat.zero_add]
  rw [decodeABIValues_scalarWords_eq hscalar (by omega)]
  cases decodeScalarWords? types bytes 0 <;> rfl

-- LIBRARY CANDIDATE: flattening a scalar tuple return to the scalar-word decoder.
theorem scalarTupleReturnDecode {out : ByteArray} {types : List ABIType}
    (hscalar : types.all isABIScalarWordType = true) (hhi : out.size < 2 ^ 255) :
    decodeReturnValues? [.tuple types] out =
      (decodeScalarWords? types out.toList 0).map (fun vs ↦ [.tuple vs]) := by
  have hl : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  obtain ⟨hdyn, hsize⟩ := scalarTupleShape hscalar
  have hvalue : decodeABIValue? (.tuple types) out.toList 0 =
      (decodeScalarWords? types out.toList 0).map
        (fun vs ↦ (.tuple vs, 32 * types.length)) := scalarTupleValueDecode hscalar
  have houter : abiTupleHeadSize? [.tuple types] = some (32 * types.length) := by
    simp only [abiTupleHeadSize?, hdyn, hsize, Bool.false_eq_true, if_false, bind,
      Option.bind, Nat.add_zero]
  simp only [decodeReturnValues?, List.isEmpty_cons, true_and, hl,
    Nat.not_le.mpr hhi, if_false, houter, bind, Option.bind]
  rw [decodeABIValues?]
  simp only [hdyn, Bool.false_eq_true, if_false, hsize, bind, Option.bind,
    Nat.zero_add, hvalue]
  cases decodeScalarWords? types out.toList 0 <;> simp [decodeABIValues?]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
