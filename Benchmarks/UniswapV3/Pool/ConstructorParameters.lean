import Benchmarks.UniswapV3.Pool.Calldata
import Benchmarks.UniswapV3.Pool.TickSpacingModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def constructorParameterTypes : List ABIType :=
  [.elem .address, .elem .address, .elem .address,
    .elem (.int (.uint ⟨24, by decide⟩)), .elem (.int (.sint ⟨24, by decide⟩))]

def constructorSpacing (out : ByteArray) : Int :=
  normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat (calldataWord out 128).toNat)

def constructorFee (out : ByteArray) : Int :=
  normalizeInt (.uint ⟨24, by decide⟩) (Int.ofNat (calldataWord out 96).toNat)

def constructorParameterValues (out : ByteArray) : List Value :=
  [.address (AccountAddress.ofNat (calldataWord out 0).toNat),
    .address (AccountAddress.ofNat (calldataWord out 32).toNat),
    .address (AccountAddress.ofNat (calldataWord out 64).toNat),
    .int (constructorFee out), .int (constructorSpacing out)]

theorem constructorSpacing_bounds (out : ByteArray) :
    -(2 ^ 23 : Int) ≤ constructorSpacing out ∧ constructorSpacing out < 2 ^ 23 :=
  normalizeSint_bounds _ _

theorem constructorFee_bounds (out : ByteArray) :
    0 ≤ constructorFee out ∧ constructorFee out < 2 ^ 24 :=
  ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

theorem constructorParameterDecodeShape (out : ByteArray) :
    decodeReturnValueWithMode? .legacySolc05 (.tuple constructorParameterTypes) out =
      (decodeScalarWordsWithMode? .legacySolc05 constructorParameterTypes out.toList 0).map
        Value.tuple := by
  have hhead : abiTupleHeadSize? constructorParameterTypes = some 160 :=
    abiTupleHeadSize_scalarWords_eq (by decide)
  have hdecode : decodeABIValue? (.tuple constructorParameterTypes) out.toList 0 .legacySolc05 =
      match decodeScalarWordsWithMode? .legacySolc05 constructorParameterTypes out.toList 0 with
      | some values => some (.tuple values, 160)
      | none => none := by
    rw [decodeABIValue?, hhead]
    simp only [bind, Option.bind, Nat.zero_add]
    rw [decodeABIValues_scalarWordsWithMode_eq (by decide) (by decide)]
    cases decodeScalarWordsWithMode? .legacySolc05 constructorParameterTypes out.toList 0 <;> rfl
  simp only [decodeReturnValueWithMode?, decodeReturnValuesWithMode?,
    show abiTupleHeadSize? [.tuple constructorParameterTypes] = some 160 by native_decide,
    bind, Option.bind, decodeABIValues?,
    show isDynamicABIType (.tuple constructorParameterTypes) = false from rfl,
    Bool.false_eq_true, ↓reduceIte,
    show staticABIEncodedSize? (.tuple constructorParameterTypes) = some 160 from rfl,
    Nat.zero_add, hdecode]
  cases decodeScalarWordsWithMode? .legacySolc05 constructorParameterTypes out.toList 0 <;> rfl

theorem constructorParameterDecode (out : ByteArray) (hlen : 160 ≤ out.size) :
    decodeReturnValueWithMode? .legacySolc05 (.tuple constructorParameterTypes) out =
      some (.tuple (constructorParameterValues out)) := by
  have hl : out.toList.length = out.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake (n : Nat) (hn : n + 32 ≤ 160) : ((out.toList.drop n).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hl]
    omega
  have hword (n : Nat) (hn : n + 32 ≤ 160) :
      ABI.bytesToWord ((out.toList.drop n).take 32) = calldataWord out n :=
    decode_word_at_eq out n (by omega) (by omega)
  have h0 := decodeScalarWord_legacyAddress_ok (htake 0 (by decide))
  have h1 := decodeScalarWord_legacyAddress_ok (htake 32 (by decide))
  have h2 := decodeScalarWord_legacyAddress_ok (htake 64 (by decide))
  have h3 := decodeScalarWord_legacyInt_ok (.uint ⟨24, by decide⟩) (htake 96 (by decide))
  have h4 := decodeScalarWord_legacyInt_ok (.sint ⟨24, by decide⟩) (htake 128 (by decide))
  rw [hword 0 (by decide)] at h0
  rw [hword 32 (by decide)] at h1
  rw [hword 64 (by decide)] at h2
  rw [hword 96 (by decide)] at h3
  rw [hword 128 (by decide)] at h4
  rw [constructorParameterDecodeShape]
  simp only [constructorParameterTypes, decodeScalarWordsWithMode?, h0, h1, h2, h3, h4,
    bind, Option.bind, Option.map_some, constructorParameterValues, constructorFee, constructorSpacing]

theorem constructorParameterDecodeShort (out : ByteArray) (hshort : out.size < 160) :
    decodeReturnValueWithMode? .legacySolc05 (.tuple constructorParameterTypes) out = none := by
  rw [constructorParameterDecodeShape]
  cases hd : decodeScalarWordsWithMode? .legacySolc05 constructorParameterTypes out.toList 0 with
  | none => rfl
  | some values =>
    have hlen := decodeScalarWordsWithMode?_some_length (Nat.zero_le _) hd
    have hl : out.toList.length = out.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
    change 160 ≤ out.toList.length at hlen
    rw [hl] at hlen
    omega

end Benchmarks.UniswapV3.Pool
