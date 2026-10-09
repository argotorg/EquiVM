import Benchmarks.CompoundIII.Comet.ConstructorDeployment
import Benchmarks.CompoundIII.Comet.StaticReturns

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem constructorEncodeFrom_fields {types : List ABIType} {values : List Value}
    {headSize : Nat} {head tail encoded : List UInt8}
    (h : encodeABIValuesFrom? types values headSize head tail = some encoded) :
    List.Forall₂ (fun ty value ↦ ∃ bytes, encodeABIValue? ty value = some bytes) types values := by
  induction types generalizing values head tail with
  | nil =>
    cases values with
    | nil => exact .nil
    | cons value rest => simp [encodeABIValuesFrom?] at h
  | cons ty types ih =>
    cases values with
    | nil => simp [encodeABIValuesFrom?] at h
    | cons value rest =>
      simp only [encodeABIValuesFrom?] at h
      obtain ⟨bytes, hb, hh⟩ := Option.bind_eq_some_iff.mp h
      refine .cons ⟨bytes, hb⟩ ?_
      split at hh
      · exact ih hh
      · exact ih hh

theorem constructorEncode_fields {types : List ABIType} {values : List Value}
    {encoded : List UInt8} (h : encodeABIValues? types values = some encoded) :
    List.Forall₂ (fun ty value ↦ ∃ bytes, encodeABIValue? ty value = some bytes) types values := by
  unfold encodeABIValues? at h
  obtain ⟨headSize, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact constructorEncodeFrom_fields h

theorem constructorEncodeFields_cons {ty : ABIType} {types : List ABIType}
    {values : List Value}
    (h : List.Forall₂ (fun ty value ↦ ∃ bytes, encodeABIValue? ty value = some bytes)
      (ty :: types) values) :
    ∃ value rest bytes, values = value :: rest ∧ encodeABIValue? ty value = some bytes ∧
      List.Forall₂ (fun ty value ↦ ∃ bytes, encodeABIValue? ty value = some bytes) types rest := by
  cases h with
  | cons hhead htail =>
    obtain ⟨bytes, hb⟩ := hhead
    exact ⟨_, _, bytes, rfl, hb, htail⟩

theorem constructorEncodeFields_nil {values : List Value}
    (h : List.Forall₂ (fun ty value ↦ ∃ bytes, encodeABIValue? ty value = some bytes) [] values) :
    values = [] := by
  cases h
  rfl

theorem constructorEncode_address {value : Value} {bytes : List UInt8}
    (h : encodeABIValue? (.elem .address) value = some bytes) :
    ∃ addr : AccountAddress, value = .address addr := by
  cases value <;> simp [encodeABIValue?, encodeABIWord?] at h
  exact ⟨_, rfl⟩

theorem constructorEncode_uint {width : BitWidth} {value : Value} {bytes : List UInt8}
    (h : encodeABIValue? (.elem (.int (.uint width))) value = some bytes) :
    ∃ n : Fin (2^width.val), value = .int (Int.ofNat n.val) := by
  cases value <;> simp only [encodeABIValue?, encodeABIWord?, bind, Option.bind] at h
  all_goals try contradiction
  rename_i i
  have hn : width.val ≠ 0 := by have := width.property.1; omega
  rw [if_neg hn] at h
  by_cases hi : 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow width.val)
  · rw [if_pos hi] at h
    refine ⟨⟨i.toNat, ?_⟩, ?_⟩
    · exact Int.toNat_lt hi.1 |>.mpr hi.2
    · exact congrArg Value.int (Int.toNat_of_nonneg hi.1).symm
  · rw [if_neg hi] at h
    contradiction

theorem constructorEncode_tuple {types : List ABIType} {value : Value} {bytes : List UInt8}
    (h : encodeABIValue? (.tuple types) value = some bytes) :
    ∃ values, value = .tuple values ∧ encodeABIValues? types values = some bytes := by
  cases value <;> simp only [encodeABIValue?] at h
  all_goals try contradiction
  exact ⟨_, rfl, h⟩

theorem constructorScalarFrom (xs : List ScalarReturn) (n : Nat) (head tail : List UInt8) :
    encodeABIValuesFrom? (xs.map (fun x ↦ .elem x.type)) (xs.map ScalarReturn.value) n head tail =
      some (head ++ (xs.flatMap (fun x ↦ EVM.Word.toBytesBE x.word)) ++ tail) := by
  induction xs generalizing head with
  | nil => simp [encodeABIValuesFrom?]
  | cons x xs ih =>
    simp only [List.map_cons, encodeABIValuesFrom?, x.encoded, isDynamicABIType,
      Bool.false_eq_true, if_false, bind, Option.bind, ih, List.flatMap_cons, List.append_assoc]

def constructorAddressScalar (a : AccountAddress) : ScalarReturn :=
  ⟨.address, .address a, EVM.word a.val, by
    simp only [encodeABIValue?, encodeABIWord?, bind, Option.bind]⟩

def constructorUintScalar (width : BitWidth) (n : Fin (2^width.val)) : ScalarReturn :=
  ⟨.int (.uint width), .int (Int.ofNat n.val), EVM.word n.val, by
    have hn : width.val ≠ 0 := by have := width.property.1; omega
    simp only [encodeABIValue?, encodeABIWord?, if_neg hn]
    rw [if_pos ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr n.isLt⟩]
    rfl⟩

theorem constructorScalarPrefix (xs : List ScalarReturn) (types : List ABIType)
    (values : List Value) (n : Nat) (head tail : List UInt8) :
    encodeABIValuesFrom? (xs.map (fun x ↦ .elem x.type) ++ types)
      (xs.map ScalarReturn.value ++ values) n head tail =
      encodeABIValuesFrom? types values n
        (head ++ xs.flatMap (fun x ↦ EVM.Word.toBytesBE x.word)) tail := by
  induction xs generalizing head with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.cons_append, encodeABIValuesFrom?, x.encoded,
      isDynamicABIType, Bool.false_eq_true, if_false, bind, Option.bind, ih,
      List.flatMap_cons, List.append_assoc]

end Benchmarks.CompoundIII.Comet
