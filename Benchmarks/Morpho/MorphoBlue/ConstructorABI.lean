import Benchmarks.Morpho.MorphoBlue.Common
import Reasoning.Constructor
import Benchmarks.Morpho.MorphoBlue.ReturnCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: inversion of the ABI encoding for one constructor address.
theorem encodeABI_address_inversion (args : List Value) (bytes : List UInt8)
    (h : encodeABIValues? [.elem .address] args = some bytes) :
    ∃ a : AccountAddress, args = [.address a] ∧ bytes = EVM.Word.toBytesBE (UInt256.ofNat a.val) := by
  cases args with
  | nil => simp [encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?] at h
  | cons x xs =>
    cases x <;> simp only [encodeABIValues?, abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      bind, Option.bind, pure, Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
      encodeABIValuesFrom?, encodeABIValue?, encodeABIWord?, reduceCtorEq] at h
    case address a =>
      cases xs with
      | nil => exact ⟨a, rfl, by simpa only [encodeABIValuesFrom?, List.append_nil, Option.some.injEq] using h.symm⟩
      | cons y ys => simp [encodeABIValuesFrom?] at h

theorem morphoConstructorDeployment {args : List Value} {code : ByteArray}
    (h : config.selfDeployment morphoCreationBytecode args = some code) :
    ∃ a : AccountAddress, args = [.address a] ∧
      code = morphoCreationBytecode ++ (UInt256.ofNat a.val).toByteArray := by
  change (genSolidityConstructorDeployment contract.ctor.params morphoCreationBytecode args) = some code at h
  change (genSolidityConstructorDeployment [⟨"newOwner", .elem .address⟩] morphoCreationBytecode args) = some code at h
  simp only [genSolidityConstructorDeployment, List.map_cons, List.map_nil, bind, Option.bind, pure] at h
  cases he : encodeABIValues? [.elem .address] args with
  | none => simp only [he] at h; contradiction
  | some bs =>
    obtain ⟨a, ha, hb⟩ := encodeABI_address_inversion args bs he
    refine ⟨a, ha, ?_⟩
    simpa only [he, Option.some.injEq, hb, word_toBytesBE_toByteArray_eq_toByteArray] using h.symm

end Benchmarks.Morpho.MorphoBlue
