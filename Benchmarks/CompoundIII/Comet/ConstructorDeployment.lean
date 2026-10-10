import Benchmarks.CompoundIII.Comet.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: successful tuple encoding always checks the argument count.
theorem constructorEncodeFrom_length {types : List ABIType} {values : List Value}
    {headSize : Nat} {head tail encoded : List UInt8}
    (h : encodeABIValuesFrom? types values headSize head tail = some encoded) :
    values.length = types.length := by
  induction types generalizing values head tail with
  | nil =>
    cases values with
    | nil => rfl
    | cons value rest => simp [encodeABIValuesFrom?] at h
  | cons ty types ih =>
    cases values with
    | nil => simp [encodeABIValuesFrom?] at h
    | cons value rest =>
      simp only [encodeABIValuesFrom?] at h
      obtain ⟨bytes, _, hh⟩ := Option.bind_eq_some_iff.mp h
      split at hh
      · exact congrArg Nat.succ (ih hh)
      · exact congrArg Nat.succ (ih hh)

theorem constructorEncode_length {types : List ABIType} {values : List Value}
    {encoded : List UInt8} (h : encodeABIValues? types values = some encoded) :
    values.length = types.length := by
  unfold encodeABIValues? at h
  obtain ⟨headSize, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact constructorEncodeFrom_length h

theorem cometConstructorDeployment_shape {args : List Value} {code : ByteArray}
    (h : config.selfDeployment cometWithExtendedAssetListCreationBytecode args = some code) :
    args.length = contract.ctor.params.length ∧
      ∃ bytes : List UInt8,
        encodeABIValues? (contract.ctor.params.map Param.ty) args = some bytes ∧
        code = cometWithExtendedAssetListCreationBytecode ++ bytes.toByteArray := by
  change (do
    let bytes ← encodeABIValues? (contract.ctor.params.map Param.ty) args
    pure (cometWithExtendedAssetListCreationBytecode ++ bytes.toByteArray)) = some code at h
  obtain ⟨bytes, hb, hc⟩ := Option.bind_eq_some_iff.mp h
  have hc : cometWithExtendedAssetListCreationBytecode ++ bytes.toByteArray = code :=
    Option.some.inj hc
  refine ⟨?_, bytes, hb, hc.symm⟩
  simpa only [List.length_map] using constructorEncode_length hb

theorem cometCreationBytecode_size : cometWithExtendedAssetListCreationBytecode.size = 21425 := by
  native_decide

/-- Extract the constructor tail and its bound from the bounded refinement premise, without
    imposing any extra condition on `selfDeployment`. -/
theorem cometConstructorDeployment_bounded_shape {args : List Value} {code : ByteArray}
    {I : ExecutionEnv}
    (h : config.selfDeployment cometWithExtendedAssetListCreationBytecode args = some code)
    (hcode : I.code = code) (hsize : I.code.size < UInt256.size) :
    args.length = contract.ctor.params.length ∧
      ∃ bytes : List UInt8,
        encodeABIValues? (contract.ctor.params.map Param.ty) args = some bytes ∧
        I.code = cometWithExtendedAssetListCreationBytecode ++ bytes.toByteArray ∧
        21425 + bytes.length < UInt256.size := by
  obtain ⟨hlen, bytes, hb, rfl⟩ := cometConstructorDeployment_shape h
  refine ⟨hlen, bytes, hb, hcode, ?_⟩
  simpa only [hcode, ByteArray.size_append, cometCreationBytecode_size,
    List.size_toByteArray] using hsize

/-- With bounded initcode, the constructor's `CODESIZE - 21425` is the actual argument length. -/
theorem cometConstructorCodeSize {tail : ByteArray}
    (hsize : (cometWithExtendedAssetListCreationBytecode ++ tail).size < UInt256.size) :
    (UInt256.sub
      (UInt256.ofNat (cometWithExtendedAssetListCreationBytecode ++ tail).size)
      (UInt256.ofNat 21425)).toNat = tail.size := by
  rw [usub_ofNat_lit_toNat (by
    simp only [ByteArray.size_append, cometCreationBytecode_size]; omega) hsize]
  simp only [ByteArray.size_append, cometCreationBytecode_size, Nat.add_sub_cancel_left]

end Benchmarks.CompoundIII.Comet
