import Benchmarks.CompoundIII.Comet.ConstructorInput

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem constructorScalarBytes_length (xs : List ScalarReturn) :
    (xs.flatMap (fun x ↦ EVM.Word.toBytesBE x.word)).length = 32 * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, word_toBytesBE_length_32, ih,
      List.length_cons]
    omega

namespace ConstructorAsset

def bytes (c : ConstructorAsset) : List UInt8 :=
  c.scalars.flatMap (fun x ↦ EVM.Word.toBytesBE x.word)

theorem encoded (c : ConstructorAsset) : encodeABIValue? abiType c.value = some c.bytes := by
  have ht : abiType = .tuple (c.scalars.map (fun x ↦ .elem x.type)) := rfl
  have hh : abiTupleHeadSize? (c.scalars.map (fun x ↦ .elem x.type)) = some 224 := by
    change abiTupleHeadSize?
      [.elem .address, .elem .address, .elem (.int (.uint ⟨8, by decide⟩)),
        .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨64, by decide⟩)),
        .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨128, by decide⟩))] = _
    native_decide
  rw [ht, value, encodeABIValue?, encodeABIValues?, hh]
  simp only [bind, Option.bind, constructorScalarFrom, List.nil_append, List.append_nil, bytes]

theorem bytes_length (c : ConstructorAsset) : c.bytes.length = 224 := by
  rw [bytes, constructorScalarBytes_length]
  rfl

theorem array_encoded (assets : List ConstructorAsset) :
    encodeABIArrayElems? abiType (assets.map value) = some (assets.flatMap bytes) := by
  rw [encodeABIArrayElems?]
  have hd : isDynamicABIType abiType = false := by decide
  rw [hd]
  simp only [Bool.false_eq_true, if_false]
  induction assets with
  | nil => simp [encodeABIStaticArrayElems?]
  | cons a assets ih =>
    rw [List.map_cons, encodeABIStaticArrayElems?, encoded]
    simp only [bind, Option.bind, ih, List.flatMap_cons]

theorem array_bytes_length (assets : List ConstructorAsset) :
    (assets.flatMap bytes).length = 224 * assets.length := by
  induction assets with
  | nil => simp
  | cons a assets ih =>
    simp only [List.flatMap_cons, List.length_append, bytes_length, ih, List.length_cons]
    omega

end ConstructorAsset

namespace ConstructorConfig

/-- Exact ABI argument bytes: outer tuple offset, twenty scalars, asset-array offset and length,
    then seven words per asset. -/
def encodedArgs (c : ConstructorConfig) : List UInt8 :=
  natBytes 32 ++ c.scalars.flatMap (fun x ↦ EVM.Word.toBytesBE x.word) ++ natBytes 672 ++
    natBytes c.assetConfigs.length ++ c.assetConfigs.flatMap ConstructorAsset.bytes

theorem value_encoded (c : ConstructorConfig) :
    encodeABIValue? abiType c.value =
      some (c.scalars.flatMap (fun x ↦ EVM.Word.toBytesBE x.word) ++ natBytes 672 ++
        natBytes c.assetConfigs.length ++ c.assetConfigs.flatMap ConstructorAsset.bytes) := by
  have ht : abiType = .tuple
      (c.scalars.map (fun x ↦ .elem x.type) ++ [.dynamicArray ConstructorAsset.abiType]) := rfl
  have hh : abiTupleHeadSize?
      (c.scalars.map (fun x ↦ .elem x.type) ++ [.dynamicArray ConstructorAsset.abiType]) =
      some 672 := by
    change abiTupleHeadSize? (match abiType with | .tuple ts => ts | _ => []) = _
    native_decide
  rw [ht, value, encodeABIValue?, encodeABIValues?, hh]
  simp only [bind, Option.bind]
  rw [constructorScalarPrefix, encodeABIValuesFrom?, encodeABIValue?, List.length_map,
    ConstructorAsset.array_encoded]
  simp only [bind, Option.bind, isDynamicABIType, if_true, List.nil_append, List.length_nil,
    Nat.add_zero, encodeABIValuesFrom?, List.append_nil, List.append_assoc]

theorem encoded (c : ConstructorConfig) :
    encodeABIValues? [abiType] [c.value] = some c.encodedArgs := by
  have hh : abiTupleHeadSize? [abiType] = some 32 := by native_decide
  have hd : isDynamicABIType abiType = true := by decide
  rw [encodeABIValues?, hh]
  simp only [bind, Option.bind]
  rw [encodeABIValuesFrom?, value_encoded, hd]
  simp only [bind, Option.bind, if_true, List.nil_append, List.length_nil,
    Nat.add_zero, encodeABIValuesFrom?, List.append_nil, encodedArgs, List.append_assoc]

theorem encodedArgs_length (c : ConstructorConfig) :
    c.encodedArgs.length = 736 + 224 * c.assetConfigs.length := by
  have hn (n : Nat) : (natBytes n).length = 32 := word_toBytesBE_length_32 _
  simp only [encodedArgs, List.length_append, hn, constructorScalarBytes_length,
    ConstructorAsset.array_bytes_length]
  have hs : c.scalars.length = 20 := rfl
  rw [hs]

end ConstructorConfig

/-- Canonical form and exact length of every deployment admitted by the bounded relation. -/
theorem cometConstructorBoundedInput {args : List Value} {code : ByteArray} {I : ExecutionEnv}
    (hdeploy : config.selfDeployment cometWithExtendedAssetListCreationBytecode args = some code)
    (hcode : I.code = code) (hsize : I.code.size < UInt256.size) :
    ∃ c : ConstructorConfig, args = [c.value] ∧
      I.code = cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray ∧
      22161 + 224 * c.assetConfigs.length < UInt256.size := by
  obtain ⟨_, bytes, hencode, hinitcode, hbytes⟩ :=
    cometConstructorDeployment_bounded_shape hdeploy hcode hsize
  obtain ⟨c, rfl⟩ := cometConstructorInput hencode
  have ht : contract.ctor.params.map Param.ty = [ConstructorConfig.abiType] := rfl
  rw [ht, c.encoded] at hencode
  cases hencode
  refine ⟨c, rfl, hinitcode, ?_⟩
  rw [ConstructorConfig.encodedArgs_length] at hbytes
  omega

end Benchmarks.CompoundIII.Comet
