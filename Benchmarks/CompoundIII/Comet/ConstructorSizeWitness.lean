import Benchmarks.CompoundIII.Comet.ConstructorEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet.ConstructorSizeWitness

set_option maxRecDepth 2000

/-- A canonical seven-word asset tuple, repeated only symbolically in this file. -/
def assetType : ABIType := .tuple
  [.elem .address, .elem .address, .elem (.int (.uint ⟨8, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨128, by decide⟩))]

def asset : Value := .tuple
  [.address (AccountAddress.ofNat 0), .address (AccountAddress.ofNat 0),
    .int 0, .int 0, .int 0, .int 0, .int 0]

theorem asset_encoded : encodeABIValue? assetType asset = some (List.replicate 224 0) := by
  native_decide

def prefixTypes : List ABIType :=
  List.replicate 5 (.elem .address) ++ List.replicate 12 (.elem (.int (.uint ⟨64, by decide⟩))) ++
    List.replicate 3 (.elem (.int (.uint ⟨104, by decide⟩)))

def prefixValues : List Value :=
  [.address (AccountAddress.ofNat 0), .address (AccountAddress.ofNat 0),
    .address (AccountAddress.ofNat 1), .address (AccountAddress.ofNat 2),
    .address (AccountAddress.ofNat 3),
    .int 0, .int 0, .int 0, .int 0, .int 0, .int 0, .int 0, .int 0,
    .int 0, .int 1, .int 0, .int 0, .int 1, .int 1, .int 0]

def configType : ABIType := .tuple (prefixTypes ++ [.dynamicArray assetType])

def configValue (n : Nat) : Value := .tuple (prefixValues ++ [.array (List.replicate n asset)])

def headWords : List Nat :=
  [32, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 672]

def encodedHead : List UInt8 := headWords.flatMap natBytes

def encodedArgs (n : Nat) : List UInt8 :=
  encodedHead ++ natBytes n ++ List.replicate (224*n) 0

theorem ctor_types : contract.ctor.params.map Param.ty = [configType] := rfl

theorem assets_encoded (n : Nat) :
    encodeABIArrayElems? assetType (List.replicate n asset) =
      some (List.replicate (224*n) 0) := by
  rw [encodeABIArrayElems?]
  have hd : isDynamicABIType assetType = false := by decide
  rw [hd]
  simp only [Bool.false_eq_true, if_false]
  induction n with
  | zero => simp [encodeABIStaticArrayElems?]
  | succ n ih =>
    rw [List.replicate_succ, encodeABIStaticArrayElems?, asset_encoded]
    simp only [bind, Option.bind, ih]
    rw [← List.replicate_add]
    congr 2
    omega

def prefixScalars : List ScalarReturn :=
  [constructorAddressScalar (AccountAddress.ofNat 0),
    constructorAddressScalar (AccountAddress.ofNat 0),
    constructorAddressScalar (AccountAddress.ofNat 1),
    constructorAddressScalar (AccountAddress.ofNat 2),
    constructorAddressScalar (AccountAddress.ofNat 3),
    constructorUintScalar ⟨64, by decide⟩ ⟨0, by decide⟩,
    constructorUintScalar ⟨64, by decide⟩ ⟨0, by decide⟩,
    constructorUintScalar ⟨64, by decide⟩ ⟨0, by decide⟩,
    constructorUintScalar ⟨64, by decide⟩ ⟨0, by decide⟩,
    constructorUintScalar ⟨64, by decide⟩ ⟨0, by decide⟩,
    constructorUintScalar ⟨64, by decide⟩ ⟨0, by decide⟩,
    constructorUintScalar ⟨64, by decide⟩ ⟨0, by decide⟩,
    constructorUintScalar ⟨64, by decide⟩ ⟨0, by decide⟩,
    constructorUintScalar ⟨64, by decide⟩ ⟨0, by decide⟩,
    constructorUintScalar ⟨64, by decide⟩ ⟨1, by decide⟩,
    constructorUintScalar ⟨64, by decide⟩ ⟨0, by decide⟩,
    constructorUintScalar ⟨64, by decide⟩ ⟨0, by decide⟩,
    constructorUintScalar ⟨104, by decide⟩ ⟨1, by decide⟩,
    constructorUintScalar ⟨104, by decide⟩ ⟨1, by decide⟩,
    constructorUintScalar ⟨104, by decide⟩ ⟨0, by decide⟩]

theorem prefix_types : prefixScalars.map (fun x ↦ .elem x.type) = prefixTypes := rfl

theorem prefix_values : prefixScalars.map ScalarReturn.value = prefixValues := rfl

theorem configValue_encoded (n : Nat) :
    encodeABIValue? configType (configValue n) =
      some (prefixScalars.flatMap (fun x ↦ EVM.Word.toBytesBE x.word) ++
        natBytes 672 ++ natBytes n ++ List.replicate (224*n) 0) := by
  change encodeABIValue? (.tuple (prefixTypes ++ [.dynamicArray assetType]))
    (.tuple (prefixValues ++ [.array (List.replicate n asset)])) = _
  rw [encodeABIValue?, encodeABIValues?]
  have hh : abiTupleHeadSize? (prefixTypes ++ [.dynamicArray assetType]) = some 672 := by native_decide
  rw [hh]
  simp only [bind, Option.bind]
  rw [← prefix_types, ← prefix_values, constructorScalarPrefix]
  rw [encodeABIValuesFrom?, encodeABIValue?, List.length_replicate, assets_encoded]
  simp only [bind, Option.bind, isDynamicABIType, if_true, List.nil_append, List.length_nil,
    Nat.add_zero, encodeABIValuesFrom?, List.append_nil, List.append_assoc]

theorem config_encoded (n : Nat) :
    encodeABIValues? [configType] [configValue n] = some (encodedArgs n) := by
  have hh : abiTupleHeadSize? [configType] = some 32 := by native_decide
  have hd : isDynamicABIType configType = true := by decide
  rw [encodeABIValues?, hh]
  simp only [bind, Option.bind]
  rw [encodeABIValuesFrom?, configValue_encoded, hd]
  simp only [bind, Option.bind, if_true, List.nil_append, List.length_nil,
    Nat.add_zero, encodeABIValuesFrom?, List.append_nil, List.append_assoc]
  have he : encodedHead = natBytes 32 ++
      prefixScalars.flatMap (fun x ↦ EVM.Word.toBytesBE x.word) ++ natBytes 672 := by
    native_decide
  simp only [encodedArgs, he, List.append_assoc]

theorem deployment (n : Nat) :
    config.selfDeployment cometWithExtendedAssetListCreationBytecode [configValue n] =
      some (cometWithExtendedAssetListCreationBytecode ++ (encodedArgs n).toByteArray) := by
  change (do
    let bs ← encodeABIValues? (contract.ctor.params.map Param.ty) [configValue n]
    pure (cometWithExtendedAssetListCreationBytecode ++ bs.toByteArray)) = _
  rw [ctor_types, config_encoded]
  rfl

theorem encodedArgs_length (n : Nat) : (encodedArgs n).length = 736 + 224*n := by
  have hh : encodedHead.length = 704 := by native_decide
  have hn : (natBytes n).length = 32 := by
    rw [← List.size_toByteArray, natBytes_toByteArray_size]
  simp only [encodedArgs, List.length_append, hh, hn, List.length_replicate]

theorem encodedLength_wraps : natBytes UInt256.size = natBytes 0 := by
  apply congrArg EVM.Word.toBytesBE
  decide

theorem encodedPrefix_wraps : (encodedArgs UInt256.size).take 736 = encodedArgs 0 := by
  have hh : encodedHead.length = 704 := by native_decide
  have hn : (natBytes UInt256.size).length = 32 := by
    rw [← List.size_toByteArray, natBytes_toByteArray_size]
  unfold encodedArgs
  rw [show 736 = (encodedHead ++ natBytes UInt256.size).length by
    rw [List.length_append, hh, hn]]
  rw [List.take_left, encodedLength_wraps]
  simp

theorem codesize_wraps :
    UInt256.ofNat
        (cometWithExtendedAssetListCreationBytecode ++ (encodedArgs UInt256.size).toByteArray).size =
      UInt256.ofNat
        (cometWithExtendedAssetListCreationBytecode ++ (encodedArgs 0).toByteArray).size := by
  apply u256_inj
  simp only [ByteArray.size_append, List.size_toByteArray,
    encodedArgs_length, Nat.mul_zero, Nat.add_zero]
  change (cometWithExtendedAssetListCreationBytecode.size + (736 + 224 * UInt256.size)) %
    UInt256.size = (cometWithExtendedAssetListCreationBytecode.size + 736) % UInt256.size
  simp [Nat.add_mod]

theorem source_length_rejects :
    evalBinaryOp? .le (.int (Int.ofNat (List.replicate UInt256.size asset).length)) (.int 24) =
      .ok (.bool false) := by
  rw [List.length_replicate]
  have hn : ¬ (Int.ofNat UInt256.size ≤ 24) := by decide
  simp only [evalBinaryOp?, decide_eq_false hn]

theorem bytecode_length_accepts : UInt256.gt (UInt256.ofNat UInt256.size) ⟨24⟩ = ⟨0⟩ := by
  decide

theorem admittedInput_wraps :
    config.selfDeployment cometWithExtendedAssetListCreationBytecode [configValue UInt256.size] =
        some (cometWithExtendedAssetListCreationBytecode ++ (encodedArgs UInt256.size).toByteArray) ∧
      UInt256.size ≤
        (cometWithExtendedAssetListCreationBytecode ++ (encodedArgs UInt256.size).toByteArray).size ∧
      natBytes UInt256.size = natBytes 0 ∧
      (encodedArgs UInt256.size).take 736 = encodedArgs 0 ∧
      UInt256.ofNat
          (cometWithExtendedAssetListCreationBytecode ++ (encodedArgs UInt256.size).toByteArray).size =
        UInt256.ofNat
          (cometWithExtendedAssetListCreationBytecode ++ (encodedArgs 0).toByteArray).size := by
  refine ⟨deployment _, ?_, encodedLength_wraps, encodedPrefix_wraps, codesize_wraps⟩
  rw [ByteArray.size_append, List.size_toByteArray, encodedArgs_length]
  omega

end Benchmarks.CompoundIII.Comet.ConstructorSizeWitness
