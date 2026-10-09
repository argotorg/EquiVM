import Benchmarks.CompoundIII.Comet.ConstructorSizeWitness

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet.ConstructorSizeBoundReview

-- Historical alternative, superseded by the user's choice of a separate bounded refinement
-- relation. This is not Comet's active deployment encoder and must not be wired into its config.
def boundedDeployment (initcode : ByteArray) (args : List Value) : Option ByteArray := do
  let code ← genSolidityConstructorDeployment contract.ctor.params initcode args
  if code.size < UInt256.size then some code else none

theorem boundedDeployment_eq_some_iff {initcode code : ByteArray} {args : List Value} :
    boundedDeployment initcode args = some code ↔
      genSolidityConstructorDeployment contract.ctor.params initcode args = some code ∧
        code.size < UInt256.size := by
  unfold boundedDeployment
  constructor
  · intro h
    obtain ⟨result, hr, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hsize
      cases h
      exact ⟨hr, hsize⟩
    · contradiction
  · rintro ⟨h, hsize⟩
    rw [h]
    simp only [bind, Option.bind, if_pos hsize]

theorem boundedDeployment_shape {args : List Value} {code : ByteArray}
    (h : boundedDeployment cometWithExtendedAssetListCreationBytecode args = some code) :
    args.length = contract.ctor.params.length ∧ code.size < UInt256.size ∧
      ∃ bytes : List UInt8,
        encodeABIValues? (contract.ctor.params.map Param.ty) args = some bytes ∧
        code = cometWithExtendedAssetListCreationBytecode ++ bytes.toByteArray := by
  obtain ⟨h, hsize⟩ := boundedDeployment_eq_some_iff.mp h
  obtain ⟨hlen, bytes, hb, hcode⟩ := cometConstructorDeployment_shape h
  exact ⟨hlen, hsize, bytes, hb, hcode⟩

theorem ordinaryDeployment_preserved (n : Nat)
    (hsize : 22161 + 224*n < UInt256.size) :
    boundedDeployment cometWithExtendedAssetListCreationBytecode
        [ConstructorSizeWitness.configValue n] =
      some (cometWithExtendedAssetListCreationBytecode ++
        (ConstructorSizeWitness.encodedArgs n).toByteArray) := by
  apply boundedDeployment_eq_some_iff.mpr
  refine ⟨ConstructorSizeWitness.deployment n, ?_⟩
  have hcreation : cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  simpa only [ByteArray.size_append, hcreation, List.size_toByteArray,
    ConstructorSizeWitness.encodedArgs_length, ← Nat.add_assoc] using hsize

theorem rejected_of_size {initcode code : ByteArray} {args : List Value}
    (h : config.selfDeployment initcode args = some code) (hsize : UInt256.size ≤ code.size) :
    boundedDeployment initcode args = none := by
  change genSolidityConstructorDeployment contract.ctor.params initcode args = some code at h
  unfold boundedDeployment
  rw [h]
  simp only [bind, Option.bind, if_neg (Nat.not_lt.mpr hsize)]

theorem wrappingDeployment_rejected :
    boundedDeployment cometWithExtendedAssetListCreationBytecode
      [ConstructorSizeWitness.configValue UInt256.size] = none :=
  rejected_of_size (ConstructorSizeWitness.deployment UInt256.size)
    ConstructorSizeWitness.admittedInput_wraps.2.1

end Benchmarks.CompoundIII.Comet.ConstructorSizeBoundReview
