import Benchmarks.EAS.EAS.StaticCallBridge

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: leading zero bytes do not change a big-endian byte-array value.
theorem fromByteArrayBigEndian_zeroes_append (n : Nat) (b : ByteArray) :
    fromByteArrayBigEndian (ByteArray.zeroes n ++ b) = fromByteArrayBigEndian b := by
  simp only [fromByteArrayBigEndian,byteArray_toList_eq,ByteArray.data_append,Array.toList_append,
    byteArray_zeroes_toList,fromBytesBigEndian,Function.comp,List.reverse_append,List.reverse_replicate,
    fromBytes'_append_zeros]

-- LIBRARY CANDIDATE: a word made from a zero-padded byte sequence fits the unpadded width.
theorem uInt256OfByteArray_zeroes_bound (n : Nat) (b : ByteArray) :
    (uInt256OfByteArray (ByteArray.zeroes n ++ b)).toNat < 2^(8*b.size) := by
  rw [uInt256OfByteArray_eq,fromByteArrayBigEndian_zeroes_append]
  have hb : fromByteArrayBigEndian b < 2^(8*b.size) := by
    simpa only [fromByteArrayBigEndian,byteArray_toList_eq,Array.length_toList] using
      fromBytesBigEndian_bound b.toList
  exact lt_of_le_of_lt (Nat.mod_le _ _) hb

-- LIBRARY CANDIDATE: the full shape of the ECRECOVER precompile's return data.
def EcrecoverOutput (out : ByteArray) : Prop :=
  out = ByteArray.empty ∨ ∃ a : AccountAddress, out = (UInt256.ofNat a.val).toByteArray

theorem ecrecoverOutput_precompile (σ : AccountMap) (gas : UInt256) (A : Substate) (I : ExecutionEnv) :
    EcrecoverOutput (Ξ_ECREC σ gas A I).2.2.2 := by
  unfold Ξ_ECREC
  dsimp
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · split
      · rename_i pubKey hpub
        right
        have hs (b : ByteArray) : (ByteArray.zeroes 12 ++ (KEC b).extract 12 32).size = 32 := by
          simp only [ByteArray.size_append,ByteArray_zeroes_size,ByteArray.size_extract,keccak_size]
          rfl
        have hb (b : ByteArray) :
            (uInt256OfByteArray (ByteArray.zeroes 12 ++ (KEC b).extract 12 32)).toNat < AccountAddress.size := by
          simpa only [ByteArray.size_extract,keccak_size] using
            uInt256OfByteArray_zeroes_bound 12 ((KEC b).extract 12 32)
        refine ⟨⟨_,hb pubKey⟩,?_⟩
        rw [u256_ofNat_toNat]
        exact (toByteArray_uInt256OfByteArray_of_size32 (hs pubKey)).symm
      · exact Or.inl rfl

-- GENERALIZES Reasoning.ExternalCall.staticcallTheta_ecrecover_output_size with canonical addresses.
theorem ecrecoverOutput_theta {fork : Ethereum.Fork}
    {blobVersionedHashes blocks σ σ₀ A_in r s gas p value value' data depth H perm σ' gas' A' z out}
    (hΘ : (σ',gas',A',z,out) =
      Θ fork σ σ₀ A_in r s (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
        (toExecute fork σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
        gas p value value' data depth H blobVersionedHashes blocks perm) :
    EcrecoverOutput out := by
  have hout := congrArg (fun x => x.2.2.2.2) hΘ
  change out = _ at hout
  rw [hout]
  unfold Θ
  rw [toExecute_ecrecover_precompile,show AccountAddress.ofUInt256 (⟨1⟩ : UInt256) = 1 by decide]
  dsimp
  exact ecrecoverOutput_precompile _ _ _ _

-- LIBRARY CANDIDATE: retain precompile output facts through the source call relation's same Θ witness.
theorem ecrecoverOutput_call {evm evm' : EVM.State} {data out : ByteArray} {z perm : Bool} {value : Int}
    (hc : callViaEVM fork evm (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) value data (z,evm',out) perm) :
    EcrecoverOutput out := by
  cases hc with
  | callMade hv hΘ he hbal hd =>
    obtain ⟨gas,A,hΘ⟩ := hΘ
    exact ecrecoverOutput_theta hΘ
  | callNotMade he hs hd => exact Or.inl rfl

end Benchmarks.EAS.EAS
