import Benchmarks.Morpho.MetaMorphoV1_1.Common
import Reasoning.ExternalCall

/-! The recovery precompile returns either no bytes or one canonical address word. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def EcrecoverOutput (out : ByteArray) : Prop :=
  out = ByteArray.empty ∨ out.size = 32 ∧ (uInt256OfByteArray out).toNat < 2 ^ 160

theorem ecrecoverPaddedHash (bytes : ByteArray) :
    EcrecoverOutput (ByteArray.zeroes 12 ++ (KEC bytes).extract 12 32) := by
  have hs : ((KEC bytes).extract 12 32).size = 20 := by
    rw [ByteArray.size_extract, keccak_size]; decide
  have hb : fromByteArrayBigEndian ((KEC bytes).extract 12 32) < 2 ^ 160 := by
    simpa only [hs] using fromByteArrayBigEndian_lt ((KEC bytes).extract 12 32)
  have hz : fromByteArrayBigEndian (ByteArray.zeroes 12) = 0 := by native_decide
  have hv : fromByteArrayBigEndian (ByteArray.zeroes 12 ++ (KEC bytes).extract 12 32) <
      2 ^ 160 := by
    rw [fromByteArrayBigEndian_append, hz, Nat.zero_mul, Nat.zero_add]
    exact hb
  refine .inr ⟨?_, ?_⟩
  · rw [ByteArray.size_append, ByteArray_zeroes_size, hs]
  · rw [uInt256OfByteArray_eq, UInt256.toNat_ofNat_of_lt
      (lt_trans hv (by decide))]
    exact hv

theorem ecrecoverOutput (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    EcrecoverOutput (Ξ_ECREC σ g A I).2.2.2 := by
  unfold Ξ_ECREC
  dsimp
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · split
      · exact ecrecoverPaddedHash _
      · exact .inl rfl

theorem thetaEcrecoverOutput
    {blobVersionedHashes blocks σ σ₀ A_in r s g p value value' d e H w σ' g' A' z out}
    (hΘ : (σ', g', A', z, out) =
      Θ σ σ₀ A_in r s (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
        (toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
        g p value value' d e H blobVersionedHashes blocks w) :
    EcrecoverOutput out := by
  have hout := congrArg (fun x ↦ x.2.2.2.2) hΘ
  change out = _ at hout
  rw [hout]
  unfold Θ
  rw [toExecute_ecrecover_precompile,
    show AccountAddress.ofUInt256 (⟨1⟩ : UInt256) = 1 by decide]
  dsimp
  exact ecrecoverOutput _ g A_in _

theorem callEcrecoverOutput {evm evm' : State} {input out : ByteArray} {ok : Bool}
    (hcall : callViaEVM evm (AccountAddress.ofNat 1) 0 input (ok, evm', out) false) :
    EcrecoverOutput out := by
  cases hcall with
  | callMade hvalue hΘ hevm hbalance hdepth =>
      obtain ⟨gas, substate, hΘ⟩ := hΘ
      exact thetaEcrecoverOutput hΘ
  | callNotMade hsubstate hevm hfail => exact .inl rfl

end Benchmarks.Morpho.MetaMorphoV1_1
