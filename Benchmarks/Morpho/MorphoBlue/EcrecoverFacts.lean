import Benchmarks.Morpho.MorphoBlue.ScalarSliceABI
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: the structural output guarantee of the ECRECOVER precompile.
def EcrecoverOutput (out : ByteArray) : Prop :=
  out = ByteArray.empty ∨ ∃ payload : ByteArray, payload.size = 20 ∧ out = ByteArray.zeroes 12 ++ payload

theorem ecrecover_output_shape (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    EcrecoverOutput (Ξ_ECREC σ g A I).2.2.2 := by
  unfold Ξ_ECREC
  dsimp
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inr ⟨_, by rw [ByteArray.size_extract, keccak_size]; rfl, rfl⟩
      · exact Or.inl rfl

theorem theta_ecrecover_output_shape
    {blobVersionedHashes blocks σ σ₀ A_in r s g p v v' d e H w σ' g' A' z o}
    (hΘ : (σ', g', A', z, o) = Θ σ σ₀ A_in r s
      (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
      (toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
      g p v v' d e H blobVersionedHashes blocks w) : EcrecoverOutput o := by
  have hout := congrArg (fun x => x.2.2.2.2) hΘ
  dsimp only at hout
  rw [hout]
  unfold Θ
  rw [toExecute_ecrecover_precompile σ,
    show AccountAddress.ofUInt256 (⟨1⟩ : UInt256) = 1 by decide]
  dsimp
  exact ecrecover_output_shape _ _ _ _

theorem callViaEVM_ecrecover_output_shape {evm evm' : EVM.State} {value : Int}
    {cd out : ByteArray} {z perm : Bool}
    (h : callViaEVM evm (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) value cd (z, evm', out) perm) :
    EcrecoverOutput out := by
  cases h with
  | callNotMade => exact Or.inl rfl
  | callMade hw ht he hb hd =>
    obtain ⟨gas, A, hΘ⟩ := ht
    exact theta_ecrecover_output_shape hΘ

theorem EcrecoverOutput.size {out : ByteArray} (ho : EcrecoverOutput out) :
    out.size = 0 ∨ out.size = 32 := by
  rcases ho with rfl | ⟨payload, hp, rfl⟩
  · exact Or.inl rfl
  · right; rw [ByteArray.size_append, ByteArray_zeroes_size, hp]

theorem EcrecoverOutput.canonical {out : ByteArray} (ho : EcrecoverOutput out) (hs : out.size = 32) :
    (calldataWord out 0).toNat < EVM.addressModulus := by
  rcases ho with rfl | ⟨payload, hp, rfl⟩
  · contradiction
  · have hread : (ByteArray.zeroes 12 ++ payload).readBytes 0 32 = ByteArray.zeroes 12 ++ payload := by
      apply byteArray_eq_of_toList_eq
      rw [byteArray_toList_eq, byteArray_toList_eq,
        readBytes_at_toList_any _ 0 (by omega), List.drop_zero]
      apply List.take_of_length_le
      simpa only [Array.length_toList] using Nat.le_of_eq hs
    have hz : fromByteArrayBigEndian (ByteArray.zeroes 12) = 0 := by
      simp only [fromByteArrayBigEndian, fromBytesBigEndian, Function.comp_apply,
        byteArray_toList_eq, byteArray_zeroes_toList, List.reverse_replicate, fromBytes'_replicate_zero]
    have hb : fromByteArrayBigEndian payload < 2 ^ 160 := by
      have h := fromBytesBigEndian_bound payload.toList
      have hlen : payload.toList.length = 20 := by
        rw [byteArray_toList_eq, Array.length_toList]; exact hp
      simpa only [hlen] using h
    rw [calldataWord, hread, uInt256OfByteArray_eq, fromByteArrayBigEndian_append, hz,
      Nat.zero_mul, Nat.zero_add, UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)]
    exact hb


-- LIBRARY CANDIDATE: a complete canonical address word decodes in modern ABI mode.
theorem decodeAddressWord32 {out : ByteArray} (hs : out.size = 32)
    (hc : (calldataWord out 0).toNat < EVM.addressModulus) :
    decodeReturnValueWithMode? .modern abiAddress out =
      some (.address (AccountAddress.ofNat (calldataWord out 0).toNat)) := by
  have hd := decodeScalarWord_extract (ty := abiAddress) (cd := out)
    (start := 0) (stop := out.size) (off := 0) (by omega) le_rfl
  rw [byteArray_extract_self] at hd
  simp only [Nat.zero_add, decodeABIWord?, show (calldataWord out 0).val.val < EVM.addressModulus from hc,
    ↓reduceIte, Option.map_some] at hd
  apply decodeReturnValue_static rfl rfl (by rw [hs]; decide)
  rw [decodeABIValue_scalarWord_eq (by decide), hd]
  rfl

-- LIBRARY CANDIDATE: the word produced when a precompile result is copied into a zeroed slot.
def ecrecoverWord (out : ByteArray) : UInt256 :=
  if out.size = 0 then UInt256.ofNat 0 else calldataWord out 0

theorem EcrecoverOutput.wordCanonical {out : ByteArray} (ho : EcrecoverOutput out) :
    (ecrecoverWord out).toNat < EVM.addressModulus := by
  rcases ho.size with hz | hs
  · simp only [ecrecoverWord, hz, ↓reduceIte]; decide
  · simpa only [ecrecoverWord, hs, show (32 : Nat) ≠ 0 by decide, ↓reduceIte] using ho.canonical hs


end Benchmarks.Morpho.MorphoBlue
