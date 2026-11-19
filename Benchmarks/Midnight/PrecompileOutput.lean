import Benchmarks.Midnight.GasOutput

/-! Osaka precompiles return at most 1024 bytes, apart from the identity precompile. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES Ethereum.EVM.precompile_dispatch_output_size_le_maxReturnDataSizeByGas_or_calldata
-- to the smaller bound justified by the Osaka fork.
lemma precompile_ECREC_output_size_le_1024_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_ECREC σ g A I).2.2.2.size ≤ max 1024 I.calldata.size := by
  have h12 : (OfNat.ofNat 12 : USize).toNat = 12 := by
    apply USize.toNat_ofNat_of_le_of_lt (n := 12) (i := 12)
    · rcases System.Platform.numBits_eq with h | h <;> rw [USize.size, h] <;> norm_num
    · rfl
  unfold Ξ_ECREC
  by_cases hgas : g.toNat < 3000
  · simp [hgas]
  · simp [hgas]
    left
    split
    · simp
    · split
      · simp [ByteArray.size_append, ByteArray_zeroes_size, ByteArray.size_extract]
        omega
      · simp [dbgTrace]

lemma precompile_SHA256_output_size_le_1024_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_SHA256 σ g A I).2.2.2.size ≤ max 1024 I.calldata.size := by
  by_cases hgas : g.toNat < 60 + 12 * ((I.calldata.size + 31) / 32)
  · simp [Ξ_SHA256, hgas]
  · simp [Ξ_SHA256, hgas]
    cases hres : SHA256 I.calldata with
    | ok s =>
        have hs := SHA256_ok_output_size hres
        simp [hs]
    | error e =>
        simp [dbgTrace]

lemma precompile_RIP160_output_size_le_1024_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_RIP160 σ g A I).2.2.2.size ≤ max 1024 I.calldata.size := by
  by_cases hgas : g.toNat < 600 + 120 * ((I.calldata.size + 31) / 32)
  · simp [Ξ_RIP160, hgas]
  · simp [Ξ_RIP160, hgas]
    cases hres : RIP160 I.calldata with
    | ok s =>
        have hs := RIP160_ok_output_size hres
        simp [hs]
    | error e =>
        simp [dbgTrace]

lemma precompile_ID_output_size_le_1024_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_ID σ g A I).2.2.2.size ≤ max 1024 I.calldata.size := by
  by_cases hgas : g.toNat <
      (let l := I.calldata.size
       let ceil := (l + 31) / 32
       15 + 3 * ceil)
  · simp [Ξ_ID, hgas]
  · exact Nat.le_trans (by simp [Ξ_ID, hgas]) (le_max_right _ _)

lemma precompile_BN_ADD_output_size_le_1024_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_BN_ADD σ g A I).2.2.2.size ≤ max 1024 I.calldata.size := by
  by_cases hgas : g.toNat < 150
  · simp [Ξ_BN_ADD, hgas]
  · simp [Ξ_BN_ADD, hgas]
    cases hres : BN_ADD (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
        (I.calldata.readBytes 64 32) (I.calldata.readBytes 96 32) with
    | ok s =>
        have hs := BN_ADD_ok_output_size hres
        simp [hs]
    | error e =>
        simp [dbgTrace]

lemma precompile_BN_MUL_output_size_le_1024_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_BN_MUL σ g A I).2.2.2.size ≤ max 1024 I.calldata.size := by
  by_cases hgas : g.toNat < 6000
  · simp [Ξ_BN_MUL, hgas]
  · simp [Ξ_BN_MUL, hgas]
    cases hres : BN_MUL (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
        (I.calldata.readBytes 64 32) with
    | ok s =>
        have hs := BN_MUL_ok_output_size hres
        simp [hs]
    | error e =>
        simp [dbgTrace]

lemma precompile_SNARKV_output_size_le_1024_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_SNARKV σ g A I).2.2.2.size ≤ max 1024 I.calldata.size := by
  by_cases hgas : g.toNat < 34000 * (I.calldata.size / 192) + 45000
  · simp [Ξ_SNARKV, hgas]
  · simp [Ξ_SNARKV, hgas]
    cases hres : SNARKV I.calldata with
    | ok s =>
        have hs := SNARKV_ok_output_size hres
        simp [hs]
    | error e =>
        simp [dbgTrace]

lemma precompile_BLAKE2_F_output_size_le_1024_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_BLAKE2_F σ g A I).2.2.2.size ≤ max 1024 I.calldata.size := by
  by_cases hgas : g.toNat < fromByteArrayBigEndian (I.calldata.extract 0 4)
  · simp [Ξ_BLAKE2_F, hgas, dbgTrace]
  · simp [Ξ_BLAKE2_F, hgas]
    cases hres : BLAKE2_F I.calldata with
    | ok s =>
        have hs := BLAKE2_F_ok_output_size hres
        simp [hs]
    | error e =>
        simp [dbgTrace]

lemma precompile_PointEval_output_size_le_1024_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_PointEval σ g A I).2.2.2.size ≤ max 1024 I.calldata.size := by
  by_cases hgas : g.toNat < 50000
  · simp [Ξ_PointEval, hgas]
  · simp [Ξ_PointEval, hgas]
    cases hres : PointEval I.calldata with
    | ok s =>
        have hs := PointEval_ok_output_size hres
        simp [hs]
    | error e =>
        simp [dbgTrace]

lemma precompile_BLS12_381_output_size_le_1024_or_calldata
    {op : ℕ} {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_BLS12_381 op σ g A I).2.2.2.size ≤ max 1024 I.calldata.size := by
  have h64 : 256 ≤ 1024 := by decide
  unfold Ξ_BLS12_381
  by_cases hgas : g.toNat < blsRequiredGas op I.calldata.size
  · simp [hgas]
  · simp only [hgas, if_false]
    cases hres : BLS12_381 op I.calldata with
    | ok out =>
      have hs := BLS12_381_ok_size hres
      have hle : blsOutputSize op ≤ 256 := by
        unfold blsOutputSize Ethereum.Crypto.BLS12_381.outputSize; split <;> omega
      exact le_max_of_le_left (by simp only; omega)
    | error e => simp

lemma precompile_P256VERIFY_output_size_le_1024_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_P256VERIFY σ g A I).2.2.2.size ≤ max 1024 I.calldata.size := by
  have h64 : 256 ≤ 1024 := by decide
  unfold Ξ_P256VERIFY
  by_cases hgas : g.toNat < 6900
  · simp [hgas]
  · simp only [hgas, if_false]
    cases hres : P256Verify I.calldata with
    | ok out =>
      have := P256Verify_ok_output_size_le hres
      exact le_max_of_le_left (by simp only; omega)
    | error e => simp [dbgTrace]

theorem precompile_EXPMOD_output_size_le_1024
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hosaka : I.fork ≥ .osaka) : (Ξ_EXPMOD σ g A I).2.2.2.size ≤ 1024 := by
  cases hreq : expmodRequiredGas I.fork I.calldata with
  | none => simp [Ξ_EXPMOD, hreq]
  | some gas =>
    have hlen : nat_of_slice I.calldata 64 32 ≤ 1024 := by
      by_contra hbig
      have hbig' : nat_of_slice I.calldata 64 32 > 1024 := by omega
      simp [expmodRequiredGas, hosaka, hbig'] at hreq
    exact precompile_EXPMOD_output_size_le_modulus_length.trans hlen

theorem precompile_dispatch_output_size_le_1024_or_calldata
    (pc : AccountAddress) (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (hosaka : I.fork ≥ .osaka) :
    (Ξ_PRECOMPILE pc σ g A I).2.2.2.size ≤ max 1024 I.calldata.size :=
  Ξ_PRECOMPILE_induction (fun r ↦ r.2.2.2.size ≤ max 1024 I.calldata.size)
    precompile_ECREC_output_size_le_1024_or_calldata
    precompile_SHA256_output_size_le_1024_or_calldata
    precompile_RIP160_output_size_le_1024_or_calldata
    precompile_ID_output_size_le_1024_or_calldata
    ((precompile_EXPMOD_output_size_le_1024 hosaka).trans (le_max_left _ _))
    precompile_BN_ADD_output_size_le_1024_or_calldata
    precompile_BN_MUL_output_size_le_1024_or_calldata
    precompile_SNARKV_output_size_le_1024_or_calldata
    precompile_BLAKE2_F_output_size_le_1024_or_calldata
    precompile_PointEval_output_size_le_1024_or_calldata
    (fun _ ↦ precompile_BLS12_381_output_size_le_1024_or_calldata)
    precompile_P256VERIFY_output_size_le_1024_or_calldata
    (Nat.zero_le _)

theorem theta_precompiled_output_size_le_1024_or_calldata
    (fork : Fork) (σ σ₀ : AccountMap) (A : Substate) (s o r pc : AccountAddress)
    (d : ByteArray) (g p v v' : UInt256) (e : Fin 1025) (H : BlockHeader)
    (blobVersionedHashes : List ByteArray) (blocks : ProcessedBlocks) (w : Bool)
    (hosaka : fork ≥ .osaka) :
    (Θ fork σ σ₀ A s o r (.Precompiled pc) g p v v' d e H
      blobVersionedHashes blocks w).2.2.2.2.size ≤ max 1024 d.size := by
  unfold Θ
  simp only
  exact precompile_dispatch_output_size_le_1024_or_calldata pc _ g A _ hosaka

theorem theta_output_memoryCost_or_small
    (fork : Fork) (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (todo : ToExecute) (d : ByteArray) (g p v v' : UInt256) (e : Fin 1025) (H : BlockHeader)
    (blobVersionedHashes : List ByteArray) (blocks : ProcessedBlocks) (w : Bool)
    (hosaka : fork ≥ .osaka) :
    (Θ fork σ σ₀ A s o r todo g p v v' d e H
      blobVersionedHashes blocks w).2.2.2.2.size ≤ max 1024 d.size ∨
    memoryCost (((Θ fork σ σ₀ A s o r todo g p v v' d e H
      blobVersionedHashes blocks w).2.2.2.2.size + 31) / 32) ≤ g.toNat := by
  cases todo with
  | Code code =>
    exact Or.inr (theta_code_output_memoryCost fork σ σ₀ A s o r code d g p v v' e H
      blobVersionedHashes blocks w)
  | Precompiled pc =>
    exact Or.inl (theta_precompiled_output_size_le_1024_or_calldata fork σ σ₀ A s o r pc
      d g p v v' e H blobVersionedHashes blocks w hosaka)

end Benchmarks.Midnight
