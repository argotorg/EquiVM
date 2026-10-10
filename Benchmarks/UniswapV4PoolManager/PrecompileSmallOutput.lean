import Benchmarks.UniswapV4PoolManager.MemoryGas

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES the fixed precompile output bounds to their shared 64-byte maximum.
lemma precompile_ECREC_output_size_le_64
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_ECREC σ g A I).2.2.2.size ≤ 64 := by
  have h12 : (OfNat.ofNat 12 : USize).toNat = 12 := by
    apply USize.toNat_ofNat_of_le_of_lt (n := 12) (i := 12)
    · rcases System.Platform.numBits_eq with h | h <;> rw [USize.size, h] <;> norm_num
    · rfl
  unfold Ξ_ECREC
  by_cases hgas : g.toNat < 3000
  · simp [hgas, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [hgas]
    split
    · simp [maxReturnDataSizeByGas, maxReturnDataWordsByGas]
    · split
      · simp [ByteArray.size_append, ByteArray_zeroes_size, ByteArray.size_extract,
          maxReturnDataSizeByGas, maxReturnDataWordsByGas]
        omega
      · simp [dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

lemma precompile_SHA256_output_size_le_64
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_SHA256 σ g A I).2.2.2.size ≤ 64 := by
  by_cases hgas : g.toNat < 60 + 12 * ((I.calldata.size + 31) / 32)
  · simp [Ξ_SHA256, hgas, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [Ξ_SHA256, hgas]
    cases hres : ffi.SHA256 I.calldata with
    | ok s =>
        have hs := ffi_SHA256_ok_output_size hres
        simp [hs, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
    | error e =>
        simp [dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

lemma precompile_RIP160_output_size_le_64
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_RIP160 σ g A I).2.2.2.size ≤ 64 := by
  by_cases hgas : g.toNat < 600 + 120 * ((I.calldata.size + 31) / 32)
  · simp [Ξ_RIP160, hgas, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [Ξ_RIP160, hgas]
    cases hres : RIP160 I.calldata with
    | ok s =>
        have hs := RIP160_ok_output_size hres
        simp [hs, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
    | error e =>
        simp [dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

lemma precompile_BN_ADD_output_size_le_64
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_BN_ADD σ g A I).2.2.2.size ≤ 64 := by
  by_cases hgas : g.toNat < 150
  · simp [Ξ_BN_ADD, hgas, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [Ξ_BN_ADD, hgas]
    cases hres : BN_ADD (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
        (I.calldata.readBytes 64 32) (I.calldata.readBytes 96 32) with
    | ok s =>
        have hs := BN_ADD_ok_output_size hres
        simp [hs, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
    | error e =>
        simp [dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

lemma precompile_BN_MUL_output_size_le_64
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_BN_MUL σ g A I).2.2.2.size ≤ 64 := by
  by_cases hgas : g.toNat < 6000
  · simp [Ξ_BN_MUL, hgas, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [Ξ_BN_MUL, hgas]
    cases hres : BN_MUL (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
        (I.calldata.readBytes 64 32) with
    | ok s =>
        have hs := BN_MUL_ok_output_size hres
        simp [hs, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
    | error e =>
        simp [dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

lemma precompile_SNARKV_output_size_le_64
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_SNARKV σ g A I).2.2.2.size ≤ 64 := by
  by_cases hgas : g.toNat < 34000 * (I.calldata.size / 192) + 45000
  · simp [Ξ_SNARKV, hgas, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [Ξ_SNARKV, hgas]
    cases hres : SNARKV I.calldata with
    | ok s =>
        have hs := SNARKV_ok_output_size hres
        simp [hs, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
    | error e =>
        simp [dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

lemma precompile_BLAKE2_F_output_size_le_64
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_BLAKE2_F σ g A I).2.2.2.size ≤ 64 := by
  by_cases hgas : g.toNat < fromByteArrayBigEndian (I.calldata.extract 0 4)
  · simp [Ξ_BLAKE2_F, hgas, dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [Ξ_BLAKE2_F, hgas]
    cases hres : ffi.BLAKE2 I.calldata with
    | ok s =>
        have hs := ffi_BLAKE2_ok_output_size hres
        simp [hs, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
    | error e =>
        simp [dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

lemma precompile_PointEval_output_size_le_64
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_PointEval σ g A I).2.2.2.size ≤ 64 := by
  by_cases hgas : g.toNat < 50000
  · simp [Ξ_PointEval, hgas, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [Ξ_PointEval, hgas]
    cases hres : PointEval I.calldata with
    | ok s =>
        have hs := PointEval_ok_output_size hres
        simp [hs, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
    | error e =>
        simp [dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

end Benchmarks.UniswapV4PoolManager
