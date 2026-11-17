import Benchmarks.UniswapV4PoolManager.PrecompileSmallOutput
import Benchmarks.UniswapV4PoolManager.PrecompileExpmodGas

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

-- Keep reply-shape reasoning tied to the dispatcher used by Θ.
def precompileResult (pc : AccountAddress) (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : AccountMap × UInt256 × Substate × ByteArray :=
  Ξ_PRECOMPILE pc σ g A I

private theorem precompile_BLS_output_size_le_256 (op : ℕ) (σ : AccountMap)
    (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BLS12_381 op σ g A I).2.2.2.size ≤ 256 := by
  unfold Ξ_BLS12_381
  by_cases hgas : g.toNat < blsRequiredGas op I.calldata.size
  · simp [hgas]
  · simp only [hgas, if_false]
    cases hresult : BLS12_381 op I.calldata with
    | ok output =>
        have hsize := BLS12_381_ok_size hresult
        have hbound : blsOutputSize op ≤ 256 := by
          unfold blsOutputSize Ethereum.Crypto.BLS12_381.outputSize
          split <;> omega
        simpa [hresult] using hsize.le.trans hbound
    | error e => simp [hresult, dbgTrace]

private theorem precompile_P256_output_size_le_256 (σ : AccountMap) (g : UInt256)
    (A : Substate) (I : ExecutionEnv) :
    (Ξ_P256VERIFY σ g A I).2.2.2.size ≤ 256 := by
  unfold Ξ_P256VERIFY
  by_cases hgas : g.toNat < 6900
  · simp [hgas]
  · simp only [hgas, if_false]
    cases hresult : P256Verify I.calldata with
    | ok output =>
        have hsize := P256Verify_ok_output_size_le hresult
        simpa [hresult] using hsize.trans (by omega : 32 ≤ 256)
    | error e => simp [hresult, dbgTrace]

theorem precompileResult_reply (pc : AccountAddress) (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) (hb : 2^132 ≤ nat_of_slice I.calldata 0 32) :
    (precompileResult pc σ g A I).2.2.2.size ≤ 256 ∨
      (precompileResult pc σ g A I).2.2.2 = I.calldata := by
  unfold precompileResult
  apply Ξ_PRECOMPILE_induction
    (P := fun result => result.2.2.2.size ≤ 256 ∨ result.2.2.2 = I.calldata)
  · exact .inl (precompile_ECREC_output_size_le_64.trans (by omega))
  · exact .inl (precompile_SHA256_output_size_le_64.trans (by omega))
  · exact .inl (precompile_RIP160_output_size_le_64.trans (by omega))
  · dsimp only [Ξ_ID]
    split
    · exact .inl (by change 0 ≤ 256; decide)
    · exact .inr rfl
  · rw [precompile_EXPMOD_large_base hb]
    exact .inl (by change 0 ≤ 256; decide)
  · exact .inl (precompile_BN_ADD_output_size_le_64.trans (by omega))
  · exact .inl (precompile_BN_MUL_output_size_le_64.trans (by omega))
  · exact .inl (precompile_SNARKV_output_size_le_64.trans (by omega))
  · exact .inl (precompile_BLAKE2_F_output_size_le_64.trans (by omega))
  · exact .inl (precompile_PointEval_output_size_le_64.trans (by omega))
  · intro op
    exact .inl (precompile_BLS_output_size_le_256 op σ g A I)
  · exact .inl (precompile_P256_output_size_le_256 σ g A I)
  · exact .inl (by decide)

theorem thetaPrecompile_reply
    {fork : Fork} {σ σ₀ : AccountMap} {A : Substate} {s o r pc : AccountAddress}
    {d : ByteArray} {g p v v' : UInt256} {e : Fin 1025} {H : BlockHeader}
    {blob : List ByteArray} {blocks : ProcessedBlocks} {perm : Bool}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray}
    (hb : 2^132 ≤ nat_of_slice d 0 32)
    (h : Ethereum.EVM.Θ fork σ σ₀ A s o r (.Precompiled pc) g p v v' d e H blob blocks perm =
      (σ', g', A', z, out)) : out.size ≤ 256 ∨ out = d := by
  let σ'₁ := match σ.get? r with
    | none => if v != UInt256.ofNat 0 then σ.insert r {(default : Account) with balance := v} else σ
    | some acc => σ.insert r {acc with balance := acc.balance+v}
  let σ₁ := match σ'₁.get? s with
    | none => σ'₁
    | some acc => σ'₁.insert s {acc with balance := acc.balance-v}
  let I : ExecutionEnv :=
    { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d, fork := fork,
      source := s, weiValue := v', depth := e, perm := perm, code := default,
      header := H, blobVersionedHashes := blob, blocks := blocks }
  have ho := congrArg (fun result => result.2.2.2.2) h
  unfold Ethereum.EVM.Θ at ho
  simp only at ho
  change (precompileResult pc σ₁ g A I).2.2.2 = out at ho
  have hp := precompileResult_reply pc σ₁ g A I hb
  simpa only [ho] using hp

end Benchmarks.UniswapV4PoolManager
