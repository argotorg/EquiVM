import Benchmarks.UniswapV4PoolManager.PrecompileSmallOutput
import Benchmarks.UniswapV4PoolManager.PrecompileExpmodGas

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: the native message-call dispatcher, exposed for reply-shape reasoning.
def precompileResult (pc : AccountAddress) (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : AccountMap × UInt256 × Substate × ByteArray :=
  match pc with
  | 1 => Ξ_ECREC σ g A I
  | 2 => Ξ_SHA256 σ g A I
  | 3 => Ξ_RIP160 σ g A I
  | 4 => Ξ_ID σ g A I
  | 5 => Ξ_EXPMOD σ g A I
  | 6 => Ξ_BN_ADD σ g A I
  | 7 => Ξ_BN_MUL σ g A I
  | 8 => Ξ_SNARKV σ g A I
  | 9 => Ξ_BLAKE2_F σ g A I
  | 10 => Ξ_PointEval σ g A I
  | _ => default

theorem precompileResult_reply (pc : AccountAddress) (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) (hb : 2^132 ≤ nat_of_slice I.calldata 0 32) :
    (precompileResult pc σ g A I).2.2.2.size ≤ 64 ∨
      (precompileResult pc σ g A I).2.2.2 = I.calldata := by
  unfold precompileResult
  have hd := precompile_dispatch_match_eq_if pc
    (Ξ_ECREC σ g A I) (Ξ_SHA256 σ g A I) (Ξ_RIP160 σ g A I)
    (Ξ_ID σ g A I) (Ξ_EXPMOD σ g A I) (Ξ_BN_ADD σ g A I)
    (Ξ_BN_MUL σ g A I) (Ξ_SNARKV σ g A I) (Ξ_BLAKE2_F σ g A I)
    (Ξ_PointEval σ g A I) (default : AccountMap × UInt256 × Substate × ByteArray)
  let result : AccountMap × UInt256 × Substate × ByteArray :=
    (if pc = 1 then Ξ_ECREC σ g A I
     else if pc = 2 then Ξ_SHA256 σ g A I
     else if pc = 3 then Ξ_RIP160 σ g A I
     else if pc = 4 then Ξ_ID σ g A I
     else if pc = 5 then Ξ_EXPMOD σ g A I
     else if pc = 6 then Ξ_BN_ADD σ g A I
     else if pc = 7 then Ξ_BN_MUL σ g A I
     else if pc = 8 then Ξ_SNARKV σ g A I
     else if pc = 9 then Ξ_BLAKE2_F σ g A I
     else if pc = 10 then Ξ_PointEval σ g A I
     else default)
  have hr : result.2.2.2.size ≤ 64 ∨ result.2.2.2 = I.calldata := by
    dsimp only [result]
    split_ifs
    · exact .inl precompile_ECREC_output_size_le_64
    · exact .inl precompile_SHA256_output_size_le_64
    · exact .inl precompile_RIP160_output_size_le_64
    · dsimp only [Ξ_ID]
      split
      · exact .inl (by change 0 ≤ 64; decide)
      · exact .inr rfl
    · rw [precompile_EXPMOD_large_base hb]
      exact .inl (by change 0 ≤ 64; decide)
    · exact .inl precompile_BN_ADD_output_size_le_64
    · exact .inl precompile_BN_MUL_output_size_le_64
    · exact .inl precompile_SNARKV_output_size_le_64
    · exact .inl precompile_BLAKE2_F_output_size_le_64
    · exact .inl precompile_PointEval_output_size_le_64
    · exact .inl (by decide)
  exact (congrArg (fun x : AccountMap × UInt256 × Substate × ByteArray =>
    x.2.2.2.size ≤ 64 ∨ x.2.2.2 = I.calldata) hd).symm ▸ hr

theorem thetaPrecompile_reply
    {σ σ₀ : AccountMap} {A : Substate} {s o r pc : AccountAddress}
    {d : ByteArray} {g p v v' : UInt256} {e : Fin 1025} {H : BlockHeader}
    {blob : List ByteArray} {blocks : ProcessedBlocks} {perm : Bool}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray}
    (hb : 2^132 ≤ nat_of_slice d 0 32)
    (h : Ethereum.EVM.Θ σ σ₀ A s o r (.Precompiled pc) g p v v' d e H blob blocks perm =
      (σ', g', A', z, out)) : out.size ≤ 64 ∨ out = d := by
  let σ'₁ := match σ.get? r with
    | none => if v != UInt256.ofNat 0 then σ.insert r {(default : Account) with balance := v} else σ
    | some acc => σ.insert r {acc with balance := acc.balance+v}
  let σ₁ := match σ'₁.get? s with
    | none => σ'₁
    | some acc => σ'₁.insert s {acc with balance := acc.balance-v}
  let I : ExecutionEnv :=
    { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
      source := s, weiValue := v', depth := e, perm := perm, code := default,
      header := H, blobVersionedHashes := blob, blocks := blocks }
  have ho := congrArg (fun result => result.2.2.2.2) h
  unfold Ethereum.EVM.Θ at ho
  simp only at ho
  change (precompileResult pc σ₁ g A I).2.2.2 = out at ho
  have hp := precompileResult_reply pc σ₁ g A I hb
  simpa only [ho] using hp

end Benchmarks.UniswapV4PoolManager
