import Benchmarks.UniswapV4PoolManager.CalleeReturnGas
import Benchmarks.UniswapV4PoolManager.CallGasEvidence

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: transfer the fresh-execution memory charge through a successful message call.
theorem thetaNonprecompile_success_returnMemoryCost
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {d : ByteArray} {g p v v' : UInt256} {e : Fin 1025} {H : BlockHeader}
    {blob : List ByteArray} {blocks : ProcessedBlocks} {perm : Bool}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {out : ByteArray}
    (hn : r ∉ π)
    (h : Ethereum.EVM.Θ σ σ₀ A s o r (toExecute σ r) g p v v' d e H blob blocks perm =
      (σ', g', A', true, out)) :
    Cₘ (UInt256.ofNat ((out.size+31)/32))+g'.toNat ≤ g.toNat := by
  unfold toExecute at h
  simp only [hn, if_false] at h
  cases hfind : σ.get? r with
  | none =>
    change σ[r]? = none at hfind
    simp [hfind] at h
    exact thetaCode_success_returnMemoryCost h
  | some acc =>
    change σ[r]? = some acc at hfind
    simp [hfind] at h
    exact thetaCode_success_returnMemoryCost h

theorem ZeroCallGasEvidence.memoryCost_le_spent {evm evm' : State}
    {target : AccountAddress} {data out : ByteArray}
    (w : ZeroCallGasEvidence evm target data evm' true out) (hn : target ∉ π) :
    Cₘ (UInt256.ofNat ((out.size+31)/32)) ≤ w.spent := by
  have hc := thetaNonprecompile_success_returnMemoryCost hn w.theta.symm
  dsimp only [ZeroCallGasEvidence.spent]
  omega

end Benchmarks.UniswapV4PoolManager
