import Benchmarks.UniswapV4PoolManager.CalleeReturnWork
import Benchmarks.UniswapV4PoolManager.CallGasEvidence

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem thetaCode_success_returnWork
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {code d : ByteArray} {g p v v' : UInt256} {e : Fin 1025} {H : BlockHeader}
    {blob : List ByteArray} {blocks : ProcessedBlocks} {perm : Bool}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {out : ByteArray}
    (hn : 0 < memoryFootprint out)
    (h : Ethereum.EVM.Θ σ σ₀ A s o r (.Code code) g p v v' d e H blob blocks perm =
      (σ', g', A', true, out)) :
    Cₘ (UInt256.ofNat ((out.size+31)/32))+memoryFootprint out+4+g'.toNat ≤ g.toNat := by
  obtain ⟨inputAccounts, I, accounts, substate, hx⟩ := thetaCode_success_Xi h
  exact Xi_success_returnWork hn hx

theorem thetaNonprecompile_success_returnWork
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {d : ByteArray} {g p v v' : UInt256} {e : Fin 1025} {H : BlockHeader}
    {blob : List ByteArray} {blocks : ProcessedBlocks} {perm : Bool}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {out : ByteArray}
    (hn : r ∉ π) (hf : 0 < memoryFootprint out)
    (h : Ethereum.EVM.Θ σ σ₀ A s o r (toExecute σ r) g p v v' d e H blob blocks perm =
      (σ', g', A', true, out)) :
    Cₘ (UInt256.ofNat ((out.size+31)/32))+memoryFootprint out+4+g'.toNat ≤ g.toNat := by
  obtain ⟨code, hc⟩ := toExecute_nonprecompile_code (σ := σ) hn
  rw [hc] at h
  exact thetaCode_success_returnWork hf h

theorem ZeroCallGasEvidence.returnWork_le_spent {evm evm' : State}
    {target : AccountAddress} {data out : ByteArray}
    (w : ZeroCallGasEvidence evm target data evm' true out) (hn : target ∉ π)
    (hf : 0 < memoryFootprint out) :
    Cₘ (UInt256.ofNat ((out.size+31)/32))+memoryFootprint out+4 ≤ w.spent := by
  have hc := thetaNonprecompile_success_returnWork hn hf w.theta.symm
  dsimp only [ZeroCallGasEvidence.spent]
  omega

end Benchmarks.UniswapV4PoolManager
