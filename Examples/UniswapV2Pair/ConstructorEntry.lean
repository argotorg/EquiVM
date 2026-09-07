import Examples.UniswapV2Pair.ConstructorMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000

set_option maxHeartbeats 1000000 in
theorem uniswapConstructorEntryCases {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairInitcode) (hperm : I.perm = true) :
    (I.weiValue ≠ ⟨0⟩ ∧ RDrev uniswapV2PairInitcode g (initState cA gh bl σ σ₀ g A I)) ∨
    (I.weiValue = ⟨0⟩ ∧ ∃ k C,
      RD uniswapV2PairInitcode I g (initState cA gh bl σ σ₀ g A I) ⟨23⟩ []
        solcFreePtrMem ⟨3⟩ ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨1⟩) k C) := by
  have rd4 := evm_run (RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode) with [push1 ⟨128⟩, push1 ⟨64⟩]
  have rd5 := RD.mstoreWord rd4 (by native_decide) (by evm_ov)
  have rd9 := evm_run rd5 with [push1 ⟨1⟩, push1 ⟨12⟩]
  obtain ⟨_, _, rd10⟩ := rd9.sstore hperm (by native_decide) (by evm_ov)
  have rd16 := evm_run rd10 with [callvalue, dup1, iszero, push2 ⟨21⟩]
  by_cases hz : I.weiValue = ⟨0⟩
  · have hc : I.weiValue.isZero ≠ ⟨0⟩ := by rw [hz]; native_decide
    exact Or.inr ⟨hz, _, _, evm_run rd16 with [jumpiT hc (by native_decide), jumpdest, pop]⟩
  · have hc : I.weiValue.isZero = ⟨0⟩ := isZero_eq_zero_of_ne hz
    have rd20 := evm_run rd16 with [jumpiNT hc, push1 ⟨0⟩, dup1]
    exact Or.inl ⟨hz, RD.revAny rd20 (by native_decide) (by evm_ov)⟩

end UniswapV2Pair
