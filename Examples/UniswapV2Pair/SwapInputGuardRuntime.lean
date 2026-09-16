import Examples.UniswapV2Pair.SwapInputRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapSwapInputGuardRuntimeCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw amount1In amount0In : UInt256} {R : List UInt256} {k C : Nat}
    (rd2418 : RD uniswapV2PairBytecode I g s0 ⟨2418⟩
      (amount1In :: amount0In :: R) mem aw rdata acc k C)
    (hov : R.length + 12 ≤ 1024) :
    (¬ (0 < amount0In.toNat ∨ 0 < amount1In.toNat)) ∧ RDrev uniswapV2PairBytecode g s0 ∨
    (0 < amount0In.toNat ∨ 0 < amount1In.toNat) ∧ ∃ k' C',
      RD uniswapV2PairBytecode I g s0 ⟨2491⟩
        (amount1In :: amount0In :: R) mem aw rdata acc k' C' := by
  have hto2432 : ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨2432⟩
      ((if 0 < amount0In.toNat ∨ 0 < amount1In.toNat then ⟨1⟩ else ⟨0⟩) ::
        amount1In :: amount0In :: R) mem aw rdata acc k' C' := by
    have rd2426 := evm_run rd2418 with [push1 ⟨0⟩, dup3, gt, dup1, push2 ⟨2432⟩]
    by_cases hp0 : 0 < amount0In.toNat
    · rw [ugt_one (by exact hp0)] at rd2426
      have rd2432 := evm_run rd2426 with [jumpiT (by decide) (by jump_dest)]
      simpa only [hp0, true_or, ite_true] using ⟨_, _, rd2432⟩
    · rw [ugt_zero (by change amount0In.toNat ≤ 0; omega)] at rd2426
      have rd2432 := evm_run rd2426 with [jumpiNT (by decide), pop, push1 ⟨0⟩, dup2, gt]
      by_cases hp1 : 0 < amount1In.toNat
      · rw [ugt_one (by exact hp1)] at rd2432
        simpa only [hp0, hp1, false_or, ite_true] using ⟨_, _, rd2432⟩
      · rw [ugt_zero (by change amount1In.toNat ≤ 0; omega)] at rd2432
        simpa only [hp0, hp1, false_or, ite_false] using ⟨_, _, rd2432⟩
  obtain ⟨_, _, rd2432⟩ := hto2432
  by_cases hpos : 0 < amount0In.toNat ∨ 0 < amount1In.toNat
  · simp only [hpos, ite_true] at rd2432
    have rd2491 := evm_run rd2432 with [jumpdest, push2 ⟨2491⟩, jumpiT (by decide) (by jump_dest)]
    exact Or.inr ⟨hpos, _, _, rd2491⟩
  · simp only [hpos, ite_false] at rd2432
    have rd2437 := evm_run rd2432 with [jumpdest, push2 ⟨2491⟩, jumpiNT (by decide)]
    exact Or.inl ⟨hpos, RD.solcErrorStringCopyReverts (source := ⟨8632⟩) (len := ⟨36⟩) rd2437
      (by constructor <;> native_decide) (by simp only [List.length_cons]; omega)⟩

end UniswapV2Pair
