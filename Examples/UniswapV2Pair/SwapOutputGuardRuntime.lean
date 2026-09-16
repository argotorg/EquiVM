import Examples.UniswapV2Pair.SwapLock
import Examples.UniswapV2Pair.ErrorStringCopyCore
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapSwapOutputGuardRuntimeCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw dataLen dataPtr toWord amount1Out amount0Out : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd1556 : RD uniswapV2PairBytecode I g s0 ⟨1556⟩
      (dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k C)
    (hov : R.length + 15 ≤ 1024) :
    (¬ (0 < amount0Out.toNat ∨ 0 < amount1Out.toNat)) ∧ RDrev uniswapV2PairBytecode g s0 ∨
    (0 < amount0Out.toNat ∨ 0 < amount1Out.toNat) ∧ ∃ k' C',
      RD uniswapV2PairBytecode I g s0 ⟨1628⟩
        (dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k' C' := by
  have hto1569 : ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨1569⟩
      ((if 0 < amount0Out.toNat ∨ 0 < amount1Out.toNat then ⟨1⟩ else ⟨0⟩) ::
        dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k' C' := by
    have rd1563 := evm_run rd1556 with [dup5, iszero, iszero, dup1, push2 ⟨1569⟩]
    by_cases hp0 : 0 < amount0Out.toNat
    · have hnz : amount0Out ≠ ⟨0⟩ := by intro h; rw [h] at hp0; contradiction
      rw [isZero_eq_zero_of_ne hnz] at rd1563
      have rd1569 := evm_run rd1563 with [jumpiT (by decide) (by jump_dest)]
      simpa only [hp0, true_or, ite_true] using ⟨_, _, rd1569⟩
    · have hz : amount0Out = ⟨0⟩ := uint256_toNat_eq_zero (by omega)
      rw [hz] at rd1563
      have rd1564 := evm_run rd1563 with [jumpiNT (by decide)]
      have rd1569 := evm_run rd1564 with [pop, push1 ⟨0⟩, dup5, gt]
      by_cases hp1 : 0 < amount1Out.toNat
      · rw [ugt_one (by exact hp1)] at rd1569
        simpa only [hp0, hp1, false_or, ite_true, hz] using ⟨_, _, rd1569⟩
      · rw [ugt_zero (by change amount1Out.toNat ≤ 0; omega)] at rd1569
        simpa only [hp0, hp1, false_or, ite_false, hz] using ⟨_, _, rd1569⟩
  obtain ⟨_, _, rd1569⟩ := hto1569
  by_cases hpos : 0 < amount0Out.toNat ∨ 0 < amount1Out.toNat
  · simp only [hpos, ite_true] at rd1569
    have rd1628 := evm_run rd1569 with [jumpdest, push2 ⟨1628⟩, jumpiT (by decide) (by jump_dest)]
    exact Or.inr ⟨hpos, _, _, rd1628⟩
  · simp only [hpos, ite_false] at rd1569
    have rd1574 := evm_run rd1569 with [jumpdest, push2 ⟨1628⟩, jumpiNT (by decide)]
    exact Or.inl ⟨hpos, RD.solcErrorStringCopyReverts (source := ⟨8595⟩) (len := ⟨37⟩) rd1574
      (by constructor <;> native_decide) (by simp only [List.length_cons]; omega)⟩
end UniswapV2Pair
