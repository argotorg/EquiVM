import Examples.UniswapV2Pair.StackRoutines
import Examples.UniswapV2Pair.BurnAmountsRuntime
import Examples.UniswapV2Pair.ErrorStringCopyRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeAmountsGuardCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {totalSupply feeOn liquidity balance0 balance1
      token0 token1 reserve0 reserve1 amount0 amount1 : UInt256} {R : List UInt256} {k C : ℕ}
    (rd4533 : RD uniswapV2PairBytecode I g s0 ⟨4533⟩
      (totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: token1 :: token0 ::
        reserve1 :: reserve0 :: amount1 :: amount0 :: R)
      mem feeToStaticcallActiveWords rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 24 ≤ 1024) :
    (¬ (0 < amount0.toNat ∧ 0 < amount1.toNat)) ∧ RDrev uniswapV2PairBytecode g s0 ∨
    (0 < amount0.toNat ∧ 0 < amount1.toNat) ∧ ∃ k' C',
      RD uniswapV2PairBytecode I g s0 ⟨8302⟩
        (liquidity :: UInt256.ofNat I.codeOwner.val :: ⟨4617⟩ ::
          totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: token1 :: token0 ::
          reserve1 :: reserve0 :: amount1 :: amount0 :: R)
        mem feeToStaticcallActiveWords rdata acc k' C' := by
  have hto4548 : ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨4548⟩
      ((if 0 < amount0.toNat ∧ 0 < amount1.toNat then ⟨1⟩ else ⟨0⟩) ::
        totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: token1 :: token0 ::
        reserve1 :: reserve0 :: amount1 :: amount0 :: R)
      mem feeToStaticcallActiveWords rdata acc k' C' := by
    have rd4542 := evm_run rd4533 with [push1 ⟨0⟩, dup12, gt, dup1, iszero, push2 ⟨4548⟩]
    by_cases hp0 : 0 < amount0.toNat
    · rw [ugt_one (by exact hp0)] at rd4542
      have rd4548 := evm_run rd4542 with [jumpiNT (by decide), pop, push1 ⟨0⟩, dup11, gt]
      by_cases hp1 : 0 < amount1.toNat
      · rw [ugt_one (by exact hp1)] at rd4548
        simpa only [hp0, hp1, and_self, ite_true] using ⟨_, _, rd4548⟩
      · rw [ugt_zero (by change amount1.toNat ≤ 0; omega)] at rd4548
        simpa only [hp1, and_false, ite_false] using ⟨_, _, rd4548⟩
    · rw [ugt_zero (by change amount0.toNat ≤ 0; omega)] at rd4542
      have rd4548 := evm_run rd4542 with [jumpiT (by decide) (by jump_dest)]
      simpa only [hp0, false_and, ite_false] using ⟨_, _, rd4548⟩
  obtain ⟨_, _, rd4548⟩ := hto4548
  by_cases hpos : 0 < amount0.toNat ∧ 0 < amount1.toNat
  · simp only [hpos] at rd4548
    have rd4607 := evm_run rd4548 with [jumpdest, push2 ⟨4607⟩,
      jumpiT (by decide) (by jump_dest)]
    have rd8302 := evm_run rd4607 with [jumpdest, push2 ⟨4617⟩, address,
      dup5, push2 ⟨8302⟩, jump (by jump_dest)]
    exact Or.inr ⟨hpos, _, _, rd8302⟩
  · simp only [hpos, ite_false] at rd4548
    have rd4553 := evm_run rd4548 with [jumpdest, push2 ⟨4607⟩, jumpiNT (by decide)]
    exact Or.inl ⟨hpos, RD.solcErrorString40CopyReverts (source := ⟨8701⟩) rd4553
      (by constructor <;> native_decide) (by native_decide) hmem hread64
      (by simp only [List.length_cons]; omega)⟩

end UniswapV2Pair
