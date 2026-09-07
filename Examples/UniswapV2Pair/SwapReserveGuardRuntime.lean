import Examples.UniswapV2Pair.SwapOutputGuardRuntime
import Examples.UniswapV2Pair.GetReserves
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapSwapRuntimeReservesLoaded
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {R : List UInt256} {k C : Nat}
    (rd1628 : RD uniswapV2PairBytecode I g s0 ⟨1628⟩ R mem aw rdata (cA, σ) k C)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨1645⟩
      (reserve1Word σ I :: reserve0Word σ I :: R) mem aw rdata (cA, σ) k' C' := by
  have rd2852 := evm_run rd1628 with [jumpdest, push1 ⟨0⟩, dup1, push2 ⟨1639⟩,
    push2 ⟨2852⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1639⟩ := RD.uniswapGetReservesRoutine rd2852 (by jump_dest) (by evm_ov)
  have rd1645 := evm_run rd1639 with [jumpdest, pop, swap2, pop, swap2, pop]
  exact ⟨_, _, rd1645⟩

set_option maxHeartbeats 1000000 in
theorem uniswapSwapReserveGuardRuntimeCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw reserve1 reserve0 dataLen dataPtr toWord amount1Out amount0Out : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd1645 : RD uniswapV2PairBytecode I g s0 ⟨1645⟩
      (reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R)
      mem aw rdata acc k C)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hov : R.length + 17 ≤ 1024) :
    (¬ (amount0Out.toNat < reserve0.toNat ∧ amount1Out.toNat < reserve1.toNat)) ∧
      RDrev uniswapV2PairBytecode g s0 ∨
    (amount0Out.toNat < reserve0.toNat ∧ amount1Out.toNat < reserve1.toNat) ∧ ∃ k' C',
      RD uniswapV2PairBytecode I g s0 ⟨1735⟩
        (reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R)
        mem aw rdata acc k' C' := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ = reserve112Mask := by native_decide
  have hto1676 : ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨1676⟩
      ((if amount0Out.toNat < reserve0.toNat ∧ amount1Out.toNat < reserve1.toNat then ⟨1⟩ else ⟨0⟩) ::
        reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R)
      mem aw rdata acc k' C' := by
    have rd1662 := evm_run rd1645 with [dup2, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩,
      shl, sub, and, dup8, lt, dup1, iszero, push2 ⟨1676⟩]
    rw [hmask, u256_land_comm reserve112Mask, hclean0] at rd1662
    by_cases hp0 : amount0Out.toNat < reserve0.toNat
    · rw [ult_one hp0] at rd1662
      have rd1676 := evm_run rd1662 with [jumpiNT (by decide), pop, dup1, push1 ⟨1⟩,
        push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, and, dup7, lt]
      rw [hmask, u256_land_comm reserve112Mask, hclean1] at rd1676
      by_cases hp1 : amount1Out.toNat < reserve1.toNat
      · rw [ult_one hp1] at rd1676
        simpa only [hp0, hp1, and_self, ite_true] using ⟨_, _, rd1676⟩
      · rw [ult_zero (by exact Nat.le_of_not_lt hp1)] at rd1676
        simpa only [hp1, and_false, ite_false] using ⟨_, _, rd1676⟩
    · rw [ult_zero (by exact Nat.le_of_not_lt hp0)] at rd1662
      have rd1676 := evm_run rd1662 with [jumpiT (by decide) (by jump_dest)]
      simpa only [hp0, false_and, ite_false] using ⟨_, _, rd1676⟩
  obtain ⟨_, _, rd1676⟩ := hto1676
  by_cases hfit : amount0Out.toNat < reserve0.toNat ∧ amount1Out.toNat < reserve1.toNat
  · simp only [hfit] at rd1676
    have rd1735 := evm_run rd1676 with [jumpdest, push2 ⟨1735⟩, jumpiT (by decide) (by jump_dest)]
    exact Or.inr ⟨hfit, _, _, rd1735⟩
  · simp only [hfit, ite_false] at rd1676
    have rd1681 := evm_run rd1676 with [jumpdest, push2 ⟨1735⟩, jumpiNT (by decide)]
    exact Or.inl ⟨hfit, RD.solcErrorStringCopyReverts (source := ⟨8668⟩) (len := ⟨33⟩) rd1681
      (by constructor <;> native_decide) (by simp only [List.length_cons]; omega)⟩

end UniswapV2Pair
