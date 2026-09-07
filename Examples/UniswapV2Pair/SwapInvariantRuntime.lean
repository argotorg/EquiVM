import Examples.UniswapV2Pair.SwapAdjustmentRuntime
import Examples.UniswapV2Pair.StackRoutines
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000

abbrev swapInvariantReserveWord (reserve0 reserve1 : UInt256) : UInt256 :=
  UInt256.mul (UInt256.mul reserve0 reserve1) ⟨1000000⟩

theorem swapInvariantReserveFits (reserve0 reserve1 : UInt256)
    (hc0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hc1 : UInt256.land reserve1 reserve112Mask = reserve1) :
    reserve0.toNat * reserve1.toNat < UInt256.size ∧
    (UInt256.mul reserve0 reserve1).toNat * 1000000 < UInt256.size := by
  have h0 : reserve0.toNat < 2 ^ 112 := by rw [← hc0]; exact reserve112Word_lt _
  have h1 : reserve1.toNat < 2 ^ 112 := by rw [← hc1]; exact reserve112Word_lt _
  have hp := Nat.mul_lt_mul_of_lt_of_lt h0 h1
  have hnum : (2 ^ 112 * 2 ^ 112) * 1000000 < UInt256.size := by native_decide
  have hprod : reserve0.toNat * reserve1.toNat < UInt256.size := by omega
  refine ⟨hprod, ?_⟩
  rw [u256_mul_toNat, Nat.mod_eq_of_lt hprod]
  exact lt_trans (Nat.mul_lt_mul_of_pos_right hp (by decide)) hnum

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSwapInvariantProductEntry
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw adjusted1 adjusted0 amount1In amount0In balance1 balance0 reserve1 reserve0 : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd2570 : RD uniswapV2PairBytecode I g s0 ⟨2570⟩
      (adjusted1 :: adjusted0 :: amount1In :: amount0In :: balance1 :: balance0 :: reserve1 :: reserve0 :: R)
      mem aw rdata acc k C)
    (hc0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hc1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hov : R.length + 23 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6780⟩
      (adjusted1 :: adjusted0 :: ⟨2632⟩ :: swapInvariantReserveWord reserve0 reserve1 ::
        adjusted1 :: adjusted0 :: amount1In :: amount0In :: balance1 :: balance0 :: reserve1 :: reserve0 :: R)
      mem aw rdata acc k' C' := by
  have rd2573 := evm_run rd2570 with [push2 ⟨2616⟩]
  have rd2577 := RD.pushConst rd2573 (⟨1000000⟩ : UInt256) (op := .PUSH3) (width := 3)
    (by decide) (by native_decide) (by simp only [List.length_cons]; omega)
  have rdMulPre := evm_run rd2577 with [push2 ⟨2604⟩,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup12, dup2, and, swap1, dup12, and,
    push4 ⟨4294967295⟩, push2 ⟨6780⟩, and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ = reserve112Mask by native_decide,
    u256_land_comm reserve112Mask, hc0, hc1,
    show UInt256.land (⟨6780⟩ : UInt256) ⟨4294967295⟩ = ⟨6780⟩ by native_decide] at rdMulPre
  have rdMul := evm_run rdMulPre with [jump (by jump_dest)]
  obtain ⟨hp, hs⟩ := swapInvariantReserveFits reserve0 reserve1 hc0 hc1
  obtain ⟨_, _, rd2604⟩ := RD.uniswapSafeMathMulSuccess rdMul hp (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rdScalePre := evm_run rd2604 with [jumpdest, swap1, push4 ⟨4294967295⟩, push2 ⟨6780⟩, and]
  rw [show UInt256.land (⟨6780⟩ : UInt256) ⟨4294967295⟩ = ⟨6780⟩ by native_decide] at rdScalePre
  have rdScale := evm_run rdScalePre with [jump (by jump_dest)]
  obtain ⟨_, _, rd2616⟩ := RD.uniswapSafeMathMulSuccess rdScale hs (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rdAdjPre := evm_run rd2616 with [jumpdest, push2 ⟨2632⟩, dup4, dup4,
    push4 ⟨4294967295⟩, push2 ⟨6780⟩, and]
  rw [show UInt256.land (⟨6780⟩ : UInt256) ⟨4294967295⟩ = ⟨6780⟩ by native_decide] at rdAdjPre
  exact ⟨_, _, evm_run rdAdjPre with [jump (by jump_dest)]⟩

abbrev swapInvariantValid (adjusted0 adjusted1 reserve0 reserve1 : UInt256) : Prop :=
  adjusted0.toNat * adjusted1.toNat < UInt256.size ∧
    (swapInvariantReserveWord reserve0 reserve1).toNat ≤ (UInt256.mul adjusted0 adjusted1).toNat

set_option maxHeartbeats 1000000 in
theorem uniswapSwapInvariantRuntimeCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw ptr adjusted1 adjusted0 amount1In amount0In balance1 balance0 reserve1 reserve0 : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd2570 : RD uniswapV2PairBytecode I g s0 ⟨2570⟩
      (adjusted1 :: adjusted0 :: amount1In :: amount0In :: balance1 :: balance0 :: reserve1 :: reserve0 :: R)
      mem aw rdata acc k C)
    (hc0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hc1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfitPtr : ptr.toNat + 131 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hawLo : 96 ≤ aw.toNat * 32) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hov : R.length + 23 ≤ 1024) :
    (¬ swapInvariantValid adjusted0 adjusted1 reserve0 reserve1) ∧ RDrev uniswapV2PairBytecode g s0 ∨
    swapInvariantValid adjusted0 adjusted1 reserve0 reserve1 ∧ ∃ k' C',
      RD uniswapV2PairBytecode I g s0 ⟨2701⟩
        (amount1In :: amount0In :: balance1 :: balance0 :: reserve1 :: reserve0 :: R)
        mem aw rdata acc k' C' := by
  obtain ⟨_, _, rdMul⟩ := RD.uniswapSwapInvariantProductEntry rd2570 hc0 hc1 hov
  by_cases hfit : adjusted0.toNat * adjusted1.toNat < UInt256.size
  · obtain ⟨_, _, rd2632⟩ := RD.uniswapSafeMathMulSuccess rdMul hfit (by jump_dest)
      (by simp only [List.length_cons]; omega)
    have rd2638 := evm_run rd2632 with [jumpdest, lt, iszero, push2 ⟨2698⟩]
    by_cases hle : (swapInvariantReserveWord reserve0 reserve1).toNat ≤ (UInt256.mul adjusted0 adjusted1).toNat
    · rw [ult_zero hle] at rd2638
      have rd2701 := evm_run rd2638 with [jumpiT (by decide) (by jump_dest), jumpdest, pop, pop]
      exact Or.inr ⟨⟨hfit, hle⟩, _, _, rd2701⟩
    · rw [ult_one (Nat.lt_of_not_ge hle)] at rd2638
      have rd2639 := evm_run rd2638 with [jumpiNT (by decide)]
      refine Or.inl ⟨fun h ↦ hle h.2, ?_⟩
      exact RD.solcErrorStringRevertTail_dynamic
        (len := ⟨12⟩) (rawWord := ⟨26439705653430490118936469579⟩) (shift := ⟨160⟩)
        (word := UInt256.shiftLeft ⟨26439705653430490118936469579⟩ ⟨160⟩)
        (op := .PUSH12) (width := 12) rd2639 (by
          dsimp only [solcErrorStringRevertTailWf]
          repeat' apply And.intro
          all_goals native_decide) (by decide) rfl
        hin hlo hgap hfitPtr haw hawLo hread (by simp only [List.length_cons]; omega)
  · exact Or.inl ⟨fun h ↦ hfit h.1, RD.uniswapSafeMathMulOverflow_dynamic rdMul
      (Nat.le_of_not_lt hfit) hin hlo hgap hfitPtr haw hawLo hread
      (by simp only [List.length_cons]; omega)⟩

end UniswapV2Pair
