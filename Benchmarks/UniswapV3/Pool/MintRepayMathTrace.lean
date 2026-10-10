import Benchmarks.UniswapV3.Pool.MintRepayControl

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem mintRepayCompareX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw required after : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (mintRepayComparePC second)
      (required :: after :: R) mem aw rdata σ k C) (hov : R.length + 5 ≤ 1024) :
    (¬ required.toNat ≤ after.toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    (required.toNat ≤ after.toNat ∧ ∃ k' C', RD (deployedRuntime v) ee g s0
      (mintRepayNextPC second) R mem aw rdata σ k' C') := by
  by_cases hp : required.toNat ≤ after.toNat
  · refine Or.inr ⟨hp, ?_⟩
    cases second with
    | false =>
      exact ⟨_, _, uniswapV3Pool_block_6147_taken (immWords := wordsOf (immStore v))
        (by omega) (by rw [ugt_zero hp]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩
    | true =>
      exact ⟨_, _, uniswapV3Pool_block_6227_taken (immWords := wordsOf (immStore v))
        (by omega) (by rw [ugt_zero hp]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩
  · refine Or.inl ⟨hp, ?_⟩
    cases second with
    | false =>
      have rr := uniswapV3Pool_block_6147_fallthrough (immWords := wordsOf (immStore v))
        (by omega) (by rw [ugt_one (Nat.lt_of_not_ge hp)]; decide) rd
      exact uniswapV3Pool_block_6154 (immWords := wordsOf (immStore v)) hov rr
    | true =>
      have rr := uniswapV3Pool_block_6227_fallthrough (immWords := wordsOf (immStore v))
        (by omega) (by rw [ugt_one (Nat.lt_of_not_ge hp)]; decide) rd
      exact uniswapV3Pool_block_6234 (immWords := wordsOf (immStore v)) hov rr

theorem mintRepayMathX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw before0 before1 amount0 amount1 after : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (mintRepayBalanceReturn second)
      (after :: mintRepayWords before0 before1 amount0 amount1 R) mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024) :
    (¬ flashRepayValid (if second then before1 else before0)
        (if second then amount1 else amount0) after ∧ RDrev (deployedRuntime v) g s0) ∨
    (flashRepayValid (if second then before1 else before0)
        (if second then amount1 else amount0) after ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 (mintRepayNextPC second)
        (mintRepayWords before0 before1 amount0 amount1 R) mem aw rdata σ k' C') := by
  obtain ⟨k1, C1, r1⟩ := mintRepayAddEntryX (v := v) second rd (by omega)
  rcases safeAddX (v := v) r1
      (by rw [uniswapV3PoolPatchedValidJumps v]; cases second <;> native_decide)
      (by change R.length + 7 + 6 ≤ 1024; omega) with ⟨hbad, rr⟩ | ⟨hgood, k2, C2, _, r2⟩
  · exact Or.inl ⟨fun h ↦ hbad h.1, rr⟩
  rcases mintRepayCompareX (v := v) second r2
      (by change R.length + 6 + 5 ≤ 1024; omega) with ⟨hbad, rr⟩ | ⟨hcmp, k3, C3, r3⟩
  · exact Or.inl ⟨fun h ↦ hbad h.2, rr⟩
  · exact Or.inr ⟨⟨hgood, hcmp⟩, k3, C3, r3⟩

end Benchmarks.UniswapV3.Pool
