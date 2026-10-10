import Benchmarks.UniswapV3.Pool.LowGasSafeAdd
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_024

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def flashRepayValid (before fee after : UInt256) : Prop :=
  before.toNat ≤ (before + fee).toNat ∧ (before + fee).toNat ≤ after.toNat

theorem flashRepaymentX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw junk before0 before1 fee0 fee1 after0 after1 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨7003⟩
      (after1 :: junk :: after0 :: before1 :: before0 :: fee1 :: fee0 :: R) mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ¬ (flashRepayValid before0 fee0 after0 ∧ flashRepayValid before1 fee1 after1)) ∨
    (flashRepayValid before0 fee0 after0 ∧ flashRepayValid before1 fee1 after1 ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨7139⟩
        (after1 :: after0 :: before1 :: before0 :: fee1 :: fee0 :: R) mem aw rdata σ k' C') := by
  have rdAdd0 := uniswapV3Pool_block_7003 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_7003_stack] at rdAdd0
  rcases safeAddX (v := v) rdAdd0 (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by evm_ov) with ⟨hb0, rdBad⟩ | ⟨ha0, k0, C0, _, rd0⟩
  · exact Or.inl ⟨rdBad, fun h ↦ hb0 h.1.1⟩
  · by_cases hp0 : (before0 + fee0).toNat ≤ after0.toNat
    · have rdNext := uniswapV3Pool_block_7016_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [ugt_zero hp0]; decide +kernel)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd0
      have rdAdd1 := uniswapV3Pool_block_7072 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdNext
      simp only [uniswapV3Pool_block_7072_stack] at rdAdd1
      rcases safeAddX (v := v) rdAdd1 (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
          (by evm_ov) with ⟨hb1, rdBad⟩ | ⟨ha1, k1, C1, _, rd1⟩
      · exact Or.inl ⟨rdBad, fun h ↦ hb1 h.2.1⟩
      · by_cases hp1 : (before1 + fee1).toNat ≤ after1.toNat
        · have rdGood := uniswapV3Pool_block_7083_taken (immWords := wordsOf (immStore v))
            (by evm_ov) (by rw [ugt_zero hp1]; decide +kernel)
            (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd1
          exact Or.inr ⟨⟨ha0, hp0⟩, ⟨ha1, hp1⟩, _, _, rdGood⟩
        · have rdFail := uniswapV3Pool_block_7083_fallthrough (immWords := wordsOf (immStore v))
            (by evm_ov) (by rw [ugt_one (Nat.lt_of_not_ge hp1)]; decide +kernel) rd1
          exact Or.inl ⟨uniswapV3Pool_block_7090 (immWords := wordsOf (immStore v))
            (by simpa only [uniswapV3Pool_block_7083_fallthrough_stack, List.length_cons] using
              (show R.length + 11 ≤ 1024 by omega)) rdFail, fun h ↦ hp1 h.2.2⟩
    · have rdFail := uniswapV3Pool_block_7016_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [ugt_one (Nat.lt_of_not_ge hp0)]; decide +kernel) rd0
      exact Or.inl ⟨uniswapV3Pool_block_7023 (immWords := wordsOf (immStore v))
        (by simpa only [uniswapV3Pool_block_7016_fallthrough_stack, List.length_cons] using
          (show R.length + 11 ≤ 1024 by omega)) rdFail, fun h ↦ hp0 h.1.2⟩

end Benchmarks.UniswapV3.Pool
