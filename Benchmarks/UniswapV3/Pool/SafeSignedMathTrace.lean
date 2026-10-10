import Benchmarks.UniswapV3.Pool.SafeSignedMathWords
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_043
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_044

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem safeSignedMathX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (subtract : Bool) (x y : Int)
    (rd : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (if subtract then 12967 else 12995))
      (EVM.wordOfInt y :: EVM.wordOfInt x :: ret :: R) mem aw rdata σ k C)
    (hxlo : -(2 ^ 255 : Int) ≤ x) (hxhi : x < 2 ^ 255)
    (hylo : -(2 ^ 255 : Int) ≤ y) (hyhi : y < 2 ^ 255)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ safeSignedMathValid subtract x y) ∨
      (safeSignedMathValid subtract x y ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (EVM.wordOfInt (safeSignedMathResult subtract x y) :: R) mem aw rdata σ k' C') := by
  classical
  have hc := safeSignedMathWordGuard subtract x y hxlo hxhi hylo hyhi
  have hw := safeSignedMathResult_word subtract x y
  cases subtract
  · simp only [Bool.false_eq_true, ↓reduceIte] at hc hw rd
    rw [hw] at hc
    by_cases hv : safeSignedMathValid false x y
    · have rb := uniswapV3Pool_block_12995_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hc, if_pos hv]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
      have rout := uniswapV3Pool_block_12989 (immWords := wordsOf (immStore v))
        (by evm_ov) hret rb
      simp only [uniswapV3Pool_block_12989_stack] at rout
      rw [← hw] at rout
      exact Or.inr ⟨hv, _, _, rout⟩
    · have rb := uniswapV3Pool_block_12995_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hc, if_neg hv]; rfl) rd
      exact Or.inl ⟨uniswapV3Pool_block_13013 (immWords := wordsOf (immStore v))
        (by change R.length + 4 + 2 ≤ 1024; omega) rb, hv⟩
  · simp only [↓reduceIte] at hc hw rd
    rw [hw] at hc
    by_cases hv : safeSignedMathValid true x y
    · have rb := uniswapV3Pool_block_12967_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hc, if_pos hv]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
      have rout := uniswapV3Pool_block_12989 (immWords := wordsOf (immStore v))
        (by evm_ov) hret rb
      simp only [uniswapV3Pool_block_12989_stack] at rout
      rw [← hw] at rout
      exact Or.inr ⟨hv, _, _, rout⟩
    · have rb := uniswapV3Pool_block_12967_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hc, if_neg hv]; rfl) rd
      exact Or.inl ⟨uniswapV3Pool_block_12985 (immWords := wordsOf (immStore v))
        (by change R.length + 4 + 2 ≤ 1024; omega) rb, hv⟩

end Benchmarks.UniswapV3.Pool
