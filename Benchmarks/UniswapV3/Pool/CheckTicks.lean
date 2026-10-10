import Benchmarks.UniswapV3.Pool.CheckTicksSource
import Benchmarks.UniswapV3.Pool.SignedComparison
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_056

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem checkTicksX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret lower upper : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨17313⟩ (upper :: lower :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 8 ≤ 1024) :
    let lo := normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat lower.toNat)
    let hi := normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat upper.toNat)
    (RDrev (deployedRuntime v) g s0 ∧ ¬ validTicks lo hi) ∨
      (validTicks lo hi ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret R mem aw rdata σ k' C') := by
  dsimp only
  let lo := normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat lower.toNat)
  let hi := normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat upper.toNat)
  have hlb : -(2 ^ 23 : Int) ≤ lo ∧ lo < 2 ^ 23 := normalizeSint_bounds _ _
  have hub : -(2 ^ 23 : Int) ≤ hi ∧ hi < 2 ^ 23 := normalizeSint_bounds _ _
  have hl : UInt256.signextend (UInt256.ofNat 2) lower = EVM.wordOfInt lo :=
    signextend_normalizeSint ⟨24, by decide⟩ _ _ (by decide) (by decide)
  have hu : UInt256.signextend (UInt256.ofNat 2) upper = EVM.wordOfInt hi :=
    signextend_normalizeSint ⟨24, by decide⟩ _ _ (by decide) (by decide)
  have hord : UInt256.slt (UInt256.signextend (UInt256.ofNat 2) lower)
      (UInt256.signextend (UInt256.ofNat 2) upper) = if lo < hi then ⟨1⟩ else ⟨0⟩ := by
    rw [hl, hu]
    exact slt_wordOfInt lo hi (by omega) (by omega) (by omega) (by omega)
  have hmin : UInt256.slt (UInt256.signextend (UInt256.ofNat 2) lower)
      (UInt256.lnot (UInt256.ofNat 887271)) = if lo < -887272 then ⟨1⟩ else ⟨0⟩ := by
    rw [hl, show UInt256.lnot (UInt256.ofNat 887271) = EVM.wordOfInt (-887272) by decide +kernel]
    exact slt_wordOfInt lo (-887272) (by omega) (by omega) (by decide) (by decide)
  have hmax : UInt256.sgt (UInt256.signextend (UInt256.ofNat 2) upper)
      (UInt256.ofNat 887272) = if 887272 < hi then ⟨1⟩ else ⟨0⟩ := by
    rw [sgt_eq_slt_swap, hu,
      show UInt256.ofNat 887272 = EVM.wordOfInt 887272 by decide +kernel]
    exact slt_wordOfInt 887272 hi (by decide) (by decide) (by omega) (by omega)
  by_cases ho : lo < hi
  · have rdLower := uniswapV3Pool_block_17313_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hord, if_pos ho]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    by_cases hlow : -887272 ≤ lo
    · have rdUpper := uniswapV3Pool_block_17377_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hmin, if_neg (by omega)]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdLower
      by_cases hhigh : hi ≤ 887272
      · have rdReturn := uniswapV3Pool_block_17444_taken (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [hmax, if_neg (by omega)]; decide)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdUpper
        exact Or.inr ⟨⟨ho, hlow, hhigh⟩, _, _,
          uniswapV3Pool_block_17510 (immWords := wordsOf (immStore v)) (by evm_ov) hret rdReturn⟩
      · have rdFail := uniswapV3Pool_block_17444_fallthrough (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [hmax, if_pos (by omega)]; decide) rdUpper
        exact Or.inl ⟨uniswapV3Pool_block_17460 (immWords := wordsOf (immStore v)) (by evm_ov) rdFail,
          fun h => hhigh h.2.2⟩
    · have rdFail := uniswapV3Pool_block_17377_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hmin, if_pos (by omega)]; decide) rdLower
      exact Or.inl ⟨uniswapV3Pool_block_17394 (immWords := wordsOf (immStore v)) (by evm_ov) rdFail,
        fun h => hlow h.2.1⟩
  · have rdFail := uniswapV3Pool_block_17313_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hord, if_neg ho]; rfl) rd
    exact Or.inl ⟨uniswapV3Pool_block_17327 (immWords := wordsOf (immStore v)) (by evm_ov) rdFail,
      fun h => ho h.1⟩

end Benchmarks.UniswapV3.Pool
