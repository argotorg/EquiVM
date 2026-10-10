import Benchmarks.UniswapV3.Pool.SafeCast128Source
import Benchmarks.UniswapV3.Pool.SignedComparison
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_052
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_034

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: word encoding is injective throughout the signed EVM range.
theorem wordOfInt_eq_iff_signed (i j : Int)
    (hilo : -(2 ^ 255 : Int) ≤ i) (hihi : i < 2 ^ 255)
    (hjlo : -(2 ^ 255 : Int) ≤ j) (hjhi : j < 2 ^ 255) :
    EVM.wordOfInt i = EVM.wordOfInt j ↔ i = j := by
  constructor
  · intro he
    have hi := wordOfInt_signed_value i hilo hihi
    have hj := wordOfInt_signed_value j hjlo hjhi
    rw [he] at hi
    exact hi.trans hj.symm
  · rintro rfl
    rfl

theorem safeCast128WordValid (y : Int) (hlo : -(2 ^ 255 : Int) ≤ y) (hhi : y < 2 ^ 255) :
    EVM.wordOfInt y = UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt y) ↔
      safeCast128Valid y := by
  rw [signextend_wordOfInt ⟨128, by decide⟩ _ y (by decide) (by decide)]
  have hb := normalizeSint_bounds ⟨128, by decide⟩ y
  change -(2 ^ 127 : Int) ≤ normalizeInt (.sint ⟨128, by decide⟩) y ∧
    normalizeInt (.sint ⟨128, by decide⟩) y < 2 ^ 127 at hb
  rw [wordOfInt_eq_iff_signed _ _ hlo hhi (by omega) (by omega)]
  exact eq_comm

theorem safeCast128X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (y : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16216⟩
      (EVM.wordOfInt y :: ret :: R) mem aw rdata σ k C)
    (hlo : -(2 ^ 255 : Int) ≤ y) (hhi : y < 2 ^ 255)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ safeCast128Valid y) ∨
      (safeCast128Valid y ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (EVM.wordOfInt y :: R) mem aw rdata σ k' C') := by
  classical
  by_cases hy : safeCast128Valid y
  · have he := (safeCast128WordValid y hlo hhi).mpr hy
    have hc : UInt256.eq (EVM.wordOfInt y)
        (UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt y)) ≠ UInt256.ofNat 0 := by
      rw [← he, uInt256_eq_self]
      decide
    have rn := uniswapV3Pool_block_16216_taken (immWords := wordsOf (immStore v))
      (by evm_ov) hc (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    have rout := uniswapV3Pool_block_11243 (immWords := wordsOf (immStore v))
      (by evm_ov) hret rn
    exact Or.inr ⟨hy, _, _, rout⟩
  · have hc : UInt256.eq (EVM.wordOfInt y)
        (UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt y)) = UInt256.ofNat 0 := by
      apply uInt256_eq_zero_of_ne
      intro he
      exact hy ((safeCast128WordValid y hlo hhi).mp (uInt256_eq_one_eq he))
    have rb := uniswapV3Pool_block_16216_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) hc rd
    exact Or.inl ⟨uniswapV3Pool_block_16229 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 2 ≤ 1024; omega) rb, hy⟩

end Benchmarks.UniswapV3.Pool
