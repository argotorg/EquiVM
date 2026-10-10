import Benchmarks.UniswapV3.Pool.LiquidityDeltaWords
import Benchmarks.UniswapV3.Pool.LiquidityDeltaSource
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_046
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_044

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem liquidityDeltaX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (xw yw : UInt256) (x y : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨13807⟩
      (yw :: xw :: ret :: R) mem aw rdata σ k C)
    (hx : normalizeInt (.uint ⟨128, by decide⟩) (Int.ofNat xw.toNat) = x)
    (hy : normalizeInt (.sint ⟨128, by decide⟩) (Int.ofNat yw.toNat) = y)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ liquidityDeltaValid x y) ∨
      (liquidityDeltaValid x y ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        ((xw + yw) :: R) mem aw rdata σ k' C') := by
  classical
  have hs := liquidityDeltaRawSign yw y hy
  have hg := liquidityDeltaRawGuard xw yw x y hx hy
  have hsub : UInt256.sub xw (UInt256.sub (UInt256.ofNat 0) yw) = xw + yw :=
    word_sub_neg xw yw
  by_cases hn : y < 0
  · have rn := uniswapV3Pool_block_13807_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hs, if_pos hn]; rfl) rd
    by_cases hv : liquidityDeltaValid x y
    · have hl : liquidityDeltaResult x y < x := by
        simpa only [liquidityDeltaValid, hn, if_true] using hv
      have rb := uniswapV3Pool_block_13821_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [solcMask128, hsub, hg, if_pos hl]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rn
      have rj := uniswapV3Pool_block_13903 (immWords := wordsOf (immStore v))
        (by change R.length + 4 + 1 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rb
      have rout := uniswapV3Pool_block_12989 (immWords := wordsOf (immStore v))
        (by evm_ov) hret rj
      simp only [uniswapV3Pool_block_12989_stack, hsub] at rout
      exact Or.inr ⟨hv, _, _, rout⟩
    · have hl : ¬ liquidityDeltaResult x y < x := by
        simpa only [liquidityDeltaValid, hn, if_true] using hv
      have rb := uniswapV3Pool_block_13821_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [solcMask128, hsub, hg, if_neg hl]; rfl) rn
      exact Or.inl ⟨uniswapV3Pool_block_13854 (immWords := wordsOf (immStore v))
        (by change R.length + 4 + 5 ≤ 1024; omega) rb, hv⟩
  · have rn := uniswapV3Pool_block_13807_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hs, if_neg hn]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    by_cases hv : liquidityDeltaValid x y
    · have hl : ¬ liquidityDeltaResult x y < x := by
        have hh : x ≤ liquidityDeltaResult x y := by
          simpa only [liquidityDeltaValid, hn, if_false] using hv
        omega
      have rb := uniswapV3Pool_block_13908_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [solcMask128, hg, if_neg hl]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rn
      have rout := uniswapV3Pool_block_12989 (immWords := wordsOf (immStore v))
        (by evm_ov) hret rb
      exact Or.inr ⟨hv, _, _, rout⟩
    · have hl : liquidityDeltaResult x y < x := by
        have hh : ¬ x ≤ liquidityDeltaResult x y := by
          simpa only [liquidityDeltaValid, hn, if_false] using hv
        omega
      have rb := uniswapV3Pool_block_13908_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [solcMask128, hg, if_pos hl]; rfl) rn
      exact Or.inl ⟨uniswapV3Pool_block_13940 (immWords := wordsOf (immStore v))
        (by change R.length + 4 + 5 ≤ 1024; omega) rb, hv⟩

theorem liquidityDeltaCanonicalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (x y : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨13807⟩
      (EVM.wordOfInt y :: EVM.wordOfInt x :: ret :: R) mem aw rdata σ k C)
    (hxlo : 0 ≤ x) (hxhi : x < 2 ^ 128)
    (hylo : -(2 ^ 127 : Int) ≤ y) (hyhi : y < 2 ^ 127)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ liquidityDeltaValid x y) ∨
      (liquidityDeltaValid x y ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (EVM.wordOfInt (liquidityDeltaResult x y) :: R) mem aw rdata σ k' C') := by
  have hx : normalizeInt (.uint ⟨128, by decide⟩) (Int.ofNat (EVM.wordOfInt x).toNat) = x := by
    rw [normalizeInt_wordOfInt, normalizeInt_uint_eq_self ⟨128, by decide⟩ _ hxlo hxhi]
  have hy : normalizeInt (.sint ⟨128, by decide⟩) (Int.ofNat (EVM.wordOfInt y).toNat) = y := by
    rw [normalizeInt_wordOfInt, normalizeSint_eq_self ⟨128, by decide⟩ _ hylo hyhi]
  rcases liquidityDeltaX (v := v) (EVM.wordOfInt x) (EVM.wordOfInt y) x y rd hx hy hret hov with
    hb | ⟨hv, k', C', rout⟩
  · exact Or.inl hb
  · refine Or.inr ⟨hv, k', C', ?_⟩
    rw [liquidityDeltaResult_of_valid x y hxlo hxhi hylo hyhi hv, wordOfInt_add]
    exact rout

end Benchmarks.UniswapV3.Pool
