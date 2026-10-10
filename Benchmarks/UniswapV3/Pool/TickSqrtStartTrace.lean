import Benchmarks.UniswapV3.Pool.TickSqrtPrefix
import Benchmarks.UniswapV3.Pool.SignedComparison
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_036

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def tickSqrtTick (tick : UInt256) : Int := normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat tick.toNat)

theorem tickSqrtStartX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw tick : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨11629⟩ (tick :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ (tickSqrtTick tick).natAbs ≤ 887272) ∨
      ((tickSqrtTick tick).natAbs ≤ 887272 ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11722⟩
        (UInt256.ofNat (tickSqrtTick tick).natAbs :: ⟨0⟩ :: tick :: R) mem aw rdata σ k' C') := by
  let t := tickSqrtTick tick
  have ht : -(2 ^ 23 : Int) ≤ t ∧ t < 2 ^ 23 := normalizeSint_bounds _ _
  have ha : (UInt256.ofNat t.natAbs).toNat = t.natAbs :=
    UInt256.toNat_ofNat_of_lt (lt_trans (tickSqrtAbs_lt t ht.1 ht.2) (by decide))
  have hsign : UInt256.signextend (UInt256.ofNat 2) tick = EVM.wordOfInt t :=
    signextend_normalizeSint ⟨24, by decide⟩ _ _ (by decide) (by decide)
  have hlt : UInt256.slt (UInt256.signextend (UInt256.ofNat 2) tick) (UInt256.ofNat 0) =
      if t < 0 then ⟨1⟩ else ⟨0⟩ := by
    rw [hsign, show UInt256.ofNat 0 = EVM.wordOfInt 0 from rfl]
    exact slt_wordOfInt t 0 (by omega) (by omega) (by decide) (by decide)
  have habs : ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11660⟩
      (UInt256.ofNat t.natAbs :: ⟨0⟩ :: ⟨0⟩ :: tick :: R) mem aw rdata σ k' C' := by
    by_cases hn : t < 0
    · have r1 := uniswapV3Pool_block_11629_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hlt, if_pos hn]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      have r2 := uniswapV3Pool_block_11652 (immWords := wordsOf (immStore v)) (by evm_ov) r1
      have hw : UInt256.sub (UInt256.ofNat 0) (UInt256.signextend (UInt256.ofNat 2) tick) =
          UInt256.ofNat t.natAbs := by
        rw [hsign, show UInt256.ofNat 0 = EVM.wordOfInt 0 from rfl, ← wordOfInt_sub]
        have heq : 0 - t = Int.ofNat t.natAbs := by
          rw [Int.ofNat_eq_natCast, Int.natCast_natAbs, abs_of_neg hn, zero_sub]
        rw [heq, wordOfInt_ofNat_eq]
      exact ⟨_, _, by simpa only [uniswapV3Pool_block_11652_stack, hw] using r2⟩
    · have r1 := uniswapV3Pool_block_11629_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hlt, if_neg hn]; rfl) rd
      have r2 := uniswapV3Pool_block_11644 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      have hw : UInt256.signextend (UInt256.ofNat 2) tick = UInt256.ofNat t.natAbs := by
        calc
          _ = EVM.wordOfInt t := hsign
          _ = EVM.wordOfInt (Int.ofNat t.natAbs) :=
            congrArg EVM.wordOfInt (Int.natAbs_of_nonneg (by omega : 0 ≤ t)).symm
          _ = _ := wordOfInt_ofNat_eq _
      exact ⟨_, _, by simpa only [uniswapV3Pool_block_11644_stack, hw] using r2⟩
  obtain ⟨k', C', rabs⟩ := habs
  by_cases hv : t.natAbs ≤ 887272
  · have hgt : UInt256.gt (UInt256.ofNat t.natAbs) (UInt256.ofNat 887272) = ⟨0⟩ :=
      ugt_zero (by rw [ha]; exact hv)
    have rout := uniswapV3Pool_block_11660_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hgt]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rabs
    exact Or.inr ⟨hv, _, _, rout⟩
  · have hgt : UInt256.gt (UInt256.ofNat t.natAbs) (UInt256.ofNat 887272) = ⟨1⟩ :=
      ugt_one (by rw [ha]; exact Nat.lt_of_not_ge hv)
    have rfail := uniswapV3Pool_block_11660_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hgt]; rfl) rabs
    exact Or.inl ⟨uniswapV3Pool_block_11674 (immWords := wordsOf (immStore v))
      (by simp only [uniswapV3Pool_block_11660_fallthrough_stack, List.length_cons]; omega) rfail, hv⟩

end Benchmarks.UniswapV3.Pool
