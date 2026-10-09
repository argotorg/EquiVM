import Benchmarks.Morpho.MorphoBlue.LiquidateWDivReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
  {total price : UInt256} {R : List UInt256}

theorem morphoLiquidateScaleReachDiv (hstack : R.length + 12 ≤ 1024)
    (hf : (UInt256.div total wad).toNat * oraclePriceScale.toNat < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3448)
      (total :: wad :: price :: R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14414)
      ([UInt256.mul (UInt256.div total wad) oraclePriceScale, price, UInt256.ofNat 3521] ++ R)
      mem aw out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_3448_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 4 ≤ 1024; omega)
    (by rw [checkedMulGuard_alt]; exact checkedMulGuard_ok _ _ hf) h
  exact ⟨_, _, morphoBlocks.morpho_block_3495 (immWords := wordsOf (immStore v)) (by change R.length + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1⟩

theorem morphoLiquidateScaleOk (hstack : R.length + 12 ≤ 1024)
    (hf : (UInt256.div total wad).toNat * oraclePriceScale.toNat < UInt256.size) (hn : price ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3448)
      (total :: wad :: price :: R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3521)
      (UInt256.div (UInt256.mul (UInt256.div total wad) oraclePriceScale) price :: R)
      mem aw out σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := morphoLiquidateScaleReachDiv (v := v) hstack hf h
  exact morphoCheckedDivOk (v := v) (by change R.length + 6 ≤ 1024; omega) (by rw [morphoPatchedValidJumps v]; jump_dest) hn rd1

theorem morphoLiquidateScaleReverts (hstack : R.length + 12 ≤ 1024) (hlen : 3 ≤ R.length)
    (hf : UInt256.size ≤ (UInt256.div total wad).toNat * oraclePriceScale.toNat ∨ price = ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3448)
      (total :: wad :: price :: R) mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  by_cases hp : (UInt256.div total wad).toNat * oraclePriceScale.toNat < UInt256.size
  · obtain ⟨k1, C1, rd1⟩ := morphoLiquidateScaleReachDiv (v := v) hstack hp h
    exact morphoCheckedDivReverts (v := v) (by change R.length + 6 ≤ 1024; omega) (hf.resolve_left (Nat.not_le_of_gt hp)) rd1
  · have rd1 := morphoBlocks.morpho_block_3448_taken (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [checkedMulGuard_alt]; change checkedMulGuard (UInt256.div total wad) oraclePriceScale ≠ _
          rw [checkedMulGuard_overflow _ _ (Nat.le_of_not_gt hp)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    rcases R with _ | ⟨r0, R⟩
    · simp at hlen
    rcases R with _ | ⟨r1, R⟩
    · simp at hlen
    rcases R with _ | ⟨r2, R⟩
    · simp at hlen
    exact morphoBlocks.morpho_block_3527 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons] at hstack; omega) rd1

end Reach
end Benchmarks.Morpho.MorphoBlue
