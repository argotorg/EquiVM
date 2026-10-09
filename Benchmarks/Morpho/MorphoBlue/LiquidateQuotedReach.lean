import Benchmarks.Morpho.MorphoBlue.LiquidateIncentiveReach
import Benchmarks.Morpho.MorphoBlue.LiquidateWDivReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidateAmountTail (id seized srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  [srcOff, len, UInt256.ofNat 0, id, seized, UInt256.ofNat 128] ++ R

def liquidateQuotedSum (seized price : UInt256) : UInt256 :=
  UInt256.mul seized price + UInt256.sub oraclePriceScale (UInt256.ofNat 1)

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
  {id seized shares price denom srcOff len : UInt256} {R : List UInt256}

theorem morphoLiquidateQuotedReachMul (hstack : R.length + 24 ≤ 1024) (hn : seized ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1743)
      (liquidateMathStack id seized shares price denom srcOff len R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395)
      ([seized, price, UInt256.ofNat 1759, denom] ++ liquidateAmountTail id seized srcOff len R)
      mem aw out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_1743_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 10 ≤ 1024; omega) (isZero_eq_zero_of_ne hn) h
  exact ⟨_, _, morphoBlocks.morpho_block_1749 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 10 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1⟩

theorem morphoLiquidateQuotedOk (hstack : R.length + 24 ≤ 1024) (hn : seized ≠ ⟨0⟩)
    (hf : MulDivUpFits seized price oraclePriceScale)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1743)
      (liquidateMathStack id seized shares price denom srcOff len R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1785)
      ([liquidateQuotedSum seized price, denom] ++ liquidateAmountTail id seized srcOff len R)
      mem aw out σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := morphoLiquidateQuotedReachMul (v := v) hstack hn h
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedMulOk (v := v) (by change R.length + 7 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hf.1 rd1
  have hc := checkedAddNoOverflowGt (UInt256.mul seized price) (UInt256.sub oraclePriceScale (UInt256.ofNat 1)) hf.2.2
  rw [u256_add_comm] at hc
  exact ⟨_, _, morphoBlocks.morpho_block_1759_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 7 + 3 ≤ 1024; omega) hc rd2⟩

theorem morphoLiquidateQuotedReverts (hstack : R.length + 24 ≤ 1024) (hn : seized ≠ ⟨0⟩)
    (hf : ¬ MulDivUpFits seized price oraclePriceScale)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1743)
      (liquidateMathStack id seized shares price denom srcOff len R) mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨k1, C1, rd1⟩ := morphoLiquidateQuotedReachMul (v := v) hstack hn h
  by_cases hp : seized.toNat * price.toNat < UInt256.size
  swap
  · exact morphoCheckedMulReverts (v := v) (by change R.length + 7 + 6 ≤ 1024; omega) (Nat.le_of_not_gt hp) rd1
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedMulOk (v := v) (by change R.length + 7 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hp rd1
  have ha : UInt256.size ≤ (UInt256.mul seized price).toNat + (UInt256.sub oraclePriceScale (UInt256.ofNat 1)).toNat :=
    Nat.le_of_not_gt (fun hh ↦ hf ⟨hp, by decide, hh⟩)
  have hc := checkedAddOverflowGt (UInt256.mul seized price) (UInt256.sub oraclePriceScale (UInt256.ofNat 1)) ha
  rw [u256_add_comm] at hc
  have rd3 := morphoBlocks.morpho_block_1759_taken (immWords := wordsOf (immStore v))
    (by change R.length + 7 + 3 ≤ 1024; omega) (by change UInt256.gt (UInt256.mul seized price) (liquidateQuotedSum seized price) ≠ _; rw [liquidateQuotedSum, hc]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact morphoBlocks.morpho_block_3277 (immWords := wordsOf (immStore v))
    (by change R.length + 8 + 2 ≤ 1024; omega) rd3

end Reach
end Benchmarks.Morpho.MorphoBlue
