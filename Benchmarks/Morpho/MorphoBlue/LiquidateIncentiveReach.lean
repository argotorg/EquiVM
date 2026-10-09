import Benchmarks.Morpho.MorphoBlue.LiquidateIncentiveMath
import Benchmarks.Morpho.MorphoBlue.LiquidateGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidateMathStack (id seized shares price denom srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  [shares, price, denom, srcOff, len, UInt256.ofNat 0, id, seized, UInt256.ofNat 128] ++ R

theorem morphoLiquidateIncentiveReach {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw seized shares price srcOff len : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (hstack : R.length + 20 ≤ 1024)
    (hlltv : memLoad (UInt256.ofNat 256) mem = p.lltv)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1638)
      (price :: liquidateGuardTail p.id seized shares srcOff len R) mem aw out σ k C) :
    if p.lltv.toNat ≤ wad.toNat then ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1743)
        (liquidateMathStack p.id seized shares price (liquidationDenom p.lltv) srcOff len R)
        mem aw' out σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hm : memLoad (UInt256.ofNat 128 + UInt256.ofNat 128) mem = p.lltv := hlltv
  by_cases hf : p.lltv.toNat ≤ wad.toNat
  swap
  · rw [if_neg hf]
    have rd0 := morphoBlocks.morpho_block_1638_taken (immWords := wordsOf (immStore v))
      (by change R.length + 11 ≤ 1024; omega)
      (by rw [hm]; change UInt256.gt (UInt256.sub wad p.lltv) wad ≠ UInt256.ofNat 0
          rw [checkedSubGuard_underflow wad p.lltv (Nat.lt_of_not_ge hf)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact morphoBlocks.morpho_block_3232 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 10 ≤ 1024; omega) rd0
  rw [if_pos hf]
  obtain ⟨a0, k0, C0, rd0⟩ := morphoBlocks.morpho_block_1638_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 11 ≤ 1024; omega) (by rw [hm]; exact checkedSubGuard_ok wad p.lltv hf) h
  dsimp only [morphoBlocks.morpho_block_1638_fallthrough_stack] at rd0
  rw [hm] at rd0
  have hfit := liquidationDiscount_mul_fits hf
  have hprod : UInt256.div (UInt256.mul liquidationCursor (UInt256.sub wad p.lltv)) liquidationCursor =
      UInt256.sub wad p.lltv := by
    rw [u256_mul_comm]
    exact u256_mul_div_right_eq_of_noOverflow _ _ (by decide) (by simpa only [Nat.mul_comm] using hfit)
  have rd1 := morphoBlocks.morpho_block_1669_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 8 + 4 ≤ 1024; omega)
    (by change UInt256.sub (UInt256.div (UInt256.mul liquidationCursor (UInt256.sub wad p.lltv)) liquidationCursor) (UInt256.sub wad p.lltv) = _
        rw [hprod, u256_sub_self]; rfl) rd0
  have hb := liquidationDiscount_bound hf
  have hle : (liquidationDiscount p.lltv).toNat ≤ wad.toNat := by change _ ≤ 1000000000000000000; omega
  have rd2 := morphoBlocks.morpho_block_1690_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 6 + 6 ≤ 1024; omega) (checkedSubGuard_ok wad (liquidationDiscount p.lltv) hle) rd1
  have hne : wad ≠ liquidationDiscount p.lltv := by
    intro he
    rw [← he] at hb
    change 1000000000000000000 ≤ 300000000000000000 at hb
    omega
  have rd3 := morphoBlocks.morpho_block_1729_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 9 + 2 ≤ 1024; omega)
    (by change UInt256.eq wad (liquidationDiscount p.lltv) = UInt256.ofNat 0
        simp only [UInt256.eq, decide_eq_false hne]; rfl) rd2
  exact ⟨a0, _, _, rd3⟩

end Benchmarks.Morpho.MorphoBlue
