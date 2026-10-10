import Benchmarks.UniswapV3.Pool.BitmapNextModel
import Benchmarks.UniswapV3.Pool.SignedQuotientBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem bitmapNextCompressed_eq (tick spacing : Int)
    (htlo : -(2 ^ 23 : Int) ≤ tick) (hthi : tick < 2 ^ 23) (hn : spacing ≠ 0) :
    bitmapNextCompressed tick spacing =
      if bitmapNextAdjust tick spacing then tick.tdiv spacing - 1 else tick.tdiv spacing := by
  by_cases h : bitmapNextAdjust tick spacing
  · simp only [bitmapNextCompressed, if_pos h]
    have hb := tdiv_sub_one_bounds_of_tmod_ne_zero (bound := 2 ^ 23) (by decide)
      (show tick.natAbs ≤ 2 ^ 23 by omega) hn h.2
    exact normalizeSint_eq_self ⟨24, by decide⟩ _ hb.1 hb.2
  · simp only [bitmapNextCompressed, if_neg h]

theorem bitmapNextCompressed_word (tick spacing : Int)
    (htlo : -(2 ^ 23 : Int) ≤ tick) (hthi : tick < 2 ^ 23) (hn : spacing ≠ 0) :
    EVM.wordOfInt (bitmapNextCompressed tick spacing) =
      if bitmapNextAdjust tick spacing then UInt256.lnot ⟨0⟩ + EVM.wordOfInt (tick.tdiv spacing)
      else EVM.wordOfInt (tick.tdiv spacing) := by
  rw [bitmapNextCompressed_eq tick spacing htlo hthi hn]
  split
  · rw [lnot_zero_add, wordOfInt_sub]
    rfl
  · rfl

end Benchmarks.UniswapV3.Pool
