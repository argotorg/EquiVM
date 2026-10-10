import Benchmarks.UniswapV4PoolManager.SignedRemainderWords
import Benchmarks.UniswapV4PoolManager.SignedRangeSource
import Benchmarks.UniswapV4PoolManager.WordSar

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickBitmapCompressed (tick spacing : Int) : Int := tick.tdiv spacing
def tickBitmapPosition (tick spacing : Int) : Int := tickBitmapCompressed tick spacing / 256
def tickBitmapMask (compressed : Int) : UInt256 :=
  UInt256.shiftLeft ⟨1⟩ (UInt256.land (EVM.wordOfInt compressed) ⟨255⟩)
def tickBitmapAligned (tick spacing : Int) : Prop := spacing = 0 ∨ tick.tmod spacing = 0
instance (tick spacing : Int) : Decidable (tickBitmapAligned tick spacing) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem tickBitmapCompressed_bounds {tick : Int} (spacing : Int) (ht : tick.natAbs ≤ 887272) :
    -887272 ≤ tickBitmapCompressed tick spacing ∧ tickBitmapCompressed tick spacing ≤ 887272 := by
  have hb := (Int.natAbs_tdiv_le_natAbs tick spacing).trans ht
  have hhi := Int.le_natAbs (a := tick.tdiv spacing)
  have hlo := Int.le_natAbs (a := -(tick.tdiv spacing))
  rw [Int.natAbs_neg] at hlo
  dsimp only [tickBitmapCompressed]
  omega

theorem tickBitmapCompressed_int256 {tick : Int} (spacing : Int) (ht : tick.natAbs ≤ 887272) :
    int256Fits (tickBitmapCompressed tick spacing) := by
  have hb := tickBitmapCompressed_bounds spacing ht
  change -(2^255 : Int) ≤ tickBitmapCompressed tick spacing ∧ tickBitmapCompressed tick spacing < (2^255 : Int)
  omega

theorem tickBitmapPosition_fits {tick : Int} (spacing : Int) (ht : tick.natAbs ≤ 887272) :
    signedFits ⟨16, by decide⟩ (tickBitmapPosition tick spacing) := by
  have hb := tickBitmapCompressed_bounds spacing ht
  change -(2^15 : Int) ≤ tickBitmapCompressed tick spacing / 256 ∧
    tickBitmapCompressed tick spacing / 256 < (2^15 : Int)
  omega

theorem tickBitmapPosition_word (tick spacing : UInt256) (ht : (EVM.signed tick).natAbs ≤ 887272) :
    EVM.wordOfInt (tickBitmapPosition (EVM.signed tick) (EVM.signed spacing)) =
      UInt256.sar (UInt256.ofNat 8) (UInt256.sdiv tick spacing) := by
  have hc := tickBitmapCompressed_int256 (EVM.signed spacing) ht
  dsimp only [tickBitmapCompressed] at hc
  have he : EVM.signed (UInt256.sar (UInt256.ofNat 8) (UInt256.sdiv tick spacing)) =
      tickBitmapPosition (EVM.signed tick) (EVM.signed spacing) := by
    rw [wordSarSigned _ (by decide), sdiv_signed, signed_wordOfInt hc]
    rfl
  rw [← he, wordOfInt_signed]

theorem tickBitmapAligned_word (tick spacing : UInt256) (ht : (EVM.signed tick).natAbs ≤ 887272) :
    UInt256.smod tick spacing = ⟨0⟩ ↔ tickBitmapAligned (EVM.signed tick) (EVM.signed spacing) := by
  rw [smod_signed, tickBitmapAligned]
  by_cases hz : spacing = ⟨0⟩
  · simp only [hz, if_true, show EVM.signed (⟨0⟩ : UInt256) = 0 from rfl, true_or]
  · have hs : EVM.signed spacing ≠ 0 := fun h => hz ((signed_eq_zero_iff spacing).mp h)
    rw [if_neg hz, or_iff_right hs]
    exact wordOfInt_eq_zero_iff (tmod_int256_of_abs_lt (EVM.signed spacing) (by omega))

theorem tickBitmapPosition_eval {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr}
    {tick spacing : Int} (ht : tick.natAbs ≤ 887272)
    (he : evalExpr? cfg f evm e = .ok (.int (tickBitmapCompressed tick spacing))) :
    evalExpr? cfg f evm (.cast (.binary (.shr (.sint ⟨256, by decide⟩)) e (.intLit 8))
      (.elem (.int (.sint ⟨16, by decide⟩)))) = .ok (.int (tickBitmapPosition tick spacing)) := by
  have hc := tickBitmapCompressed_int256 spacing ht
  have hs := evalSignedWordSar (x := EVM.wordOfInt (tickBitmapCompressed tick spacing)) (n := 8) (by decide)
    (by rw [signed_wordOfInt hc]; exact he)
    (show evalExpr? cfg f evm (.intLit 8) = .ok (.int (Int.ofNat 8)) by simp only [evalExpr?, pure]; rfl)
  rw [wordSarSigned _ (by decide), signed_wordOfInt hc] at hs
  have hp := evalExpr_cast_int (intType := .sint ⟨16, by decide⟩) hs
  have hnorm := normalizeSigned_of_fits (tickBitmapPosition_fits spacing ht)
  dsimp only [tickBitmapPosition] at hnorm
  simpa only [show Int.ofNat (2^8) = (256 : Int) from rfl, hnorm] using hp

theorem tickBitmapMask_eval {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {compressed : Int}
    (hc : int256Fits compressed) (he : evalExpr? cfg f evm e = .ok (.int compressed)) :
    evalExpr? cfg f evm (.binary (.shl (.uint ⟨256, by decide⟩)) (.intLit 1)
      (.cast e (.elem (.int (.uint ⟨8, by decide⟩))))) =
      .ok (.int (Int.ofNat (tickBitmapMask compressed).toNat)) := by
  have hnorm := normalizeUintSignedWord ⟨8, by decide⟩ (EVM.wordOfInt compressed) ⟨255⟩ rfl
  rw [signed_wordOfInt hc] at hnorm
  have hcast := evalExpr_cast_int (intType := .uint ⟨8, by decide⟩) he
  rw [hnorm] at hcast
  have hn : (UInt256.land (EVM.wordOfInt compressed) ⟨255⟩).toNat < 256 := by
    rw [uland_toNat]
    change Nat.land (EVM.wordOfInt compressed).toNat (2^8-1) < 256
    rw [nat_land_mask_eq_mod]
    exact Nat.mod_lt _ (by decide)
  have hshift := evalWordShl (x := (⟨1⟩ : UInt256)) hn
    (show evalExpr? cfg f evm (.intLit 1) = .ok (.int (Int.ofNat (⟨1⟩ : UInt256).toNat)) by simp only [evalExpr?, pure]; rfl) hcast
  simpa only [u256_ofNat_toNat] using hshift

end Benchmarks.UniswapV4PoolManager
