import Benchmarks.UniswapV3.Pool.BitmapPositionSource
import Benchmarks.UniswapV3.Pool.SignedRightShift

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

-- GENERALIZES normalizeUInt_sint to any narrower unsigned result width.
theorem normalizeUInt_sint_of_le (small large : ABI.BitWidth) (i : Int)
    (hle : small.val ≤ large.val) :
    normalizeInt (.uint small) (normalizeInt (.sint large) i) =
      normalizeInt (.uint small) i := by
  have hr := normalizeInt_residue (.sint large) i
  change normalizeInt (.sint large) i % (2 ^ large.val : Int) = i % (2 ^ large.val : Int) at hr
  have hmod := congrArg (fun z : Int ↦ z % (2 ^ small.val : Int)) hr
  have hd : (2 ^ small.val : Int) ∣ 2 ^ large.val := pow_dvd_pow 2 hle
  simpa only [Int.emod_emod_of_dvd _ hd] using hmod

def bitmapPositionBitRaw (tick : Int) : UInt256 :=
  EVM.wordOfInt ((normalizeInt (.sint ⟨24, by decide⟩) tick).tmod 256)

theorem bitmapPositionBitClean (tick : Int) :
    UInt256.land (UInt256.ofNat 255) (bitmapPositionBitRaw tick) =
      EVM.wordOfInt (bitmapBitPos tick) := by
  have hm := normalizeUIntInt_mask ⟨8, by decide⟩
    ((normalizeInt (.sint ⟨24, by decide⟩) tick).tmod 256) (UInt256.ofNat 255) (by decide)
  rw [bitmapBitPos_tmod] at hm
  unfold bitmapBitPos at hm
  rw [normalizeUInt_sint_of_le ⟨8, by decide⟩ ⟨24, by decide⟩ tick (by decide)] at hm
  have hw := congrArg EVM.wordOfInt hm
  rw [wordOfInt_ofNat_toNat] at hw
  rw [u256_land_comm]
  exact hw.symm

theorem bitmapPositionWordShift (tick : Int) :
    UInt256.sar (UInt256.ofNat 8) (UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt tick)) =
      EVM.wordOfInt (bitmapWordPos tick) := by
  rw [signextend_wordOfInt ⟨24, by decide⟩ _ tick (by decide) (by decide)]
  have hb := normalizeSint_bounds ⟨24, by decide⟩ tick
  change -(2 ^ 23 : Int) ≤ normalizeInt (.sint ⟨24, by decide⟩) tick ∧
    normalizeInt (.sint ⟨24, by decide⟩) tick < 2 ^ 23 at hb
  have hc : normalizeInt (.sint ⟨256, by decide⟩)
      (normalizeInt (.sint ⟨24, by decide⟩) tick) = normalizeInt (.sint ⟨24, by decide⟩) tick :=
    normalizeSint_eq_self ⟨256, by decide⟩ _ (by change -(2 ^ 255 : Int) ≤ _; omega)
      (by change _ < (2 ^ 255 : Int); omega)
  rw [← wordOfInt_signedWordInt
    (UInt256.sar (UInt256.ofNat 8) (EVM.wordOfInt (normalizeInt (.sint ⟨24, by decide⟩) tick))),
    signedWordInt_sar _ 8 (by decide), signedWordInt_wordOfInt, hc]
  rfl

theorem bitmapPositionBitRemainder (tick : Int) :
    UInt256.smod (UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt tick))
      (UInt256.ofNat 256) = bitmapPositionBitRaw tick := by
  rw [signextend_wordOfInt ⟨24, by decide⟩ _ tick (by decide) (by decide)]
  have hb := normalizeSint_bounds ⟨24, by decide⟩ tick
  change -(2 ^ 23 : Int) ≤ normalizeInt (.sint ⟨24, by decide⟩) tick ∧
    normalizeInt (.sint ⟨24, by decide⟩) tick < 2 ^ 23 at hb
  exact wordOfInt_smod _ 256 (by omega) (by omega) (by decide) (by decide) (by decide)

end Benchmarks.UniswapV3.Pool
