import Benchmarks.UniswapV3.Pool.TickSpacingModel
import Benchmarks.UniswapV3.Pool.SignedDivisionGeneral
import Benchmarks.UniswapV3.Pool.ModularMultiplication

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def spacingMinRaw (word : UInt256) : UInt256 :=
  UInt256.mul (UInt256.sdiv (UInt256.lnot (UInt256.ofNat 887271))
    (UInt256.signextend (UInt256.ofNat 2) word)) word

def spacingMaxRaw (word : UInt256) : UInt256 :=
  UInt256.mul (UInt256.sdiv (UInt256.ofNat 887272)
    (UInt256.signextend (UInt256.ofNat 2) word)) word

def spacingDeltaRaw (word : UInt256) : UInt256 :=
  UInt256.signextend (UInt256.ofNat 2) (UInt256.sub (spacingMaxRaw word) (spacingMinRaw word))

def spacingCountRaw (word : UInt256) : UInt256 :=
  UInt256.land (UInt256.ofNat 16777215)
    (UInt256.ofNat 1 + UInt256.sdiv (spacingDeltaRaw word) (UInt256.signextend (UInt256.ofNat 2) word))

def spacingLiquidityRaw (word : UInt256) : UInt256 :=
  UInt256.div (UInt256.ofNat (2 ^ 128 - 1)) (spacingCountRaw word)

theorem spacingWord_clean (word : UInt256) (spacing : Int)
    (hclean : normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat word.toNat) = spacing) :
    UInt256.signextend (UInt256.ofNat 2) word = EVM.wordOfInt spacing := by
  rw [signextend_normalizeSint ⟨24, by decide⟩ _ word (by decide) (by decide), hclean]

theorem spacingMinRaw_normalize (word : UInt256) (spacing : Int)
    (hclean : normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat word.toNat) = spacing)
    (hlo : -(2 ^ 23 : Int) ≤ spacing) (hhi : spacing < 2 ^ 23) :
    normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat (spacingMinRaw word).toNat) = spacingMin spacing := by
  have hm : spacingMinRaw word = EVM.wordOfInt ((-887272 : Int).tdiv spacing * Int.ofNat word.toNat) := by
    unfold spacingMinRaw
    rw [spacingWord_clean word spacing hclean,
      show UInt256.lnot (UInt256.ofNat 887271) = EVM.wordOfInt (-887272) by decide,
      wordOfInt_sdiv (-887272) spacing (by decide) (by decide) (by omega) (by omega),
      wordOfInt_mul, wordOfInt_ofNat_toNat]
  rw [hm, normalizeInt_wordOfInt, ← normalizeInt_mul_right, hclean]
  rfl

theorem spacingMaxRaw_normalize (word : UInt256) (spacing : Int)
    (hclean : normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat word.toNat) = spacing)
    (hlo : -(2 ^ 23 : Int) ≤ spacing) (hhi : spacing < 2 ^ 23) :
    normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat (spacingMaxRaw word).toNat) = spacingMax spacing := by
  have hm : spacingMaxRaw word = EVM.wordOfInt ((887272 : Int).tdiv spacing * Int.ofNat word.toNat) := by
    unfold spacingMaxRaw
    rw [spacingWord_clean word spacing hclean,
      show UInt256.ofNat 887272 = EVM.wordOfInt 887272 from rfl,
      wordOfInt_sdiv 887272 spacing (by decide) (by decide) (by omega) (by omega),
      wordOfInt_mul, wordOfInt_ofNat_toNat]
  rw [hm, normalizeInt_wordOfInt, ← normalizeInt_mul_right, hclean]
  rfl

theorem spacingDeltaRaw_eq (word : UInt256) (spacing : Int)
    (hclean : normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat word.toNat) = spacing)
    (hlo : -(2 ^ 23 : Int) ≤ spacing) (hhi : spacing < 2 ^ 23) :
    spacingDeltaRaw word = EVM.wordOfInt (spacingDelta spacing) := by
  have hsub : UInt256.sub (spacingMaxRaw word) (spacingMinRaw word) =
      EVM.wordOfInt (Int.ofNat (spacingMaxRaw word).toNat - Int.ofNat (spacingMinRaw word).toNat) := by
    rw [wordOfInt_sub, wordOfInt_ofNat_toNat, wordOfInt_ofNat_toNat]
  unfold spacingDeltaRaw
  rw [hsub, signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
    ← normalizeInt_sub_both, spacingMaxRaw_normalize word spacing hclean hlo hhi,
    spacingMinRaw_normalize word spacing hclean hlo hhi]
  rfl

theorem spacingCountRaw_eq (word : UInt256) (spacing : Int)
    (hclean : normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat word.toNat) = spacing)
    (hlo : -(2 ^ 23 : Int) ≤ spacing) (hhi : spacing < 2 ^ 23) :
    spacingCountRaw word = EVM.wordOfInt (spacingCount spacing) := by
  have hd := normalizeSint_bounds ⟨24, by decide⟩ (spacingMax spacing - spacingMin spacing)
  change -(2 ^ 23 : Int) ≤ spacingDelta spacing ∧ spacingDelta spacing < 2 ^ 23 at hd
  unfold spacingCountRaw spacingCount
  rw [spacingWord_clean word spacing hclean, spacingDeltaRaw_eq word spacing hclean hlo hhi,
    wordOfInt_sdiv _ spacing (by omega) (by omega) (by omega) (by omega)]
  rw [Int.add_comm (normalizeInt _ _) 1, normalizeInt_add_right,
    wordOfInt_normalizeUint ⟨24, by decide⟩ _ (UInt256.ofNat 16777215) (by decide),
    wordOfInt_add]
  rw [u256_land_comm]
  rfl

theorem spacingLiquidityRaw_eq (word : UInt256) (spacing : Int)
    (hclean : normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat word.toNat) = spacing)
    (hlo : -(2 ^ 23 : Int) ≤ spacing) (hhi : spacing < 2 ^ 23) :
    spacingLiquidityRaw word = EVM.wordOfInt (spacingLiquidity spacing) := by
  have hc := spacingCount_bounds spacing
  have hcast : Int.ofNat (EVM.wordOfInt (spacingCount spacing)).toNat = spacingCount spacing := by
    rw [wordOfInt_nonneg _ hc.1]
    change Int.ofNat (UInt256.ofNat (spacingCount spacing).toNat).toNat = _
    rw [ulit_toNat' _ (by change _ < 2 ^ 256; omega)]
    exact Int.toNat_of_nonneg hc.1
  have hdiv (a b : UInt256) : Int.ofNat a.toNat / Int.ofNat b.toNat =
      Int.ofNat (UInt256.div a b).toNat := by rw [udiv_toNat]; rfl
  unfold spacingLiquidityRaw spacingLiquidity
  rw [spacingCountRaw_eq word spacing hclean hlo hhi, ← hcast]
  have hn : (2 ^ 128 - 1 : Int) = Int.ofNat (UInt256.ofNat (2 ^ 128 - 1)).toNat := by decide
  rw [hn, hdiv]
  simp only [wordOfInt_ofNat_toNat]

end Benchmarks.UniswapV3.Pool
