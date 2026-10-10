import Benchmarks.UniswapV4PoolManager.WordSignedSource
import Benchmarks.UniswapV4PoolManager.Signed128Range

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: an unsigned cast erases a preceding signed cast of the same width.
theorem normalizeUintAfterSigned (bits : BitWidth) (i : Int) :
    normalizeInt (.uint bits) (normalizeInt (.sint bits) i) = normalizeInt (.uint bits) i := by
  simp only [normalizeInt]
  split
  · exact Int.emod_emod _ _
  · simp only [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod]

def liquidityMagnitudeValue (delta : Int) : Int := if delta < 0 then -delta else delta
def liquidityMagnitude (delta : Int) : UInt256 := EVM.wordOfInt (liquidityMagnitudeValue delta)

theorem liquidityMagnitude_range {delta : Int}
    (hlo : -(2^127 : Int) ≤ delta) (hhi : delta < 2^127) :
    0 ≤ liquidityMagnitudeValue delta ∧ liquidityMagnitudeValue delta < 2^128 := by
  unfold liquidityMagnitudeValue
  split <;> omega

theorem liquidityMagnitude_value {delta : Int}
    (hlo : -(2^127 : Int) ≤ delta) (hhi : delta < 2^127) :
    Int.ofNat (liquidityMagnitude delta).toNat = liquidityMagnitudeValue delta := by
  rw [liquidityMagnitude, wordOfIntResidue]
  have hr := liquidityMagnitude_range hlo hhi
  exact Int.emod_eq_of_lt hr.1 (by omega)

theorem liquidityMagnitude_bound {delta : Int}
    (hlo : -(2^127 : Int) ≤ delta) (hhi : delta < 2^127) :
    (liquidityMagnitude delta).toNat < 2^128 := by
  apply Int.ofNat_lt.mp
  change Int.ofNat (liquidityMagnitude delta).toNat < Int.ofNat (2^128)
  rw [liquidityMagnitude_value hlo hhi]
  exact (liquidityMagnitude_range hlo hhi).2

theorem liquidityMagnitude_positive {delta : Int}
    (hlo : -(2^127 : Int) ≤ delta) (hhi : delta < 2^127) (hz : ¬delta < 0) :
    UInt256.land (UInt256.ofNat 340282366920938463463374607431768211455) (EVM.wordOfInt delta) =
      liquidityMagnitude delta := by
  have he : liquidityMagnitude delta = EVM.wordOfInt delta := by
    simp only [liquidityMagnitude, liquidityMagnitudeValue, if_neg hz]
  rw [← he, u256_land_comm]
  exact u256LandMaskCleanOfToNat _ _ rfl (liquidityMagnitude_bound hlo hhi)

theorem liquidityMagnitude_negative {delta : Int}
    (hlo : -(2^127 : Int) ≤ delta) (hhi : delta < 2^127) (hz : delta < 0) :
    UInt256.land (UInt256.ofNat 340282366920938463463374607431768211455)
      (UInt256.sub ⟨0⟩ (EVM.wordOfInt delta)) = liquidityMagnitude delta := by
  have hfit : int256Fits delta := by
    change -(2^255 : Int) ≤ delta ∧ delta < 2^255
    constructor <;> omega
  have he : UInt256.sub ⟨0⟩ (EVM.wordOfInt delta) = liquidityMagnitude delta := by
    rw [← wordOfInt_signed_sub, signed_wordOfInt hfit]
    simp only [liquidityMagnitude, liquidityMagnitudeValue, if_pos hz]
    rw [show EVM.signed (⟨0⟩ : UInt256) = 0 from rfl, zero_sub]
  rw [he, u256_land_comm]
  exact u256LandMaskCleanOfToNat _ _ rfl (liquidityMagnitude_bound hlo hhi)

theorem liquidityNegativeCmp {delta : Int}
    (hdlo : -(2^127 : Int) ≤ delta) (hdhi : delta < 2^127) :
    UInt256.slt (UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt delta)) ⟨0⟩ =
      UInt256.fromBool (decide (delta < 0)) := by
  have hfit : int256Fits delta := by
    change -(2^255 : Int) ≤ delta ∧ delta < 2^255
    constructor <;> omega
  have hs : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt delta) = EVM.wordOfInt delta :=
    signextend128_wordOfInt hdlo hdhi
  rw [hs, slt_signed, signed_wordOfInt hfit]
  rfl

theorem evalLiquidityMagnitudePositive {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {delta : Int}
    (hlo : -(2^127 : Int) ≤ delta) (hhi : delta < 2^127) (hz : ¬delta < 0)
    (he : evalExpr? cfg f evm e = .ok (.int delta)) :
    evalExpr? cfg f evm (.cast e (.elem (.int (.uint ⟨128, by decide⟩)))) =
      .ok (.int (Int.ofNat (liquidityMagnitude delta).toNat)) := by
  have hc := evalExpr_cast_int (intType := .uint ⟨128, by decide⟩) he
  have hn := normalizeInt_uint_eq_self ⟨128, by decide⟩ delta (by omega) (by change delta < 2^128; omega)
  simpa only [hn, liquidityMagnitude_value hlo hhi, liquidityMagnitudeValue, if_neg hz] using hc

theorem evalLiquidityMagnitudeNegative {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {delta : Int}
    (hlo : -(2^127 : Int) ≤ delta) (hhi : delta < 2^127) (hz : delta < 0)
    (he : evalExpr? cfg f evm e = .ok (.int delta)) :
    evalExpr? cfg f evm (.cast (.cast (.binary .sub (.intLit 0) e)
      (.elem (.int (.sint ⟨128, by decide⟩)))) (.elem (.int (.uint ⟨128, by decide⟩)))) =
      .ok (.int (Int.ofNat (liquidityMagnitude delta).toNat)) := by
  have hsub : evalExpr? cfg f evm (.binary .sub (.intLit 0) e) = .ok (.int (-delta)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide)]
    simp only [evalExpr?, he, bind, EvalResult.bind, pure, evalBinaryOp?, zero_sub]
  have hc := evalExpr_cast_int (intType := .uint ⟨128, by decide⟩)
    (evalExpr_cast_int (intType := .sint ⟨128, by decide⟩) hsub)
  have hn := normalizeInt_uint_eq_self ⟨128, by decide⟩ (-delta) (by omega) (by change -delta < 2^128; omega)
  simpa only [normalizeUintAfterSigned, hn, liquidityMagnitude_value hlo hhi,
    liquidityMagnitudeValue, if_pos hz] using hc

end Benchmarks.UniswapV4PoolManager
