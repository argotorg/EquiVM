import Benchmarks.UniswapV3.Pool.SourceWordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- Constants from the unrolled TickMath square-root routine, in execution order.
def tickSqrtFactors : List (Nat × Nat) :=
  [(2, 340248342086729790484326174814286782778),
   (4, 340214320654664324051920982716015181260),
   (8, 340146287995602323631171512101879684304),
   (16, 340010263488231146823593991679159461444),
   (32, 339738377640345403697157401104375502016),
   (64, 339195258003219555707034227454543997025),
   (128, 338111622100601834656805679988414885971),
   (256, 335954724994790223023589805789778977700),
   (512, 331682121138379247127172139078559817300),
   (1024, 323299236684853023288211250268160618739),
   (2048, 307163716377032989948697243942600083929),
   (4096, 277268403626896220162999269216087595045),
   (8192, 225923453940442621947126027127485391333),
   (16384, 149997214084966997727330242082538205943),
   (32768, 66119101136024775622716233608466517926),
   (65536, 12847376061809297530290974190478138313),
   (131072, 485053260817066172746253684029974020),
   (262144, 691415978906521570653435304214168),
   (524288, 1404880482679654955896180642)]

def tickSqrtInitial (absTick : UInt256) : UInt256 :=
  if UInt256.land absTick ⟨1⟩ = ⟨0⟩ then UInt256.ofNat (2 ^ 128)
  else UInt256.ofNat 340265354078544963557816517032075149313

def tickSqrtStep (absTick ratio : UInt256) (factor : Nat × Nat) : UInt256 :=
  if UInt256.land absTick (UInt256.ofNat factor.1) = ⟨0⟩ then ratio
  else UInt256.shiftRight (UInt256.mul (UInt256.ofNat factor.2) ratio) ⟨128⟩

def tickSqrtRatio (absTick : UInt256) : UInt256 :=
  tickSqrtFactors.foldl (tickSqrtStep absTick) (tickSqrtInitial absTick)

def tickSqrtInvert (tick : Int) (ratio : UInt256) : UInt256 :=
  if 0 < tick then UInt256.div (UInt256.lnot ⟨0⟩) ratio else ratio

def tickSqrtRound (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight ratio ⟨32⟩ +
    (if UInt256.mod ratio (UInt256.ofNat (2 ^ 32)) = ⟨0⟩ then ⟨0⟩ else ⟨1⟩)

def tickSqrtRaw (tick : Int) : UInt256 :=
  tickSqrtRound (tickSqrtInvert tick (tickSqrtRatio (UInt256.ofNat tick.natAbs)))

def tickSqrtValue (tick : Int) : UInt256 :=
  UInt256.land (tickSqrtRaw tick) (UInt256.ofNat (2 ^ 160 - 1))

-- LIBRARY CANDIDATE: bounds for a fixed-point multiply with a factor below one.
theorem mulShift128_bounds (ratio : UInt256) (factor low : Nat)
    (hr : ratio.toNat ≤ 2 ^ 128) (hf : factor < 2 ^ 128) (hl : low ≤ ratio.toNat) :
    low * factor / 2 ^ 128 ≤
        (UInt256.shiftRight (UInt256.mul (UInt256.ofNat factor) ratio) ⟨128⟩).toNat ∧
      (UInt256.shiftRight (UInt256.mul (UInt256.ofNat factor) ratio) ⟨128⟩).toNat ≤ 2 ^ 128 := by
  have hfactor : (UInt256.ofNat factor).toNat = factor :=
    UInt256.toNat_ofNat_of_lt (lt_trans hf (by decide))
  have hprod : factor * ratio.toNat < UInt256.size := by
    calc
      factor * ratio.toNat ≤ factor * 2 ^ 128 := Nat.mul_le_mul_left _ hr
      _ < 2 ^ 128 * 2 ^ 128 := Nat.mul_lt_mul_of_pos_right hf (by decide)
      _ = UInt256.size := by decide
  rw [rpowShiftRight128_toNat, u256_mul_toNat, hfactor, Nat.mod_eq_of_lt hprod]
  constructor
  · exact Nat.div_le_div_right (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left factor hl)
  · have hle : factor * ratio.toNat ≤ 2 ^ 128 * 2 ^ 128 := by
      calc
        factor * ratio.toNat ≤ factor * 2 ^ 128 := Nat.mul_le_mul_left _ hr
        _ ≤ 2 ^ 128 * 2 ^ 128 := Nat.mul_le_mul_right _ (Nat.le_of_lt hf)
    have hdiv := Nat.div_le_div_right (c := 2 ^ 128) hle
    simpa using hdiv

theorem tickSqrtFold_bounds (absTick ratio : UInt256) (factors : List (Nat × Nat))
    (low : Nat) (hr : ratio.toNat ≤ 2 ^ 128) (hl : low ≤ ratio.toNat)
    (hf : ∀ f ∈ factors, f.2 < 2 ^ 128) :
    factors.foldl (fun n f ↦ n * f.2 / 2 ^ 128) low ≤
        (factors.foldl (tickSqrtStep absTick) ratio).toNat ∧
      (factors.foldl (tickSqrtStep absTick) ratio).toNat ≤ 2 ^ 128 := by
  induction factors generalizing ratio low with
  | nil => exact ⟨hl, hr⟩
  | cons f fs ih =>
    simp only [List.foldl_cons]
    apply ih
    · unfold tickSqrtStep
      split
      · exact hr
      · exact (mulShift128_bounds ratio f.2 low hr (hf f (by simp)) hl).2
    · unfold tickSqrtStep
      split
      · have h : low * f.2 ≤ low * 2 ^ 128 :=
          Nat.mul_le_mul_left _ (Nat.le_of_lt (hf f (by simp)))
        have hd := Nat.div_le_div_right (c := 2 ^ 128) h
        exact le_trans (by simpa using hd) hl
      · exact (mulShift128_bounds ratio f.2 low hr (hf f (by simp)) hl).1
    · intro f hf'
      exact hf f (by simp [hf'])

theorem tickSqrtRatio_bounds (absTick : UInt256) :
    0 < (tickSqrtRatio absTick).toNat ∧ (tickSqrtRatio absTick).toNat ≤ 2 ^ 128 := by
  have hinit : 340265354078544963557816517032075149313 ≤ (tickSqrtInitial absTick).toNat ∧
      (tickSqrtInitial absTick).toNat ≤ 2 ^ 128 := by
    unfold tickSqrtInitial
    split <;> constructor <;> decide
  have h := tickSqrtFold_bounds absTick (tickSqrtInitial absTick) tickSqrtFactors
    340265354078544963557816517032075149313 hinit.2 hinit.1 (by decide +kernel)
  have hlow : 0 < tickSqrtFactors.foldl (fun n f ↦ n * f.2 / 2 ^ 128)
      340265354078544963557816517032075149313 := by native_decide
  exact ⟨lt_of_lt_of_le hlow h.1, h.2⟩

end Benchmarks.UniswapV3.Pool
