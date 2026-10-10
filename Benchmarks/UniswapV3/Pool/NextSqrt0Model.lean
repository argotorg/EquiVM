import Benchmarks.UniswapV3.Pool.NextSqrtModel
import Benchmarks.UniswapV3.Pool.WordShiftBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def nextSqrt0Numerator (a : NextSqrtArgs) : UInt256 :=
  UInt256.shiftLeft a.liquidity (UInt256.ofNat 96)

def nextSqrt0Product (a : NextSqrtArgs) : UInt256 := a.amount * a.price

def nextSqrt0ProductExact (a : NextSqrtArgs) : Prop :=
  UInt256.div (nextSqrt0Product a) a.amount = a.price

instance (a : NextSqrtArgs) : Decidable (nextSqrt0ProductExact a) :=
  inferInstanceAs (Decidable (_ = _))

def nextSqrt0Denominator (a : NextSqrtArgs) : UInt256 :=
  if a.add then nextSqrt0Numerator a + nextSqrt0Product a
  else UInt256.sub (nextSqrt0Numerator a) (nextSqrt0Product a)

def nextSqrt0Fast (a : NextSqrtArgs) : Prop :=
  nextSqrt0ProductExact a ∧
    (nextSqrt0Numerator a).toNat ≤ (nextSqrt0Numerator a + nextSqrt0Product a).toNat

instance (a : NextSqrtArgs) : Decidable (nextSqrt0Fast a) :=
  inferInstanceAs (Decidable (_ ∧ _))

def nextSqrt0SubtractGuard (a : NextSqrtArgs) : Prop :=
  nextSqrt0ProductExact a ∧ (nextSqrt0Product a).toNat < (nextSqrt0Numerator a).toNat

def nextSqrt0FallbackQuotient (a : NextSqrtArgs) : UInt256 :=
  UInt256.div (nextSqrt0Numerator a) a.price

def nextSqrt0FallbackSum (a : NextSqrtArgs) : UInt256 := nextSqrt0FallbackQuotient a + a.amount

def nextSqrt0FallbackValid (a : NextSqrtArgs) : Prop :=
  a.price.toNat ≠ 0 ∧ (nextSqrt0FallbackQuotient a).toNat ≤ (nextSqrt0FallbackSum a).toNat

noncomputable def nextSqrt0FullResult (a : NextSqrtArgs) : UInt256 :=
  fullMathRoundResult (nextSqrt0Numerator a) a.price (nextSqrt0Denominator a)

def nextSqrt0FullValid (a : NextSqrtArgs) : Prop :=
  fullMathRoundValid (nextSqrt0Numerator a) a.price (nextSqrt0Denominator a)

def nextSqrt0Valid (a : NextSqrtArgs) : Prop :=
  if a.amount.toNat = 0 then True
  else if a.add then
    if nextSqrt0Fast a then nextSqrt0FullValid a else nextSqrt0FallbackValid a
  else nextSqrt0SubtractGuard a ∧ nextSqrt0FullValid a ∧
    safeCast160Valid (nextSqrt0FullResult a)

noncomputable def nextSqrt0Computed (a : NextSqrtArgs) : UInt256 :=
  if a.add = true ∧ ¬nextSqrt0Fast a then
    unsafeDivRoundResult (nextSqrt0Numerator a) (nextSqrt0FallbackSum a)
  else nextSqrt0FullResult a

noncomputable def nextSqrt0RawResult (a : NextSqrtArgs) (priceRaw : UInt256) : UInt256 :=
  if a.amount.toNat = 0 then priceRaw else nextSqrt0Computed a

noncomputable def nextSqrt0Result (a : NextSqrtArgs) : UInt256 :=
  if a.amount.toNat = 0 then a.price
  else UInt256.land (nextSqrt0Computed a) (UInt256.ofNat (2 ^ 160 - 1))

theorem nextSqrt0Result_clean (a : NextSqrtArgs) (priceRaw : UInt256)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.price) :
    UInt256.land (nextSqrt0RawResult a priceRaw) (UInt256.ofNat (2 ^ 160 - 1)) =
      nextSqrt0Result a := by
  by_cases hz : a.amount.toNat = 0 <;>
    simp only [nextSqrt0RawResult, nextSqrt0Result, hz, ↓reduceIte, hp]

theorem nextSqrt0Result_fits (a : NextSqrtArgs) (ha : a.Fits) :
    (nextSqrt0Result a).toNat < 2 ^ 160 := by
  by_cases hz : a.amount.toNat = 0
  · simpa only [nextSqrt0Result, if_pos hz] using ha.1
  · rw [nextSqrt0Result, if_neg hz]
    exact u256LandMaskToNatLtOfToNat (bits := 160) _ _ (by decide)

theorem nextSqrt0NumeratorClean (liquidityRaw : UInt256) (a : NextSqrtArgs)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity) :
    UInt256.land (UInt256.shiftLeft liquidityRaw (UInt256.ofNat 96))
      (UInt256.ofNat 26959946667150639794667015087019630673557916260026308143510066298880) =
      nextSqrt0Numerator a := by
  rw [show UInt256.ofNat
    26959946667150639794667015087019630673557916260026308143510066298880 =
      UInt256.shiftLeft (UInt256.ofNat (2 ^ 128 - 1)) (UInt256.ofNat 96) by decide]
  rw [wordShiftLeft_land _ _ _ (by decide), hl]
  rfl

end Benchmarks.UniswapV3.Pool
