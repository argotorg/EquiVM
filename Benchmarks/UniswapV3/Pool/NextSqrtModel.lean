import Benchmarks.UniswapV3.Pool.FullMathRoundSource
import Benchmarks.UniswapV3.Pool.UnsafeDivRoundSource
import Benchmarks.UniswapV3.Pool.SafeCast160Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure NextSqrtArgs where
  price : UInt256
  liquidity : UInt256
  amount : UInt256
  add : Bool

def NextSqrtArgs.Fits (a : NextSqrtArgs) : Prop :=
  a.price.toNat < 2 ^ 160 ∧ a.liquidity.toNat < 2 ^ 128

def nextSqrtFunction (one : Bool) : FunctionDecl := contract.functions[if one then 49 else 48]!

def nextSqrtName (one : Bool) : String :=
  if one then "SqrtPriceMath_getNextSqrtPriceFromAmount1RoundingDown"
  else "SqrtPriceMath_getNextSqrtPriceFromAmount0RoundingUp"

theorem nextSqrtLookup (one : Bool) :
    lookupCallable? contract (nextSqrtName one) = some (nextSqrtFunction one).toCallable := by
  cases one <;> rfl

def NextSqrtArgs.values (a : NextSqrtArgs) : List Value :=
  [.int (Int.ofNat a.price.toNat), .int (Int.ofNat a.liquidity.toNat),
    .int (Int.ofNat a.amount.toNat), .bool a.add]

def nextSqrtLocals (a : NextSqrtArgs) : Store :=
  let locals := ((∅ : Store).insert "add" (.bool a.add)).insert "amount"
    (.int (Int.ofNat a.amount.toNat))
  let locals := locals.insert "liquidity" (.int (Int.ofNat a.liquidity.toNat))
  locals.insert "sqrtPX96" (.int (Int.ofNat a.price.toNat))

def nextSqrtFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {contract := contract, locals := nextSqrtLocals a, immutables := imms}

theorem nextSqrtBind (one : Bool) (a : NextSqrtArgs) :
    bindParams? (nextSqrtFunction one).params a.values = some (nextSqrtLocals a) := by
  cases one <;> rfl

theorem nextSqrtGet (imms : Store) (a : NextSqrtArgs) :
    (nextSqrtFrame imms a).locals.get? "sqrtPX96" = some (.int (Int.ofNat a.price.toNat)) ∧
      (nextSqrtFrame imms a).locals.get? "liquidity" = some (.int (Int.ofNat a.liquidity.toNat)) ∧
      (nextSqrtFrame imms a).locals.get? "amount" = some (.int (Int.ofNat a.amount.toNat)) ∧
      (nextSqrtFrame imms a).locals.get? "add" = some (.bool a.add) := by
  simp only [nextSqrtFrame, nextSqrtLocals, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert]
  exact ⟨rfl, rfl, rfl, rfl⟩

def nextSqrt1Small (a : NextSqrtArgs) : Prop := a.amount.toNat < 2 ^ 160

instance (a : NextSqrtArgs) : Decidable (nextSqrt1Small a) :=
  inferInstanceAs (Decidable (_ < _))

def nextSqrt1ScaledAmount (a : NextSqrtArgs) : UInt256 :=
  UInt256.shiftLeft a.amount (UInt256.ofNat 96)

def nextSqrt1QuotientValid (a : NextSqrtArgs) : Prop :=
  if nextSqrt1Small a then a.add = true → a.liquidity.toNat ≠ 0
  else if a.add then fullMathValid a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity
  else fullMathRoundValid a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity

noncomputable def nextSqrt1Quotient (a : NextSqrtArgs) : UInt256 :=
  if nextSqrt1Small a then
    if a.add then UInt256.div (nextSqrt1ScaledAmount a) a.liquidity
    else unsafeDivRoundResult (nextSqrt1ScaledAmount a) a.liquidity
  else if a.add then fullMathResult a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity
  else fullMathRoundResult a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity

def nextSqrt1OutputValid (a : NextSqrtArgs) : Prop :=
  if a.add then a.price.toNat ≤ (a.price + nextSqrt1Quotient a).toNat ∧
    safeCast160Valid (a.price + nextSqrt1Quotient a)
  else (nextSqrt1Quotient a).toNat < a.price.toNat

def nextSqrt1Valid (a : NextSqrtArgs) : Prop := nextSqrt1QuotientValid a ∧ nextSqrt1OutputValid a

noncomputable def nextSqrt1Result (a : NextSqrtArgs) : UInt256 :=
  if a.add then a.price + nextSqrt1Quotient a else UInt256.sub a.price (nextSqrt1Quotient a)

theorem nextSqrt1Result_fits (a : NextSqrtArgs) (hfit : a.Fits) (hv : nextSqrt1OutputValid a) :
    (nextSqrt1Result a).toNat < 2 ^ 160 := by
  cases ha : a.add
  · simp only [nextSqrt1OutputValid, ha, Bool.false_eq_true, if_false] at hv
    simp only [nextSqrt1Result, ha, Bool.false_eq_true, if_false]
    rw [usub_toNat (Nat.le_of_lt hv)]
    exact lt_of_le_of_lt (Nat.sub_le _ _) hfit.1
  · simp only [nextSqrt1OutputValid, ha, if_true] at hv
    simp only [nextSqrt1Result, ha, if_true]
    exact (safeCast160Valid_iff _).mp hv.2

end Benchmarks.UniswapV3.Pool
