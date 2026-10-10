import Benchmarks.UniswapV3.Pool.NextSqrt0Model

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

structure NextPriceArgs where
  price : UInt256
  liquidity : UInt256
  amount : UInt256
  zeroForOne : Bool

def NextPriceArgs.Fits (a : NextPriceArgs) : Prop :=
  a.price.toNat < 2 ^ 160 ∧ a.liquidity.toNat < 2 ^ 128

def NextPriceArgs.sqrtArgs (a : NextPriceArgs) (input : Bool) : NextSqrtArgs :=
  ⟨a.price, a.liquidity, a.amount, input⟩

def nextPriceOne (input : Bool) (a : NextPriceArgs) : Bool :=
  if input then !a.zeroForOne else a.zeroForOne

def nextPriceFunction (input : Bool) : FunctionDecl :=
  contract.functions[if input then 38 else 39]!

def nextPriceName (input : Bool) : String :=
  if input then "SqrtPriceMath_getNextSqrtPriceFromInput"
  else "SqrtPriceMath_getNextSqrtPriceFromOutput"

def nextPriceAmountName (input : Bool) : String := if input then "amountIn" else "amountOut"

def NextPriceArgs.values (a : NextPriceArgs) : List Value :=
  [.int (Int.ofNat a.price.toNat), .int (Int.ofNat a.liquidity.toNat),
    .int (Int.ofNat a.amount.toNat), .bool a.zeroForOne]

def nextPriceLocals (input : Bool) (a : NextPriceArgs) : Store :=
  let locals := ((∅ : Store).insert "zeroForOne" (.bool a.zeroForOne)).insert
    (nextPriceAmountName input) (.int (Int.ofNat a.amount.toNat))
  let locals := locals.insert "liquidity" (.int (Int.ofNat a.liquidity.toNat))
  locals.insert "sqrtPX96" (.int (Int.ofNat a.price.toNat))

def nextPriceFrame (imms : Store) (input : Bool) (a : NextPriceArgs) : Frame :=
  {contract := contract, locals := nextPriceLocals input a, immutables := imms}

theorem nextPriceLookup (input : Bool) :
    lookupCallable? contract (nextPriceName input) = some (nextPriceFunction input).toCallable := by
  cases input <;> rfl

theorem nextPriceBind (input : Bool) (a : NextPriceArgs) :
    bindParams? (nextPriceFunction input).params a.values = some (nextPriceLocals input a) := by
  cases input <;> rfl

def nextPriceGuard (a : NextPriceArgs) : Prop := 0 < a.price.toNat ∧ 0 < a.liquidity.toNat

def nextPriceCalleeValid (input : Bool) (a : NextPriceArgs) : Prop :=
  if nextPriceOne input a then nextSqrt1Valid (a.sqrtArgs input)
  else nextSqrt0Valid (a.sqrtArgs input)

def nextPriceValid (input : Bool) (a : NextPriceArgs) : Prop :=
  nextPriceGuard a ∧ nextPriceCalleeValid input a

noncomputable def nextPriceResult (input : Bool) (a : NextPriceArgs) : UInt256 :=
  if nextPriceOne input a then nextSqrt1Result (a.sqrtArgs input)
  else nextSqrt0Result (a.sqrtArgs input)

noncomputable def nextPriceRawResult (input : Bool) (a : NextPriceArgs)
    (priceRaw : UInt256) : UInt256 :=
  if nextPriceOne input a then nextSqrt1Result (a.sqrtArgs input)
  else nextSqrt0RawResult (a.sqrtArgs input) priceRaw

theorem nextPriceResult_fits (input : Bool) (a : NextPriceArgs) (ha : a.Fits)
    (hv : nextPriceCalleeValid input a) : (nextPriceResult input a).toNat < 2 ^ 160 := by
  cases ho : nextPriceOne input a
  · simpa only [nextPriceResult, ho, Bool.false_eq_true, if_false]
      using nextSqrt0Result_fits (a.sqrtArgs input) ha
  · simp only [nextPriceResult, ho, if_true]
    apply nextSqrt1Result_fits (a.sqrtArgs input) ha
    have hh : nextSqrt1Valid (a.sqrtArgs input) := by
      simpa only [nextPriceCalleeValid, ho, if_true] using hv
    exact hh.2

theorem nextPriceResult_clean (input : Bool) (a : NextPriceArgs) (priceRaw : UInt256)
    (ha : a.Fits) (hv : nextPriceCalleeValid input a)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.price) :
    UInt256.land (nextPriceRawResult input a priceRaw) (UInt256.ofNat (2 ^ 160 - 1)) =
      nextPriceResult input a := by
  cases ho : nextPriceOne input a
  · simpa only [nextPriceRawResult, nextPriceResult, ho, Bool.false_eq_true, if_false]
      using nextSqrt0Result_clean (a.sqrtArgs input) priceRaw hp
  · simp only [nextPriceRawResult, nextPriceResult, ho, if_true]
    apply u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide)
    simpa only [nextPriceResult, ho, if_true] using nextPriceResult_fits input a ha hv

end Benchmarks.UniswapV3.Pool
