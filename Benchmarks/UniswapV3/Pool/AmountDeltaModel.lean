import Benchmarks.UniswapV3.Pool.FullMathRoundBounds
import Benchmarks.UniswapV3.Pool.UnsafeDivRoundSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

structure AmountDeltaArgs where
  sqrtA : UInt256
  sqrtB : UInt256
  liquidity : UInt256
  roundUp : Bool

def AmountDeltaArgs.Fits (a : AmountDeltaArgs) : Prop :=
  a.sqrtA.toNat < 2 ^ 160 ∧ a.sqrtB.toNat < 2 ^ 160 ∧ a.liquidity.toNat < 2 ^ 128

def amountDeltaLower (a : AmountDeltaArgs) : UInt256 :=
  if a.sqrtB.toNat < a.sqrtA.toNat then a.sqrtB else a.sqrtA

def amountDeltaUpper (a : AmountDeltaArgs) : UInt256 :=
  if a.sqrtB.toNat < a.sqrtA.toNat then a.sqrtA else a.sqrtB

def amountDeltaDifference (a : AmountDeltaArgs) : UInt256 :=
  UInt256.land (UInt256.sub (amountDeltaUpper a) (amountDeltaLower a)) (UInt256.ofNat (2 ^ 160 - 1))

def amountDeltaNumerator (a : AmountDeltaArgs) : UInt256 := UInt256.shiftLeft a.liquidity ⟨96⟩

def amountDeltaValid (second : Bool) (a : AmountDeltaArgs) : Prop :=
  second = true ∨ 0 < (amountDeltaLower a).toNat

def amountDeltaFactor (second : Bool) (a : AmountDeltaArgs) : UInt256 :=
  if second then a.liquidity else amountDeltaNumerator a

def amountDeltaDenominator (second : Bool) (a : AmountDeltaArgs) : UInt256 :=
  if second then UInt256.ofNat (2 ^ 96) else amountDeltaUpper a

noncomputable def amountDeltaMulResult (second : Bool) (a : AmountDeltaArgs) : UInt256 :=
  if a.roundUp then fullMathRoundResult (amountDeltaFactor second a) (amountDeltaDifference a)
    (amountDeltaDenominator second a)
  else fullMathResult (amountDeltaFactor second a) (amountDeltaDifference a)
    (amountDeltaDenominator second a)

noncomputable def amountDeltaResult (second : Bool) (a : AmountDeltaArgs) : UInt256 :=
  if second then amountDeltaMulResult second a
  else if a.roundUp then unsafeDivRoundResult (amountDeltaMulResult second a) (amountDeltaLower a)
  else UInt256.div (amountDeltaMulResult second a) (amountDeltaLower a)

def amountDeltaFunction (second : Bool) : FunctionDecl := contract.functions[if second then 37 else 36]!

def amountDeltaName (second : Bool) : Ident :=
  if second then "SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool"
  else "SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool"

theorem amountDeltaLookup (second : Bool) : lookupCallable? contract (amountDeltaName second) =
    some (amountDeltaFunction second).toCallable := by cases second <;> rfl

def amountDeltaLocals (a : AmountDeltaArgs) : Store :=
  let locals := (∅ : Store).insert "roundUp" (.bool a.roundUp)
  let locals := locals.insert "liquidity" (.int (Int.ofNat a.liquidity.toNat))
  let locals := locals.insert "sqrtRatioBX96" (.int (Int.ofNat a.sqrtB.toNat))
  locals.insert "sqrtRatioAX96" (.int (Int.ofNat a.sqrtA.toNat))

def amountDeltaFrame (imms : Store) (a : AmountDeltaArgs) : Frame :=
  {contract := contract, locals := amountDeltaLocals a, immutables := imms}

theorem amountDeltaBind (second : Bool) (a : AmountDeltaArgs) :
    bindParams? (amountDeltaFunction second).params
      [.int (Int.ofNat a.sqrtA.toNat), .int (Int.ofNat a.sqrtB.toNat),
        .int (Int.ofNat a.liquidity.toNat), .bool a.roundUp] = some (amountDeltaLocals a) := by
  cases second <;> rfl

end Benchmarks.UniswapV3.Pool
