import Benchmarks.UniswapV3.Pool.AmountDeltaModel
import Benchmarks.UniswapV3.Pool.NextPriceModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

structure SwapStepArgs where
  current : UInt256
  target : UInt256
  liquidity : UInt256
  remaining : Int
  fee : UInt256

def SwapStepArgs.Fits (a : SwapStepArgs) : Prop :=
  a.current.toNat < 2 ^ 160 ∧ a.target.toNat < 2 ^ 160 ∧ a.liquidity.toNat < 2 ^ 128 ∧
  (-(2 ^ 255 : Int) ≤ a.remaining ∧ a.remaining < 2 ^ 255) ∧ a.fee.toNat < 2 ^ 24

def swapStepZeroForOne (a : SwapStepArgs) : Bool := decide (a.target.toNat ≤ a.current.toNat)
def swapStepExactIn (a : SwapStepArgs) : Bool := decide (0 ≤ a.remaining)

def swapStepComplement (a : SwapStepArgs) : UInt256 :=
  UInt256.land (UInt256.sub (UInt256.ofNat 1000000) a.fee) (UInt256.ofNat (2 ^ 24 - 1))

def swapStepAbsRemaining (a : SwapStepArgs) : UInt256 :=
  UInt256.sub (UInt256.ofNat 0) (EVM.wordOfInt a.remaining)

noncomputable def swapStepBudget (a : SwapStepArgs) : UInt256 :=
  if swapStepExactIn a then
    fullMathResult (EVM.wordOfInt a.remaining) (swapStepComplement a) (UInt256.ofNat 1000000)
  else swapStepAbsRemaining a

def swapStepBudgetValid (a : SwapStepArgs) : Prop :=
  if swapStepExactIn a then
    fullMathValid (EVM.wordOfInt a.remaining) (swapStepComplement a) (UInt256.ofNat 1000000)
  else True

def swapStepDeltaOne (a : SwapStepArgs) (input : Bool) : Bool :=
  if input then !swapStepZeroForOne a else swapStepZeroForOne a

def swapStepDeltaArgs (a : SwapStepArgs) (price : UInt256) (input : Bool) : AmountDeltaArgs :=
  {sqrtA := if swapStepZeroForOne a then price else a.current
   sqrtB := if swapStepZeroForOne a then a.current else price
   liquidity := a.liquidity, roundUp := input}

noncomputable def swapStepInitialDelta (a : SwapStepArgs) : UInt256 :=
  amountDeltaResult (swapStepDeltaOne a (swapStepExactIn a))
    (swapStepDeltaArgs a a.target (swapStepExactIn a))

def swapStepInitialValid (a : SwapStepArgs) : Prop :=
  amountDeltaValid (swapStepDeltaOne a (swapStepExactIn a))
    (swapStepDeltaArgs a a.target (swapStepExactIn a))

noncomputable def swapStepReachTarget (a : SwapStepArgs) : Bool :=
  decide ((swapStepInitialDelta a).toNat ≤ (swapStepBudget a).toNat)

noncomputable def swapStepNextArgs (a : SwapStepArgs) : NextPriceArgs :=
  ⟨a.current, a.liquidity, swapStepBudget a, swapStepZeroForOne a⟩

noncomputable def swapStepPrice (a : SwapStepArgs) : UInt256 :=
  if swapStepReachTarget a then a.target
  else nextPriceResult (swapStepExactIn a) (swapStepNextArgs a)

noncomputable def swapStepPriceValid (a : SwapStepArgs) : Prop :=
  swapStepBudgetValid a ∧ swapStepInitialValid a ∧
    (if swapStepReachTarget a then True
     else nextPriceValid (swapStepExactIn a) (swapStepNextArgs a))

def swapStepFunction : FunctionDecl := contract.functions[18]!

theorem swapStepLookup : lookupCallable? contract "SwapMath_computeSwapStep" =
    some swapStepFunction.toCallable := rfl

def SwapStepArgs.values (a : SwapStepArgs) : List Value :=
  [.int (Int.ofNat a.current.toNat), .int (Int.ofNat a.target.toNat),
   .int (Int.ofNat a.liquidity.toNat), .int a.remaining, .int (Int.ofNat a.fee.toNat)]

def swapStepLocals (a : SwapStepArgs) : Store :=
  let locals := (∅ : Store).insert "feePips" (.int (Int.ofNat a.fee.toNat))
  let locals := locals.insert "amountRemaining" (.int a.remaining)
  let locals := locals.insert "liquidity" (.int (Int.ofNat a.liquidity.toNat))
  let locals := locals.insert "sqrtRatioTargetX96" (.int (Int.ofNat a.target.toNat))
  locals.insert "sqrtRatioCurrentX96" (.int (Int.ofNat a.current.toNat))

def swapStepFrame (imms : Store) (a : SwapStepArgs) : Frame :=
  {contract := contract, locals := swapStepLocals a, immutables := imms}

def swapStepZeroFrame (imms : Store) (a : SwapStepArgs) : Frame :=
  let locals := (swapStepLocals a).insert "sqrtRatioNextX96" (.int 0)
  let locals := locals.insert "amountIn" (.int 0)
  let locals := locals.insert "amountOut" (.int 0)
  {swapStepFrame imms a with locals := locals.insert "feeAmount" (.int 0)}

def swapStepDirectionFrame (imms : Store) (a : SwapStepArgs) : Frame :=
  {swapStepZeroFrame imms a with locals :=
    (swapStepZeroFrame imms a).locals.insert "zeroForOne" (.bool (swapStepZeroForOne a))}

def swapStepReadyFrame (imms : Store) (a : SwapStepArgs) : Frame :=
  {swapStepDirectionFrame imms a with locals :=
    (swapStepDirectionFrame imms a).locals.insert "exactIn" (.bool (swapStepExactIn a))}

theorem swapStepBind (a : SwapStepArgs) :
    bindParams? swapStepFunction.params a.values = some (swapStepLocals a) := rfl

theorem swapStepDeltaArgs_fits (a : SwapStepArgs) (price : UInt256) (input : Bool)
    (ha : a.Fits) (hp : price.toNat < 2 ^ 160) : (swapStepDeltaArgs a price input).Fits := by
  cases hz : swapStepZeroForOne a <;>
    simp only [AmountDeltaArgs.Fits, swapStepDeltaArgs, hz, Bool.false_eq_true, if_false, if_true]
  · exact ⟨ha.1, hp, ha.2.2.1⟩
  · exact ⟨hp, ha.1, ha.2.2.1⟩

theorem swapStepNextArgs_fits (a : SwapStepArgs) (ha : a.Fits) : (swapStepNextArgs a).Fits :=
  ⟨ha.1, ha.2.2.1⟩

theorem swapStepPrice_fits (a : SwapStepArgs) (ha : a.Fits) (hv : swapStepPriceValid a) :
    (swapStepPrice a).toNat < 2 ^ 160 := by
  cases hr : swapStepReachTarget a
  · have hn : nextPriceValid (swapStepExactIn a) (swapStepNextArgs a) := by
      simpa only [hr, Bool.false_eq_true, if_false] using hv.2.2
    simpa only [swapStepPrice, hr, Bool.false_eq_true, if_false] using
      nextPriceResult_fits (swapStepExactIn a) (swapStepNextArgs a)
        (swapStepNextArgs_fits a ha) hn.2
  · simpa only [swapStepPrice, hr, if_true] using ha.2.1

end Benchmarks.UniswapV3.Pool
