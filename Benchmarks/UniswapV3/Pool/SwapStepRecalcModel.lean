import Benchmarks.UniswapV3.Pool.SwapStepPriceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

noncomputable def swapStepMax (a : SwapStepArgs) : Bool :=
  decide (a.target.toNat = (swapStepPrice a).toNat)

noncomputable def swapStepKeep (a : SwapStepArgs) (input : Bool) : Bool :=
  swapStepMax a && (if input then swapStepExactIn a else !swapStepExactIn a)

noncomputable def swapStepBeforeAmount (a : SwapStepArgs) (input : Bool) : UInt256 :=
  if swapStepExactIn a = input then swapStepInitialDelta a else UInt256.ofNat 0

noncomputable def swapStepRecalcDelta (a : SwapStepArgs) (input : Bool) : UInt256 :=
  amountDeltaResult (swapStepDeltaOne a input) (swapStepDeltaArgs a (swapStepPrice a) input)

noncomputable def swapStepAmount (a : SwapStepArgs) (input : Bool) : UInt256 :=
  if swapStepKeep a input then swapStepBeforeAmount a input else swapStepRecalcDelta a input

noncomputable def swapStepRecalcValid (a : SwapStepArgs) (input : Bool) : Prop :=
  if swapStepKeep a input then True
  else amountDeltaValid (swapStepDeltaOne a input) (swapStepDeltaArgs a (swapStepPrice a) input)

def swapStepRecalcCondName (a : SwapStepArgs) (input : Bool) : Ident :=
  if swapStepZeroForOne a then (if input then "__cond10" else "__cond12")
  else (if input then "__cond14" else "__cond16")

def swapStepRecalcCallName (a : SwapStepArgs) (input : Bool) : Ident :=
  if swapStepZeroForOne a then (if input then "__c9" else "__c11")
  else (if input then "__c13" else "__c15")

def swapStepRecalcTest (input : Bool) : Expr :=
  .binary .and (.var "max") (if input then .var "exactIn" else .unary .not (.var "exactIn"))

def swapStepRecalcBlock (a : SwapStepArgs) (input : Bool) : List Stmt :=
  [.letDecl (swapStepRecalcCondName a input) none (.intLit 0),
   .ite (swapStepRecalcTest input)
     [.assign .localVar ⟨swapStepRecalcCondName a input, []⟩ (.var (swapStepAmountName input))]
     [.internalCall (amountDeltaName (swapStepDeltaOne a input))
        (swapStepDeltaCallArgs a input "sqrtRatioNextX96") (swapStepRecalcCallName a input),
      .assign .localVar ⟨swapStepRecalcCondName a input, []⟩
        (.var (swapStepRecalcCallName a input))],
   .assign .localVar ⟨swapStepAmountName input, []⟩ (.var (swapStepRecalcCondName a input))]

def swapStepCalcFrame (imms locals : Store) : Frame :=
  {contract := contract, immutables := imms, locals := locals}

noncomputable def swapStepMaxFrame (imms : Store) (a : SwapStepArgs) : Frame :=
  {swapStepPriceFrame imms a (swapStepExactIn a) with
    locals := (swapStepPriceFrame imms a (swapStepExactIn a)).locals.insert
      "max" (.bool (swapStepMax a))}

def swapStepRecalcZeroLocals (locals : Store) (a : SwapStepArgs) (input : Bool) : Store :=
  locals.insert (swapStepRecalcCondName a input) (.int 0)

noncomputable def swapStepRecalcCallLocals (locals : Store) (a : SwapStepArgs)
    (input : Bool) : Store :=
  (swapStepRecalcZeroLocals locals a input).insert (swapStepRecalcCallName a input)
    (.int (Int.ofNat (swapStepRecalcDelta a input).toNat))

noncomputable def swapStepRecalcChosenLocals (locals : Store) (a : SwapStepArgs)
    (input : Bool) : Store :=
  (if swapStepKeep a input then swapStepRecalcZeroLocals locals a input
    else swapStepRecalcCallLocals locals a input).insert (swapStepRecalcCondName a input)
      (.int (Int.ofNat (swapStepAmount a input).toNat))

noncomputable def swapStepRecalcLocals (locals : Store) (a : SwapStepArgs) (input : Bool) : Store :=
  (swapStepRecalcChosenLocals locals a input).insert (swapStepAmountName input)
    (.int (Int.ofNat (swapStepAmount a input).toNat))

noncomputable def swapStepAmountInFrame (imms : Store) (a : SwapStepArgs) : Frame :=
  swapStepCalcFrame imms (swapStepRecalcLocals (swapStepMaxFrame imms a).locals a true)

noncomputable def swapStepAmountsFrame (imms : Store) (a : SwapStepArgs) : Frame :=
  swapStepCalcFrame imms (swapStepRecalcLocals (swapStepAmountInFrame imms a).locals a false)

structure SwapStepCalcGet (locals : Store) (a : SwapStepArgs) : Prop where
  current : locals.get? "sqrtRatioCurrentX96" = some (.int (Int.ofNat a.current.toNat))
  price : locals.get? "sqrtRatioNextX96" = some (.int (Int.ofNat (swapStepPrice a).toNat))
  liquidity : locals.get? "liquidity" = some (.int (Int.ofNat a.liquidity.toNat))
  max : locals.get? "max" = some (.bool (swapStepMax a))
  exactIn : locals.get? "exactIn" = some (.bool (swapStepExactIn a))

def swapStepRecalcBranch (zero : Bool) : List Stmt :=
  match swapStepFunction.body[8]! with
  | .ite _ yes no => if zero then yes else no
  | _ => []

theorem swapStepRecalcBlock_eq (a : SwapStepArgs) :
    swapStepRecalcBranch (swapStepZeroForOne a) =
      swapStepRecalcBlock a true ++ swapStepRecalcBlock a false := by
  cases hz : swapStepZeroForOne a <;>
    simp only [swapStepRecalcBlock, swapStepRecalcCondName, swapStepRecalcCallName,
      swapStepDeltaOne, swapStepDeltaCallArgs, hz, Bool.false_eq_true, if_false, if_true,
      Bool.not_false, Bool.not_true]
  all_goals rfl

end Benchmarks.UniswapV3.Pool
