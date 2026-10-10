import Benchmarks.UniswapV3.Pool.SwapCacheSource
import Benchmarks.UniswapV3.Pool.FeeGrowthStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure SwapStateData where
  remaining : Int
  calculated : Int
  price : UInt256
  tick : Int
  feeGrowth : UInt256
  protocolFee : UInt256
  liquidity : UInt256

def SwapStateData.value (s : SwapStateData) : Value :=
  .struct "SwapState" [
    ("amountSpecifiedRemaining", .int s.remaining), ("amountCalculated", .int s.calculated),
    ("sqrtPriceX96", .int (Int.ofNat s.price.toNat)), ("tick", .int s.tick),
    ("feeGrowthGlobalX128", .int (Int.ofNat s.feeGrowth.toNat)),
    ("protocolFee", .int (Int.ofNat s.protocolFee.toNat)),
    ("liquidity", .int (Int.ofNat s.liquidity.toNat))]

def SwapStateData.words (s : SwapStateData) : List UInt256 :=
  [EVM.wordOfInt s.remaining, EVM.wordOfInt s.calculated, s.price, EVM.wordOfInt s.tick,
    s.feeGrowth, s.protocolFee, s.liquidity]

def swapStateInitial (a : SwapArgs) (evm : EVM.State) : SwapStateData :=
  {remaining := a.amountSpecified, calculated := 0,
    price := slot0FieldWord 0 20 evm.accountMap evm.executionEnv,
    tick := slot0TickValue evm.accountMap evm.executionEnv,
    feeGrowth := feeGrowthWord (!a.zeroForOne)
      (storeSlot0Unlocked evm false).accountMap evm.executionEnv,
    protocolFee := ⟨0⟩, liquidity := (swapCacheInitial a evm).liquidityStart}

def swapExactInput (a : SwapArgs) : Bool := decide (0 < a.amountSpecified)

def swapExactFrame (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) : Frame :=
  {swapCachedFrame v a evm with
    locals := (swapCachedFrame v a evm).locals.insert "exactInput" (.bool (swapExactInput a))}

def swapReadyFrame (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) : Frame :=
  {swapExactFrame v a evm with
    locals := (swapExactFrame v a evm).locals.insert "state" (swapStateInitial a evm).value}

def swapInitialFeeExpr : Expr :=
  .ite (.var "zeroForOne") (.storage ⟨"feeGrowthGlobal0X128", []⟩)
    (.storage ⟨"feeGrowthGlobal1X128", []⟩)

def swapInitialStateExpr : Expr :=
  .structLit "SwapState" [
    ("amountSpecifiedRemaining", .var "amountSpecified"), ("amountCalculated", .intLit 0),
    ("sqrtPriceX96", .field (.var "slot0Start") "sqrtPriceX96"),
    ("tick", .field (.var "slot0Start") "tick"),
    ("feeGrowthGlobalX128", swapInitialFeeExpr), ("protocolFee", .intLit 0),
    ("liquidity", .field (.var "cache") "liquidityStart")]

macro "swap_cached_get" : tactic =>
  `(tactic| (simp only [swapCachedFrame]; swap_time_get))

macro "swap_exact_get" : tactic =>
  `(tactic| (simp only [swapExactFrame, swapCachedFrame]; swap_time_get))

theorem swapExactInputSource (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    ExecStmt config (swapCachedFrame v a evm) (storeSlot0Unlocked evm false)
      swapTransition.body[11]!
      (.ok (swapExactFrame v a evm) (storeSlot0Unlocked evm false)) := by
  apply ExecStmt.letDecl
  have he : evalExpr? config (swapCachedFrame v a evm) (storeSlot0Unlocked evm false)
      (.var "amountSpecified") = .ok (.int a.amountSpecified) :=
    evalExpr_var_get (by swap_cached_get)
  simp only [evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind, pure, swapExactInput]

theorem evalSwapInitialFee (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    evalExpr? config (swapExactFrame v a evm) (storeSlot0Unlocked evm false) swapInitialFeeExpr =
      .ok (.int (Int.ofNat (swapStateInitial a evm).feeGrowth.toNat)) := by
  have hz : evalExpr? config (swapExactFrame v a evm) (storeSlot0Unlocked evm false)
      (.var "zeroForOne") = .ok (.bool a.zeroForOne) :=
    evalExpr_var_get (by swap_exact_get)
  rw [swapInitialFeeExpr, evalExpr?, hz]
  cases hdir : a.zeroForOne
  · have he := evalFeeGrowthGlobal1X128 (swapExactFrame v a evm).locals (immStore v)
      (storeSlot0Unlocked evm false) (by swap_exact_get)
    change evalExpr? config (swapExactFrame v a evm) _ _ = _ at he
    simpa only [bind, EvalResult.bind, swapStateInitial, hdir, Bool.not_false,
      feeGrowthWord, feeGrowthSlot, if_true, storeSlot0Unlocked_executionEnv] using he
  · have he := evalFeeGrowthGlobal0X128 (swapExactFrame v a evm).locals (immStore v)
      (storeSlot0Unlocked evm false) (by swap_exact_get)
    change evalExpr? config (swapExactFrame v a evm) _ _ = _ at he
    simpa only [bind, EvalResult.bind, swapStateInitial, hdir, Bool.not_true,
      feeGrowthWord, feeGrowthSlot, Bool.false_eq_true, if_false,
      storeSlot0Unlocked_executionEnv] using he

theorem evalSwapInitialState (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    evalExpr? config (swapExactFrame v a evm) (storeSlot0Unlocked evm false)
      swapInitialStateExpr = .ok (swapStateInitial a evm).value := by
  have hr : evalExpr? config (swapExactFrame v a evm) (storeSlot0Unlocked evm false)
      (.var "amountSpecified") = .ok (.int a.amountSpecified) :=
    evalExpr_var_get (by swap_exact_get)
  have hs : evalExpr? config (swapExactFrame v a evm) (storeSlot0Unlocked evm false)
      (.var "slot0Start") = .ok (slot0StructValue evm.accountMap evm.executionEnv) :=
    evalExpr_var_get (by swap_exact_get)
  have hp := evalExpr_structField (name := "sqrtPriceX96") hs rfl
  have ht := evalExpr_structField (name := "tick") hs rfl
  have hc : evalExpr? config (swapExactFrame v a evm) (storeSlot0Unlocked evm false)
      (.var "cache") = .ok (swapCacheInitial a evm).value :=
    evalExpr_var_get (by swap_exact_get)
  have hl := evalExpr_structField (name := "liquidityStart") hc rfl
  have hf := evalSwapInitialFee v a evm
  simp only [swapInitialStateExpr, evalExpr?, evalStructFields?, hr, hp, ht, hl, hf,
    bind, EvalResult.bind, pure, swapStateInitial, SwapStateData.value]
  rfl

theorem swapStateSource (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    ExecBlock config (swapCachedFrame v a evm) (storeSlot0Unlocked evm false)
      ((swapTransition.body.drop 11).take 2)
      (.ok (swapReadyFrame v a evm) (storeSlot0Unlocked evm false)) := by
  exact ExecBlock.consNormal (swapExactInputSource v a evm)
    (ExecBlock.consNormal (ExecStmt.letDecl (evalSwapInitialState v a evm)) ExecBlock.nil)

theorem swapInitSource (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hself : evm.executionEnv.codeOwner = v.original)
    (hn : a.amountSpecified ≠ 0)
    (hu : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hl : swapLimitValid a evm) :
    ExecBlock config (swapFrame v a) evm (swapTransition.body.take 13)
      (.ok (swapReadyFrame v a evm) (storeSlot0Unlocked evm false)) := by
  change ExecBlock config _ _ (swapTransition.body.take 9 ++
    (swapTransition.body.drop 9).take 2 ++ (swapTransition.body.drop 11).take 2) _
  exact execBlock_append_ok
    (execBlock_append_ok (swapLockSource v a evm hwv hself hn hu hl) (swapCacheSource v a evm))
    (swapStateSource v a evm)

end Benchmarks.UniswapV3.Pool
