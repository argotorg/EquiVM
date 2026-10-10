import Benchmarks.UniswapV3.Pool.BurnModel
import Benchmarks.UniswapV3.Pool.PoolEntrySource
import Benchmarks.UniswapV3.Pool.SignedCastWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem burnInitSource (v : UniswapV3PoolImmutables) (a : BurnArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecBlock config (burnFrame v a) evm (burnTransition.body.take 3) (.ok (burnInitFrame v a) evm) := by
  exact poolAmountsInitSource (burnLocals a) (immStore v) evm hwv

theorem evalBurnUnlocked (v : UniswapV3PoolImmutables) (a : BurnArgs) (evm : EVM.State) :
    evalExpr? config (burnInitFrame v a) evm (.storage ⟨"slot0", [.field "unlocked"]⟩) =
      .ok (.bool (!decide (slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩))) := by
  exact evalPoolAmountsUnlocked (burnLocals a) (immStore v) evm
    (by change (burnInitFrame v a).locals.get? "slot0" = none; burn_prefix_get)

theorem burnAssignLock (v : UniswapV3PoolImmutables) (a : BurnArgs) (evm : EVM.State) :
    ExecStmt config (burnInitFrame v a) evm
      (.assign .storage ⟨"slot0", [.field "unlocked"]⟩ (.boolLit false))
      (.ok (burnInitFrame v a) (storeSlot0Unlocked evm false)) := by
  exact poolAmountsAssignLock (burnLocals a) (immStore v) evm
    (by change (burnInitFrame v a).locals.get? "slot0" = none; burn_prefix_get)

theorem burnLockPrefix (v : UniswapV3PoolImmutables) (a : BurnArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecBlock config (burnFrame v a) evm (burnTransition.body.take 5)
      (.ok (burnInitFrame v a) (storeSlot0Unlocked evm false)) := by
  exact poolLockPrefixSource (burnLocals a) (immStore v) evm
    (by change (burnInitFrame v a).locals.get? "slot0" = none; burn_prefix_get) hwv hunlocked

theorem burnRevertsLocked (v : UniswapV3PoolImmutables) (a : BurnArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecTransitionBody config contract evm (burnLocals a) burnTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  exact poolEntryRevertsLocked (burnLocals a) (immStore v) evm (burnTransition.body.drop 5)
    (by change (burnInitFrame v a).locals.get? "slot0" = none; burn_prefix_get) hwv hlocked

theorem burnStatic (v : UniswapV3PoolImmutables) (a : BurnArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (burnLocals a) burnTransition.body .staticViolation (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  exact poolEntryStatic (burnLocals a) (immStore v) evm (burnTransition.body.drop 5)
    (by change (burnInitFrame v a).locals.get? "slot0" = none; burn_prefix_get) hwv hunlocked hperm

theorem evalBurnCastExprs (v : UniswapV3PoolImmutables) (a : BurnArgs) (evm : EVM.State)
    (ha : a.Fits) :
    evalExprs? config (burnInitFrame v a) evm burnCastExprs = .ok [.int (Int.ofNat a.amount.toNat)] := by
  have he : evalExpr? config (burnInitFrame v a) evm (.var "amount") =
      .ok (.int (Int.ofNat a.amount.toNat)) := evalExpr_var_get (by burn_prefix_get)
  have hn := normalizeSint_word_of_lt ⟨256, by decide⟩ a.amount
    (lt_trans ha.2.2 (by decide))
  simp only [burnCastExprs, evalExprs?, evalExpr?, he, castValue?, EvalResult.ofOption,
    bind, EvalResult.bind, pure, hn]

theorem burnCastSource (v : UniswapV3PoolImmutables) (a : BurnArgs) (evm : EVM.State)
    (ha : a.Fits) (hv : safeCast128Valid (Int.ofNat a.amount.toNat)) :
    ExecStmt config (burnInitFrame v a) evm (.internalCall "SafeCast_toInt128" burnCastExprs "__c0")
      (.ok (burnCastFrame v a) evm) :=
  internalCallFunctionReturn (callee := safeCast128Function)
    (calleeSolm := safeCast128ReadyFrame (immStore v) (Int.ofNat a.amount.toNat))
    (value := some [.int (Int.ofNat a.amount.toNat)]) (evalBurnCastExprs v a evm ha)
    safeCast128Lookup (safeCast128Bind _) (safeCast128Returns (immStore v) evm _ hv)

theorem burnCastRevertsCall (v : UniswapV3PoolImmutables) (a : BurnArgs) (evm : EVM.State)
    (ha : a.Fits) (hv : ¬safeCast128Valid (Int.ofNat a.amount.toNat)) :
    ExecStmt config (burnInitFrame v a) evm (.internalCall "SafeCast_toInt128" burnCastExprs "__c0") .reverted :=
  internalCallFunctionRevert (evalBurnCastExprs v a evm ha) safeCast128Lookup (safeCast128Bind _)
    (safeCast128Reverts (immStore v) evm _ hv)

theorem evalBurnModifyExprs (v : UniswapV3PoolImmutables) (a : BurnArgs) (evm : EVM.State) :
    evalExprs? config (burnCastFrame v a) evm burnModifyExprs = .ok [(burnModifyArgs a evm).value] := by
  have hl : evalExpr? config (burnCastFrame v a) evm (.var "tickLower") = .ok (.int a.lower) :=
    evalExpr_var_get (by burn_prefix_get)
  have hu : evalExpr? config (burnCastFrame v a) evm (.var "tickUpper") = .ok (.int a.upper) :=
    evalExpr_var_get (by burn_prefix_get)
  have hc : evalExpr? config (burnCastFrame v a) evm (.var "__c0") = .ok (.int (Int.ofNat a.amount.toNat)) :=
    evalExpr_var_get (by burn_prefix_get)
  simp only [burnModifyExprs, evalExprs?, evalExpr?, evalStructFields?, hl, hu, hc,
    envValue, evalBinaryOp?, castValue?, EvalResult.ofOption, bind, EvalResult.bind, pure,
    burnModifyArgs, ModifyPositionArgs.value]

end Benchmarks.UniswapV3.Pool
