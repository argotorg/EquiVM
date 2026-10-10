import Benchmarks.UniswapV3.Pool.MintModel
import Benchmarks.UniswapV3.Pool.SignedCastWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem mintLockPrefix (v : UniswapV3PoolImmutables) (a : MintArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecBlock config (mintFrame v a) evm (mintTransition.body.take 5)
      (.ok (mintInitFrame v a) (storeSlot0Unlocked evm false)) :=
  poolLockPrefixSource (mintLocals a) (immStore v) evm (by mint_prefix_get) hwv hunlocked

theorem mintRevertsLocked (v : UniswapV3PoolImmutables) (a : MintArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecTransitionBody config contract evm (mintLocals a) mintTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  exact poolEntryRevertsLocked (mintLocals a) (immStore v) evm (mintTransition.body.drop 5)
    (by mint_prefix_get) hwv hlocked

theorem mintStatic (v : UniswapV3PoolImmutables) (a : MintArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (mintLocals a) mintTransition.body .staticViolation (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  exact poolEntryStatic (mintLocals a) (immStore v) evm (mintTransition.body.drop 5)
    (by mint_prefix_get) hwv hunlocked hperm

theorem evalMintAmountPositive (v : UniswapV3PoolImmutables) (a : MintArgs) (evm : EVM.State) :
    evalExpr? config (mintInitFrame v a) evm (.binary .gt (.var "amount") (.intLit 0)) =
      .ok (.bool (decide (0 < a.amount.toNat))) := by
  have he : evalExpr? config (mintInitFrame v a) evm (.var "amount") =
      .ok (.int (Int.ofNat a.amount.toNat)) := evalExpr_var_get (by mint_prefix_get)
  simp [evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind]

theorem mintAmountPrefix (v : UniswapV3PoolImmutables) (a : MintArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hpos : 0 < a.amount.toNat) :
    ExecBlock config (mintFrame v a) evm (mintTransition.body.take 6)
      (.ok (mintInitFrame v a) (storeSlot0Unlocked evm false)) := by
  change ExecBlock config _ _ (mintTransition.body.take 5 ++
    [.require (.binary .gt (.var "amount") (.intLit 0))]) _
  apply execBlock_append_ok (mintLockPrefix v a evm hwv hunlocked)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil
  simpa only [hpos, decide_true] using evalMintAmountPositive v a (storeSlot0Unlocked evm false)

theorem mintRevertsZero (v : UniswapV3PoolImmutables) (a : MintArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hz : a.amount = ⟨0⟩) :
    ExecTransitionBody config contract evm (mintLocals a) mintTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 5 mintTransition.body]
  apply execBlock_append_ok (mintLockPrefix v a evm hwv hunlocked)
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa only [hz, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false] using
    evalMintAmountPositive v a (storeSlot0Unlocked evm false)

theorem evalMintCastExprs (v : UniswapV3PoolImmutables) (a : MintArgs) (evm : EVM.State)
    (ha : a.Fits) :
    evalExprs? config (mintInitFrame v a) evm mintCastExprs = .ok [.int (Int.ofNat a.amount.toNat)] := by
  have he : evalExpr? config (mintInitFrame v a) evm (.var "amount") =
      .ok (.int (Int.ofNat a.amount.toNat)) := evalExpr_var_get (by mint_prefix_get)
  have hn := normalizeSint_word_of_lt ⟨256, by decide⟩ a.amount
    (lt_trans ha.2.2 (by decide))
  simp only [mintCastExprs, evalExprs?, evalExpr?, he, castValue?, EvalResult.ofOption,
    bind, EvalResult.bind, pure, hn]

theorem mintCastSource (v : UniswapV3PoolImmutables) (a : MintArgs) (evm : EVM.State)
    (ha : a.Fits) (hv : safeCast128Valid (Int.ofNat a.amount.toNat)) :
    ExecStmt config (mintInitFrame v a) evm (.internalCall "SafeCast_toInt128" mintCastExprs "__c0")
      (.ok (mintCastFrame v a) evm) :=
  internalCallFunctionReturn (callee := safeCast128Function)
    (calleeSolm := safeCast128ReadyFrame (immStore v) (Int.ofNat a.amount.toNat))
    (value := some [.int (Int.ofNat a.amount.toNat)]) (evalMintCastExprs v a evm ha)
    safeCast128Lookup (safeCast128Bind _) (safeCast128Returns (immStore v) evm _ hv)

theorem mintCastRevertsCall (v : UniswapV3PoolImmutables) (a : MintArgs) (evm : EVM.State)
    (ha : a.Fits) (hv : ¬safeCast128Valid (Int.ofNat a.amount.toNat)) :
    ExecStmt config (mintInitFrame v a) evm (.internalCall "SafeCast_toInt128" mintCastExprs "__c0") .reverted :=
  internalCallFunctionRevert (evalMintCastExprs v a evm ha) safeCast128Lookup (safeCast128Bind _)
    (safeCast128Reverts (immStore v) evm _ hv)

theorem evalMintModifyExprs (v : UniswapV3PoolImmutables) (a : MintArgs) (evm : EVM.State) :
    evalExprs? config (mintCastFrame v a) evm mintModifyExprs = .ok [(mintModifyArgs a).value] := by
  have ho : evalExpr? config (mintCastFrame v a) evm (.var "recipient") = .ok (.address a.recipient) :=
    evalExpr_var_get (by mint_prefix_get)
  have hl : evalExpr? config (mintCastFrame v a) evm (.var "tickLower") = .ok (.int a.lower) :=
    evalExpr_var_get (by mint_prefix_get)
  have hu : evalExpr? config (mintCastFrame v a) evm (.var "tickUpper") = .ok (.int a.upper) :=
    evalExpr_var_get (by mint_prefix_get)
  have hc : evalExpr? config (mintCastFrame v a) evm (.var "__c0") = .ok (.int (Int.ofNat a.amount.toNat)) :=
    evalExpr_var_get (by mint_prefix_get)
  simp only [mintModifyExprs, evalExprs?, evalExpr?, evalStructFields?, ho, hl, hu, hc,
    bind, EvalResult.bind, pure, mintModifyArgs, ModifyPositionArgs.value]

end Benchmarks.UniswapV3.Pool
