import Benchmarks.UniswapV3.Pool.FlashRepaymentTrace
import Benchmarks.UniswapV3.Pool.SwapBalanceBefore
import Benchmarks.UniswapV3.Pool.SwapBalanceAfter

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapRepayName (second : Bool) : Ident := if second then "__c24" else "__c29"

def swapRepayTailStmts (second : Bool) : List Stmt :=
  [.internalCall "LowGasSafeMath_add"
      [.var (swapBalanceBeforeName second), .cast (.var (poolAmountName (!second))) (.elem (.int
        (.uint ⟨256, by decide⟩)))] (swapRepayName second),
    .require (.binary .le (.var (swapRepayName second)) (.var (swapBalanceAfterName second)))]

theorem swapRepayTailStmts_eq (second : Bool) :
    swapRepayTailStmts second = (swapPaymentBody second).drop 6 := by
  cases second <;> rfl

def swapRepayFrame (v : UniswapV3PoolImmutables) (locals : Store)
    (second : Bool) (before : UInt256) (fee : Int) : Frame :=
  {contract := contract, immutables := immStore v,
    locals := locals.insert (swapRepayName second) (.int (Int.ofNat (before + EVM.wordOfInt
      fee).toNat))}

theorem evalSwapRepayArgs (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (before : UInt256) (fee : Int)
    (hb : locals.get? (swapBalanceBeforeName second) = some (.int (Int.ofNat before.toNat)))
    (hf : locals.get? (poolAmountName (!second)) = some (.int fee)) :
    evalExprs? config {contract := contract, locals := locals, immutables := immStore v} evm
      [.var (swapBalanceBeforeName second), .cast (.var (poolAmountName (!second))) (.elem (.int
        (.uint ⟨256, by decide⟩)))] =
      .ok [.int (Int.ofNat before.toNat), .int (Int.ofNat (EVM.wordOfInt fee).toNat)] := by
  simp only [evalExprs?, evalExpr?, hb, hf, castValue?, normalizeUInt256_int, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

theorem swapRepayAddReturns (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (before : UInt256) (fee : Int)
    (hb : locals.get? (swapBalanceBeforeName second) = some (.int (Int.ofNat before.toNat)))
    (hf : locals.get? (poolAmountName (!second)) = some (.int fee))
    (hv : before.toNat ≤ (before + EVM.wordOfInt fee).toNat) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (swapRepayTailStmts second)[0]! (.ok (swapRepayFrame v locals second before fee) evm) := by
  exact internalCallFunctionReturn (callee := safeAddFunction) (locals := safeAddLocals before
    (EVM.wordOfInt fee))
    (calleeSolm := safeAddResultFrame (immStore v) before (EVM.wordOfInt fee))
    (value := some [.int (Int.ofNat (before + EVM.wordOfInt fee).toNat)])
    (evalSwapRepayArgs v locals evm second before fee hb hf) safeAddLookup
    (safeAddBind before (EVM.wordOfInt fee)) (safeAddReturns (immStore v) evm before (EVM.wordOfInt
      fee) hv)

theorem evalSwapRepayGuard (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (before after : UInt256) (fee : Int)
    (ha : locals.get? (swapBalanceAfterName second) = some (.int (Int.ofNat after.toNat))) :
    evalExpr? config (swapRepayFrame v locals second before fee) evm
      (.binary .le (.var (swapRepayName second)) (.var (swapBalanceAfterName second))) =
      .ok (.bool (decide ((before + EVM.wordOfInt fee).toNat ≤ after.toNat))) := by
  have hne : swapRepayName second ≠ swapBalanceAfterName second := by
    cases second <;> decide
  change locals[swapBalanceAfterName second]? = _ at ha
  simp [evalExpr?, swapRepayFrame, Std.HashMap.getElem?_insert, hne, ha,
    EvalResult.ofOption, evalBinaryOp?, bind, EvalResult.bind]

theorem swapRepayReturns (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (before after : UInt256) (fee : Int)
    (hb : locals.get? (swapBalanceBeforeName second) = some (.int (Int.ofNat before.toNat)))
    (hf : locals.get? (poolAmountName (!second)) = some (.int fee))
    (ha : locals.get? (swapBalanceAfterName second) = some (.int (Int.ofNat after.toNat)))
    (hv : flashRepayValid before (EVM.wordOfInt fee) after) :
    ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
      (swapRepayTailStmts second) (.ok (swapRepayFrame v locals second before fee) evm) := by
  refine ExecBlock.consNormal (swapRepayAddReturns v locals evm second before fee hb hf hv.1)
    (ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil)
  simpa only [hv.2, decide_true] using evalSwapRepayGuard v locals evm second before after fee ha

theorem swapRepayReverts (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (before after : UInt256) (fee : Int)
    (hb : locals.get? (swapBalanceBeforeName second) = some (.int (Int.ofNat before.toNat)))
    (hf : locals.get? (poolAmountName (!second)) = some (.int fee))
    (ha : locals.get? (swapBalanceAfterName second) = some (.int (Int.ofNat after.toNat)))
    (hv : ¬ flashRepayValid before (EVM.wordOfInt fee) after) :
    ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
      (swapRepayTailStmts second) .reverted := by
  by_cases hadd : before.toNat ≤ (before + EVM.wordOfInt fee).toNat
  · refine ExecBlock.consNormal (swapRepayAddReturns v locals evm second before fee hb hf hadd)
      (ExecBlock.consRevert (ExecStmt.requireFalse ?_))
    have hfail : ¬ (before + EVM.wordOfInt fee).toNat ≤ after.toNat := fun h ↦ hv ⟨hadd, h⟩
    simpa only [hfail, decide_false] using evalSwapRepayGuard v locals evm second before after fee
      ha
  · apply ExecBlock.consRevert
    exact internalCallFunctionRevert (callee := safeAddFunction)
      (locals := safeAddLocals before (EVM.wordOfInt fee))
      (evalSwapRepayArgs v locals evm second before fee hb hf) safeAddLookup
      (safeAddBind before (EVM.wordOfInt fee)) (safeAddReverts (immStore v) evm before
        (EVM.wordOfInt fee) hadd)


end Benchmarks.UniswapV3.Pool
