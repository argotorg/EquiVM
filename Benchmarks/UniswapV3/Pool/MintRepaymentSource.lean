import Benchmarks.UniswapV3.Pool.FlashRepaymentTrace
import Benchmarks.UniswapV3.Pool.MintCallValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def mintAfterBalanceTemp (second : Bool) : Ident := if second then "__c8" else "__c6"

def mintRepayName (second : Bool) : Ident := if second then "__c7" else "__c5"

def mintRepayTailStmts (second : Bool) : List Stmt :=
  [.internalCall "LowGasSafeMath_add"
      [.var (mintBeforeBalanceName second), .var (poolAmountName second)] (mintRepayName second),
    .require (.binary .le (.var (mintRepayName second)) (.var (mintAfterBalanceTemp second)))]

def mintRepayFrame (v : UniswapV3PoolImmutables) (locals : Store)
    (second : Bool) (before fee : UInt256) : Frame :=
  {contract := contract, immutables := immStore v,
    locals := locals.insert (mintRepayName second) (.int (Int.ofNat (before + fee).toNat))}

theorem evalMintRepayArgs (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (before fee : UInt256)
    (hb : locals.get? (mintBeforeBalanceName second) = some (.int (Int.ofNat before.toNat)))
    (hf : locals.get? (poolAmountName second) = some (.int (Int.ofNat fee.toNat))) :
    evalExprs? config {contract := contract, locals := locals, immutables := immStore v} evm
      [.var (mintBeforeBalanceName second), .var (poolAmountName second)] =
      .ok [.int (Int.ofNat before.toNat), .int (Int.ofNat fee.toNat)] := by
  simp only [evalExprs?, evalExpr?, hb, hf, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem mintRepayAddReturns (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (before fee : UInt256)
    (hb : locals.get? (mintBeforeBalanceName second) = some (.int (Int.ofNat before.toNat)))
    (hf : locals.get? (poolAmountName second) = some (.int (Int.ofNat fee.toNat)))
    (hv : before.toNat ≤ (before + fee).toNat) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (mintRepayTailStmts second)[0]! (.ok (mintRepayFrame v locals second before fee) evm) := by
  exact internalCallFunctionReturn (callee := safeAddFunction) (locals := safeAddLocals before fee)
    (calleeSolm := safeAddResultFrame (immStore v) before fee)
    (value := some [.int (Int.ofNat (before + fee).toNat)])
    (evalMintRepayArgs v locals evm second before fee hb hf) safeAddLookup
    (safeAddBind before fee) (safeAddReturns (immStore v) evm before fee hv)

theorem evalMintRepayGuard (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (before fee after : UInt256)
    (ha : locals.get? (mintAfterBalanceTemp second) = some (.int (Int.ofNat after.toNat))) :
    evalExpr? config (mintRepayFrame v locals second before fee) evm
      (.binary .le (.var (mintRepayName second)) (.var (mintAfterBalanceTemp second))) =
      .ok (.bool (decide ((before + fee).toNat ≤ after.toNat))) := by
  have hne : mintRepayName second ≠ mintAfterBalanceTemp second := by
    cases second <;> decide
  change locals[mintAfterBalanceTemp second]? = _ at ha
  simp [evalExpr?, mintRepayFrame, Std.HashMap.getElem?_insert, hne, ha,
    EvalResult.ofOption, evalBinaryOp?, bind, EvalResult.bind]

theorem mintRepayReturns (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (before fee after : UInt256)
    (hb : locals.get? (mintBeforeBalanceName second) = some (.int (Int.ofNat before.toNat)))
    (hf : locals.get? (poolAmountName second) = some (.int (Int.ofNat fee.toNat)))
    (ha : locals.get? (mintAfterBalanceTemp second) = some (.int (Int.ofNat after.toNat)))
    (hv : flashRepayValid before fee after) :
    ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
      (mintRepayTailStmts second) (.ok (mintRepayFrame v locals second before fee) evm) := by
  refine ExecBlock.consNormal (mintRepayAddReturns v locals evm second before fee hb hf hv.1)
    (ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil)
  simpa only [hv.2, decide_true] using evalMintRepayGuard v locals evm second before fee after ha

theorem mintRepayReverts (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (before fee after : UInt256)
    (hb : locals.get? (mintBeforeBalanceName second) = some (.int (Int.ofNat before.toNat)))
    (hf : locals.get? (poolAmountName second) = some (.int (Int.ofNat fee.toNat)))
    (ha : locals.get? (mintAfterBalanceTemp second) = some (.int (Int.ofNat after.toNat)))
    (hv : ¬ flashRepayValid before fee after) :
    ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
      (mintRepayTailStmts second) .reverted := by
  by_cases hadd : before.toNat ≤ (before + fee).toNat
  · refine ExecBlock.consNormal (mintRepayAddReturns v locals evm second before fee hb hf hadd)
      (ExecBlock.consRevert (ExecStmt.requireFalse ?_))
    have hfail : ¬ (before + fee).toNat ≤ after.toNat := fun h ↦ hv ⟨hadd, h⟩
    simpa only [hfail, decide_false] using evalMintRepayGuard v locals evm second before fee after ha
  · apply ExecBlock.consRevert
    exact internalCallFunctionRevert (callee := safeAddFunction)
      (locals := safeAddLocals before fee)
      (evalMintRepayArgs v locals evm second before fee hb hf) safeAddLookup
      (safeAddBind before fee) (safeAddReverts (immStore v) evm before fee hadd)

def mintRepayStmt (second : Bool) : Stmt :=
  .ite (.binary .gt (.var (poolAmountName second)) (.intLit 0))
    (.internalCall (if second then "balance1" else "balance0") [] (mintAfterBalanceTemp second) ::
      mintRepayTailStmts second) []

theorem mintRepayStmt_eq (second : Bool) :
    mintRepayStmt second = mintTransition.body[if second then 20 else 19]! := by
  cases second <;> rfl

theorem mintRepaySkip (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (ha : locals.get? (poolAmountName second) = some (.int 0)) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (mintRepayStmt second)
      (.ok {contract := contract, locals := locals, immutables := immStore v} evm) := by
  refine ExecStmt.iteFalse ?_ ExecBlock.nil
  simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false] using
    evalFlashTransferGuard v locals evm second ⟨0⟩ ha

end Benchmarks.UniswapV3.Pool
