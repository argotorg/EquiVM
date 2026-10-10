import Benchmarks.UniswapV3.Pool.FlashRepaymentTrace
import Benchmarks.UniswapV3.Pool.FlashBalances
import Benchmarks.UniswapV3.Pool.FlashFeesSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def flashRepayName (second : Bool) : Ident := if second then "__c11" else "__c10"

def flashRepayStmts (second : Bool) : List Stmt :=
  [.internalCall "LowGasSafeMath_add"
      [.var (flashBalanceName false second), .var (flashFeeName second)] (flashRepayName second),
    .require (.binary .le (.var (flashRepayName second)) (.var (flashBalanceName true second)))]

def flashRepayFrame (v : UniswapV3PoolImmutables) (locals : Store)
    (second : Bool) (before fee : UInt256) : Frame :=
  {contract := contract, immutables := immStore v,
    locals := locals.insert (flashRepayName second) (.int (Int.ofNat (before + fee).toNat))}

theorem evalFlashRepayArgs (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (before fee : UInt256)
    (hb : locals.get? (flashBalanceName false second) = some (.int (Int.ofNat before.toNat)))
    (hf : locals.get? (flashFeeName second) = some (.int (Int.ofNat fee.toNat))) :
    evalExprs? config {contract := contract, locals := locals, immutables := immStore v} evm
      [.var (flashBalanceName false second), .var (flashFeeName second)] =
      .ok [.int (Int.ofNat before.toNat), .int (Int.ofNat fee.toNat)] := by
  simp only [evalExprs?, evalExpr?, hb, hf, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem flashRepayAddReturns (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (before fee : UInt256)
    (hb : locals.get? (flashBalanceName false second) = some (.int (Int.ofNat before.toNat)))
    (hf : locals.get? (flashFeeName second) = some (.int (Int.ofNat fee.toNat)))
    (hv : before.toNat ≤ (before + fee).toNat) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (flashRepayStmts second)[0]! (.ok (flashRepayFrame v locals second before fee) evm) := by
  exact internalCallFunctionReturn (callee := safeAddFunction) (locals := safeAddLocals before fee)
    (calleeSolm := safeAddResultFrame (immStore v) before fee)
    (value := some [.int (Int.ofNat (before + fee).toNat)])
    (evalFlashRepayArgs v locals evm second before fee hb hf) safeAddLookup
    (safeAddBind before fee) (safeAddReturns (immStore v) evm before fee hv)

theorem evalFlashRepayGuard (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (before fee after : UInt256)
    (ha : locals.get? (flashBalanceName true second) = some (.int (Int.ofNat after.toNat))) :
    evalExpr? config (flashRepayFrame v locals second before fee) evm
      (.binary .le (.var (flashRepayName second)) (.var (flashBalanceName true second))) =
      .ok (.bool (decide ((before + fee).toNat ≤ after.toNat))) := by
  have hne : flashRepayName second ≠ flashBalanceName true second := by
    cases second <;> decide
  change locals[flashBalanceName true second]? = _ at ha
  simp [evalExpr?, flashRepayFrame, Std.HashMap.getElem?_insert, hne, ha,
    EvalResult.ofOption, evalBinaryOp?, bind, EvalResult.bind]

theorem flashRepayReturns (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (before fee after : UInt256)
    (hb : locals.get? (flashBalanceName false second) = some (.int (Int.ofNat before.toNat)))
    (hf : locals.get? (flashFeeName second) = some (.int (Int.ofNat fee.toNat)))
    (ha : locals.get? (flashBalanceName true second) = some (.int (Int.ofNat after.toNat)))
    (hv : flashRepayValid before fee after) :
    ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
      (flashRepayStmts second) (.ok (flashRepayFrame v locals second before fee) evm) := by
  refine ExecBlock.consNormal (flashRepayAddReturns v locals evm second before fee hb hf hv.1)
    (ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil)
  simpa only [hv.2, decide_true] using evalFlashRepayGuard v locals evm second before fee after ha

theorem flashRepayReverts (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (before fee after : UInt256)
    (hb : locals.get? (flashBalanceName false second) = some (.int (Int.ofNat before.toNat)))
    (hf : locals.get? (flashFeeName second) = some (.int (Int.ofNat fee.toNat)))
    (ha : locals.get? (flashBalanceName true second) = some (.int (Int.ofNat after.toNat)))
    (hv : ¬ flashRepayValid before fee after) :
    ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
      (flashRepayStmts second) .reverted := by
  by_cases hadd : before.toNat ≤ (before + fee).toNat
  · refine ExecBlock.consNormal (flashRepayAddReturns v locals evm second before fee hb hf hadd)
      (ExecBlock.consRevert (ExecStmt.requireFalse ?_))
    have hfail : ¬ (before + fee).toNat ≤ after.toNat := fun h ↦ hv ⟨hadd, h⟩
    simpa only [hfail, decide_false] using evalFlashRepayGuard v locals evm second before fee after ha
  · apply ExecBlock.consRevert
    exact internalCallFunctionRevert (callee := safeAddFunction)
      (locals := safeAddLocals before fee)
      (evalFlashRepayArgs v locals evm second before fee hb hf) safeAddLookup
      (safeAddBind before fee) (safeAddReverts (immStore v) evm before fee hadd)

structure FlashRepayValues (locals : Store) (before0 before1 fee0 fee1 after0 after1 : UInt256) :
    Prop where
  before0 : locals.get? "balance0Before" = some (.int (Int.ofNat before0.toNat))
  before1 : locals.get? "balance1Before" = some (.int (Int.ofNat before1.toNat))
  fee0 : locals.get? "fee0" = some (.int (Int.ofNat fee0.toNat))
  fee1 : locals.get? "fee1" = some (.int (Int.ofNat fee1.toNat))
  after0 : locals.get? "balance0After" = some (.int (Int.ofNat after0.toNat))
  after1 : locals.get? "balance1After" = some (.int (Int.ofNat after1.toNat))

def flashRepaidFrame (v : UniswapV3PoolImmutables) (locals : Store)
    (before0 before1 fee0 fee1 : UInt256) : Frame :=
  flashRepayFrame v (flashRepayFrame v locals false before0 fee0).locals true before1 fee1

theorem flashRepaymentReturns (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (before0 before1 fee0 fee1 after0 after1 : UInt256)
    (hget : FlashRepayValues locals before0 before1 fee0 fee1 after0 after1)
    (hv : flashRepayValid before0 fee0 after0 ∧ flashRepayValid before1 fee1 after1) :
    ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
      ((flashTransition.body.drop 17).take 4)
      (.ok (flashRepaidFrame v locals before0 before1 fee0 fee1) evm) := by
  change ExecBlock _ _ _ (flashRepayStmts false ++ flashRepayStmts true) _
  apply execBlock_append_ok
    (flashRepayReturns v locals evm false before0 fee0 after0 hget.before0 hget.fee0 hget.after0 hv.1)
  apply flashRepayReturns v _ evm true before1 fee1 after1 _ _ _ hv.2
  · simpa [flashRepayFrame, flashRepayName, flashBalanceName,
      Std.HashMap.getElem?_insert] using hget.before1
  · simpa [flashRepayFrame, flashRepayName, flashFeeName,
      Std.HashMap.getElem?_insert] using hget.fee1
  · simpa [flashRepayFrame, flashRepayName, flashBalanceName,
      Std.HashMap.getElem?_insert] using hget.after1

theorem flashRepaymentReverts (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (before0 before1 fee0 fee1 after0 after1 : UInt256)
    (hget : FlashRepayValues locals before0 before1 fee0 fee1 after0 after1)
    (hv : ¬ (flashRepayValid before0 fee0 after0 ∧ flashRepayValid before1 fee1 after1)) :
    ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
      ((flashTransition.body.drop 17).take 4) .reverted := by
  change ExecBlock _ _ _ (flashRepayStmts false ++ flashRepayStmts true) _
  by_cases hv0 : flashRepayValid before0 fee0 after0
  · apply execBlock_append_ok
      (flashRepayReturns v locals evm false before0 fee0 after0 hget.before0 hget.fee0 hget.after0 hv0)
    apply flashRepayReverts v _ evm true before1 fee1 after1 _ _ _ (fun h ↦ hv ⟨hv0, h⟩)
    · simpa [flashRepayFrame, flashRepayName, flashBalanceName,
        Std.HashMap.getElem?_insert] using hget.before1
    · simpa [flashRepayFrame, flashRepayName, flashFeeName,
        Std.HashMap.getElem?_insert] using hget.fee1
    · simpa [flashRepayFrame, flashRepayName, flashBalanceName,
        Std.HashMap.getElem?_insert] using hget.after1
  · exact execBlock_append_term
      (flashRepayReverts v locals evm false before0 fee0 after0
        hget.before0 hget.fee0 hget.after0 hv0) (by intro _ _ h; cases h)

def flashPaidFrame (v : UniswapV3PoolImmutables) (locals : Store)
    (before0 before1 after0 after1 : UInt256) : Frame :=
  {contract := contract, immutables := immStore v,
    locals := (locals.insert "paid0" (.int (Int.ofNat (UInt256.sub after0 before0).toNat))).insert
      "paid1" (.int (Int.ofNat (UInt256.sub after1 before1).toNat))}

theorem flashPaidSource (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (before0 before1 after0 after1 : UInt256)
    (hb0 : locals.get? "balance0Before" = some (.int (Int.ofNat before0.toNat)))
    (hb1 : locals.get? "balance1Before" = some (.int (Int.ofNat before1.toNat)))
    (ha0 : locals.get? "balance0After" = some (.int (Int.ofNat after0.toNat)))
    (ha1 : locals.get? "balance1After" = some (.int (Int.ofNat after1.toNat))) :
    ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
      ((flashTransition.body.drop 21).take 2)
      (.ok (flashPaidFrame v locals before0 before1 after0 after1) evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (evalExpr_word_sub (evalExpr_var_get ha0) (evalExpr_var_get hb0))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_word_sub ?_ ?_)) ExecBlock.nil
  · exact evalExpr_var_get (by simpa [Std.HashMap.getElem?_insert] using ha1)
  · exact evalExpr_var_get (by simpa [Std.HashMap.getElem?_insert] using hb1)

end Benchmarks.UniswapV3.Pool
