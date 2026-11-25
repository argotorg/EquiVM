import Benchmarks.Midnight.TickArithmetic
import Benchmarks.Midnight.TickExpSource

variable {fork : Ethereum.Fork}

/-! Source execution of tick-to-price, including its two rounding divisions. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

abbrev divHalfDownFunction : FunctionDecl := contract.functions[23]!
abbrev tickToPriceFunction : FunctionDecl := contract.functions[4]!

theorem divHalfDownSource {cfg : Config} {frame : Frame} {evm : State} {x d : Int}
    (hx : frame.locals.get? "x" = some (.int x))
    (hd : frame.locals.get? "d" = some (.int d)) (hnz : d ≠ 0) :
    ExecFuncBody fork cfg frame evm divHalfDownFunction.body
      (.returned frame evm (some [.int (divHalfDownValue x d)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?, hx, hd, EvalResult.ofOption, bind, pure, EvalResult.bind,
    evalBinaryOp?, castValue_int, if_neg hnz, show (2 : Int) ≠ 0 by decide, if_false,
    divHalfDownValue]

theorem callDivHalfDown {cfg : Config} {frame : Frame} {evm : State}
    {x d : Int} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract) (he : evalExprs? cfg frame evm args = .ok [.int x, .int d])
    (hnz : d ≠ 0) :
    ExecStmt fork cfg frame evm (.internalCall "TickLib_divHalfDownUnchecked" args name)
      (.ok (resumeAfterInternalCall frame name (some [.int (divHalfDownValue x d)])) evm) := by
  let locals : Store := ((∅ : Store).insert "d" (.int d)).insert "x" (.int x)
  apply internalCallFunctionReturn (callee := divHalfDownFunction) (locals := locals) he
  · rw [hc]; rfl
  · rfl
  · apply divHalfDownSource (store_get_self _ _ _) _ hnz
    simp only [locals, store_get_ne _ _ (show ("x" == "d") = false from rfl), store_get_self]

theorem tickToPriceSource {cfg : Config} {frame : Frame} {evm : State} {tick : UInt256}
    (hc : frame.contract = contract) (ht : frame.locals.get? "tick" = some (.int tick.toNat))
    (hbound : tick.toNat ≤ 6744) :
    ∃ frame', ExecFuncBody fork cfg frame evm tickToPriceFunction.body
      (.returned frame' evm (some [.int (tickPriceWord tick.toNat).toNat])) := by
  have hf := tickArithmeticFacts tick hbound
  have ht' := ht
  simp only [Std.HashMap.get?_eq_getElem?] at ht'
  let x := tickExpArgument tick.toNat
  let denominator := tickUnsigned (1000000000000000000 + wExpValue x)
  let first := divHalfDownValue 1000000000000000000000000000000000000 denominator
  let second := divHalfDownValue first 100000000000
  let f1 := resumeAfterInternalCall frame "__c0" (some [.int (wExpValue x)])
  let f2 := resumeAfterInternalCall f1 "__c1" (some [.int first])
  let f3 := resumeAfterInternalCall f2 "__c2" (some [.int second])
  have hcall1 : ExecStmt fork cfg frame evm tickToPriceFunction.body[1]! (.ok f1 evm) := by
    apply callWExp hc
    · simp [evalExprs?, evalExpr?, ht', EvalResult.ofOption, bind, pure, EvalResult.bind,
        evalBinaryOp?, castValue_int, x, tickExpArgument]
    · exact fun h ↦ (hf.1 h).2.2.2.1
    · exact fun h ↦ (hf.1 h).2.2.2.2
  have hcall2 : ExecStmt fork cfg f1 evm tickToPriceFunction.body[2]! (.ok f2 evm) := by
    apply callDivHalfDown (frame := f1) hc
    · simp only [evalExprs?, evalExpr?, f1, resumeAfterInternalCall, collapseReturns,
        store_get_self, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?,
        castValue_int]
      rfl
    · exact hf.2.2.2.2.1
  have hcall3 : ExecStmt fork cfg f2 evm tickToPriceFunction.body[3]! (.ok f3 evm) := by
    apply callDivHalfDown (frame := f2) hc
    · simp only [evalExprs?, evalExpr?, f2, resumeAfterInternalCall, collapseReturns,
        store_get_self, EvalResult.ofOption, bind, pure, EvalResult.bind]
    · decide
  refine ⟨f3, ExecFuncBody.execBlockRet (ExecBlock.consNormal (ExecStmt.requireTrue ?_)
    (ExecBlock.consNormal hcall1 (ExecBlock.consNormal hcall2
      (ExecBlock.consNormal hcall3 (ExecBlock.consReturn (ExecStmt.return ?_))))))⟩
  · have hh : (tick.toNat : Int) ≤ 6744 := by omega
    simp only [evalExpr?, ht, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?,
      decide_eq_true hh]
  · simp only [evalExprs?, evalExpr?, f3, resumeAfterInternalCall, collapseReturns,
      store_get_self, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?,
      castValue_int]
    exact congrArg (fun value : Int ↦ EvalResult.ok [Value.int value]) hf.2.2.2.2.2

theorem tickToPriceRevert {cfg : Config} {frame : Frame} {evm : State} {tick : UInt256}
    (ht : frame.locals.get? "tick" = some (.int tick.toNat)) (hbound : 6744 < tick.toNat) :
    ExecFuncBody fork cfg frame evm tickToPriceFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  have hh : ¬ (tick.toNat : Int) ≤ 6744 := by omega
  simp only [evalExpr?, ht, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?,
    decide_eq_false hh]

theorem callTickToPrice {cfg : Config} {frame : Frame} {evm : State}
    {tick : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (he : evalExprs? cfg frame evm args = .ok [.int tick.toNat]) (hbound : tick.toNat ≤ 6744) :
    ExecStmt fork cfg frame evm (.internalCall "TickLib_tickToPrice" args name)
      (.ok (resumeAfterInternalCall frame name
        (some [.int (tickPriceWord tick.toNat).toNat])) evm) := by
  obtain ⟨frame', hbody⟩ := tickToPriceSource (cfg := cfg) (evm := evm)
    (frame := { frame with locals := (∅ : Store).insert "tick" (.int tick.toNat) })
    hc (store_get_self _ _ _) hbound
  exact internalCallFunctionReturn he (by rw [hc]; rfl) rfl hbody

theorem callTickToPriceRevert {cfg : Config} {frame : Frame} {evm : State}
    {tick : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (he : evalExprs? cfg frame evm args = .ok [.int tick.toNat]) (hbound : 6744 < tick.toNat) :
    ExecStmt fork cfg frame evm (.internalCall "TickLib_tickToPrice" args name) .reverted := by
  apply internalCallFunctionRevert (callee := tickToPriceFunction)
    (locals := (∅ : Store).insert "tick" (.int tick.toNat)) he
  · rw [hc]; rfl
  · rfl
  · exact tickToPriceRevert (store_get_self _ _ _) hbound

end Benchmarks.Midnight
