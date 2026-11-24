import Benchmarks.EAS.EAS.RefundResult
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

abbrev refundFunction : FunctionDecl := contract.functions[30]!
def refundBalance (evm : EVM.State) : UInt256 :=
  (evm.lookupAccount evm.executionEnv.codeOwner).option (EVM.Word.ofNat 0) (·.balance)
def refundNonzeroExpr : Expr := .binary .gt (.var "remainingValue") (.intLit 0)
def refundBalanceExpr : Expr := .binary .ge (.env .selfbalance) (.var "remainingValue")
def refundCallPrefix : Body := [
  .require refundBalanceExpr,
  .letDecl "empty" (some .bytes) (.newBytes (.intLit 0)),
  .lowLevelCall (.env .caller) (.var "remainingValue") (.var "empty") "ok" "result"]
def refundReturn : Body := [.return [.tupleLit [], .var "$EAS.freeMemory"]]

theorem refund_body : refundFunction.body =
    [.ite refundNonzeroExpr (refundCallPrefix ++ refundResultTail) []] ++ refundReturn := by native_decide

theorem refundNonzero_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {value : UInt256}
    (hv : frame.locals.get? "remainingValue" = some (.int (Int.ofNat value.toNat))) :
    evalExpr? cfg frame evm refundNonzeroExpr = .ok (.bool (decide (value ≠ ⟨0⟩))) := by
  have hn : (Int.ofNat value.toNat > (0 : Int)) = (value ≠ ⟨0⟩) := by
    apply propext
    simp only [Int.ofNat_eq_natCast]
    constructor
    · intro h he; rw [he] at h; exact (by change (0 : Int) < 0 at h; omega : False)
    · intro h
      have hn : value.toNat ≠ 0 := fun hz => h (uint256_toNat_eq_zero hz)
      omega
  simp only [refundNonzeroExpr, evalExpr?, hv, EvalResult.ofOption, pure, bind, EvalResult.bind, evalBinaryOp?, hn]

theorem refundBalance_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {value : UInt256}
    (hv : frame.locals.get? "remainingValue" = some (.int (Int.ofNat value.toNat))) :
    evalExpr? cfg frame evm refundBalanceExpr = .ok (.bool (decide (value.toNat ≤ (refundBalance evm).toNat))) := by
  have hn : (Int.ofNat (refundBalance evm).toNat ≥ Int.ofNat value.toNat) = (value.toNat ≤ (refundBalance evm).toNat) := by
    apply propext
    simp only [Int.ofNat_eq_natCast, Int.ofNat_le]
  simp only [refundBalanceExpr, evalExpr?, hv, envValue, EvalResult.ofOption, pure, bind, EvalResult.bind, evalBinaryOp?]
  change EvalResult.ok (Value.bool (decide (Int.ofNat (refundBalance evm).toNat ≥ Int.ofNat value.toNat))) = _
  simp only [hn]

theorem refundSource_zero {cfg : Config} {locals imms : Store} {evm : EVM.State} {heap : Nat}
    (hv : locals.get? "remainingValue" = some (.int 0))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := imms} evm refundFunction.body
      (.returned {contract := contract, locals := locals, immutables := imms} evm (some [.tuple [], .int (Int.ofNat heap)])) := by
  rw [refund_body]
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (ExecStmt.iteFalse (by
    simpa only [ne_self_iff_false, decide_false] using refundNonzero_eval (value := ⟨0⟩) (cfg := cfg)
      (frame := {contract := contract, locals := locals, immutables := imms}) (evm := evm) hv) ExecBlock.nil)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, evalExprList?, hh, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem refundSource_insufficient {cfg : Config} {locals imms : Store} {evm : EVM.State} {value : UInt256}
    (hv : locals.get? "remainingValue" = some (.int (Int.ofNat value.toNat))) (hn : value ≠ ⟨0⟩)
    (hb : ¬ value.toNat ≤ (refundBalance evm).toNat) :
    ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := imms} evm refundFunction.body .reverted := by
  rw [refund_body]
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert (ExecStmt.iteTrue ?_ ?_)
  · simpa only [decide_eq_true hn] using refundNonzero_eval (cfg := cfg)
      (frame := {contract := contract, locals := locals, immutables := imms}) (evm := evm) hv
  · apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
    simpa only [decide_eq_false hb] using refundBalance_eval (cfg := cfg)
      (frame := {contract := contract, locals := locals, immutables := imms}) (evm := evm) hv

def refundPostLocals (locals : Store) (success : Bool) (out : ByteArray) : Store :=
  ((locals.insert "empty" (.bytes ByteArray.empty)).insert "ok" (.bool success)).insert "result" (.bytes out)

theorem refundPostLocals_facts (locals : Store) (success : Bool) (out : ByteArray) :
    (refundPostLocals locals success out).get? "ok" = some (.bool success) ∧
    (refundPostLocals locals success out).get? "result" = some (.bytes out) ∧
    (refundPostLocals locals success out).get? "$EAS.freeMemory" = locals.get? "$EAS.freeMemory" := by
  simp (disch := decide) only [refundPostLocals, store_get_ne, store_get_self, and_self]

theorem refundCallPrefix_exec {cfg : Config} {locals imms : Store} {evm evm' : EVM.State}
    {value : UInt256} {success : Bool} {out : ByteArray}
    (hv : locals.get? "remainingValue" = some (.int (Int.ofNat value.toNat)))
    (hb : value.toNat ≤ (refundBalance evm).toNat)
    (hc : callViaEVM fork evm evm.executionEnv.source (Int.ofNat value.toNat) ByteArray.empty (success,evm',out))
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm refundCallPrefix
      (.ok {contract := contract, locals := refundPostLocals locals success out, immutables := imms} evm') := by
  apply ExecBlock.consNormal (ExecStmt.requireTrue (by
    simpa only [decide_eq_true hb] using refundBalance_eval (cfg := cfg)
      (frame := {contract := contract, locals := locals, immutables := imms}) (evm := evm) hv))
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .bytes ByteArray.empty) (by simp only [evalExpr?, pure]; rfl))
  apply ExecBlock.consNormal (lowLevelCallSource (fork := fork) (hperm := Or.inr hperm) (by simp only [evalExpr?, envValue, pure]) ?_
    (by simp only [evalExpr?, store_get_self, EvalResult.ofOption]) hc) ExecBlock.nil
  simp only [evalExpr?, store_get_ne _ _ (by decide : ("empty" == "remainingValue") = false), hv, EvalResult.ofOption]

theorem refundSource_call {cfg : Config} {locals imms : Store} {evm evm' : EVM.State}
    {value : UInt256} {success : Bool} {out : ByteArray} {heap : Nat}
    (hv : locals.get? "remainingValue" = some (.int (Int.ofNat value.toNat)))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) (hn : value ≠ ⟨0⟩)
    (hb : value.toNat ≤ (refundBalance evm).toNat)
    (hc : callViaEVM fork evm evm.executionEnv.source (Int.ofNat value.toNat) ByteArray.empty (success,evm',out))
    (hperm : evm.executionEnv.perm = true) :
    if refundResultValid heap success out then
      ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := imms} evm refundFunction.body
        (.returned {contract := contract, locals := refundAllocationLocals (refundPostLocals locals success out) heap out.size, immutables := imms} evm' (some [.tuple [], .int (Int.ofNat (refundNext heap out.size))]))
    else ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := imms} evm refundFunction.body .reverted := by
  have hp := refundCallPrefix_exec (hperm := by assumption) (cfg := cfg) (imms := imms) hv hb hc
  have hf := refundPostLocals_facts locals success out
  have hh' := hf.2.2.trans hh
  have hr := refundResultSource (fork := fork) (cfg := cfg) (imms := imms) (evm := evm') hf.2.1 hf.1 hh'
  have he : evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm refundNonzeroExpr = .ok (.bool true) := by
    simpa only [decide_eq_true hn] using refundNonzero_eval (cfg := cfg)
      (frame := {contract := contract, locals := locals, immutables := imms}) (evm := evm) hv
  by_cases hg : refundResultValid heap success out
  · rw [if_pos hg, refund_body]
    rw [if_pos hg] at hr
    apply ExecFuncBody.execBlockRet
    apply ExecBlock.consNormal (ExecStmt.iteTrue he (execBlock_append hp hr))
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, evalExpr?, evalExprList?, refundAllocationLocals_heap hh', EvalResult.ofOption, EvalResult.bind, bind, pure]
  · rw [if_neg hg, refund_body]
    rw [if_neg hg] at hr
    exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.iteTrue he (execBlock_append hp hr)))


def refundArgs (value : UInt256) (heap : Nat) : Store :=
  (∅ : Store) |>.insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "remainingValue" (.int (Int.ofNat value.toNat))

theorem refundArgs_heap (value : UInt256) (heap : Nat) :
    (refundArgs value heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := by
  simp only [refundArgs, store_get_ne _ _ (by decide : ("remainingValue" == "$EAS.freeMemory") = false), store_get_self]

theorem refund_lookup : lookupCallable? contract "_refund" = some refundFunction.toCallable := by rfl

theorem refund_bind (value : UInt256) (heap : Nat) :
    bindParams? refundFunction.params [.int (Int.ofNat value.toNat), .int (Int.ofNat heap)] = some (refundArgs value heap) := by rfl

theorem refundCall_zero {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {heap : Nat} {args : List Expr} {retVar : Ident}
    (he : evalExprs? cfg {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [.int 0, .int (Int.ofNat heap)]) :
    ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm (.internalCall "_refund" args retVar)
      (.ok {contract := contract, locals := locals.insert retVar (.tuple [.tuple [], .int (Int.ofNat heap)]), immutables := imms} evm) := by
  exact internalCallFunctionReturn he refund_lookup (refund_bind ⟨0⟩ heap)
    (refundSource_zero (store_get_self _ _ _) (refundArgs_heap ⟨0⟩ heap))

theorem refundCall_insufficient {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {value : UInt256} {heap : Nat} {args : List Expr} {retVar : Ident}
    (he : evalExprs? cfg {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [.int (Int.ofNat value.toNat), .int (Int.ofNat heap)])
    (hn : value ≠ ⟨0⟩) (hb : ¬ value.toNat ≤ (refundBalance evm).toNat) :
    ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm (.internalCall "_refund" args retVar) .reverted := by
  exact internalCallFunctionRevert he refund_lookup (refund_bind value heap)
    (refundSource_insufficient (store_get_self _ _ _) hn hb)

theorem refundCall {cfg : Config} {locals imms : Store} {evm evm' : EVM.State}
    {value : UInt256} {success : Bool} {out : ByteArray} {heap : Nat} {args : List Expr} {retVar : Ident}
    (he : evalExprs? cfg {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [.int (Int.ofNat value.toNat), .int (Int.ofNat heap)])
    (hn : value ≠ ⟨0⟩) (hb : value.toNat ≤ (refundBalance evm).toNat)
    (hc : callViaEVM fork evm evm.executionEnv.source (Int.ofNat value.toNat) ByteArray.empty (success,evm',out))
    (hperm : evm.executionEnv.perm = true) :
    if refundResultValid heap success out then
      ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm (.internalCall "_refund" args retVar)
        (.ok {contract := contract, locals := locals.insert retVar (.tuple [.tuple [], .int (Int.ofNat (refundNext heap out.size))]), immutables := imms} evm')
    else ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm (.internalCall "_refund" args retVar) .reverted := by
  have hs := refundSource_call (hperm := by assumption) (cfg := cfg) (imms := imms) (locals := refundArgs value heap)
    (store_get_self _ _ _) (refundArgs_heap value heap) hn hb hc
  by_cases hg : refundResultValid heap success out
  · rw [if_pos hg] at hs ⊢
    exact internalCallFunctionReturn he refund_lookup (refund_bind value heap) hs
  · rw [if_neg hg] at hs ⊢
    exact internalCallFunctionRevert he refund_lookup (refund_bind value heap) hs

end Benchmarks.EAS.EAS
