import Benchmarks.EAS.EAS.Allocate

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

abbrev ecdsaErrorFunction : FunctionDecl := contract.functions[33]!
def ecdsaErrorGuard (op : BinaryOp) (n : Int) : Expr := .binary op (.var "error") (.intLit n)
def ecdsaErrorReturn : Stmt := .return [.tupleLit [],.var "$EAS.freeMemory"]
def ecdsaErrorBranch : Stmt := .ite (ecdsaErrorGuard .eq 0) [ecdsaErrorReturn]
  [.ite (ecdsaErrorGuard .eq 1) [.require (.boolLit false)]
    [.ite (ecdsaErrorGuard .eq 2) [.require (.boolLit false)] [.require (ecdsaErrorGuard .ne 3)]]]
theorem ecdsaError_body : ecdsaErrorFunction.body =
    [.require (ecdsaErrorGuard .lt 5),ecdsaErrorBranch,ecdsaErrorReturn] := by native_decide

theorem ecdsaError_return {cfg : Config} {frame : Frame} {evm : EVM.State} {heap : Nat}
    (hh : frame.locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecStmt fork cfg frame evm ecdsaErrorReturn (.returned frame evm (some [.tuple [],.int (Int.ofNat heap)])) := by
  apply ExecStmt.return
  simp only [evalExprs?,evalExpr?,evalExprList?,hh,EvalResult.ofOption,EvalResult.bind,bind,pure]

theorem ecdsaErrorSource {cfg : Config} {frame : Frame} {evm : EVM.State} {n heap : Nat}
    (he : frame.locals.get? "error" = some (.int (Int.ofNat n)))
    (hh : frame.locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    if n = 0 ∨ n = 4 then
      ExecFuncBody fork cfg frame evm ecdsaErrorFunction.body
        (.returned frame evm (some [.tuple [],.int (Int.ofNat heap)]))
    else ExecFuncBody fork cfg frame evm ecdsaErrorFunction.body .reverted := by
  rw [ecdsaError_body]
  by_cases hn : n < 5
  · interval_cases n
    · simp only [if_pos (Or.inl rfl)]
      apply ExecFuncBody.execBlockRet
      refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
      · simp only [ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
      apply ExecBlock.consReturn
      apply ExecStmt.iteTrue
      · simp only [ecdsaErrorBranch,ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
      exact ExecBlock.consReturn (ecdsaError_return hh)
    · simp only [show ¬ (1 = (0 : Nat) ∨ 1 = 4) by decide,if_false]
      apply ExecFuncBody.execBlockRevert
      refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
      · simp only [ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
      apply ExecBlock.consRevert
      apply ExecStmt.iteFalse
      · simp only [ecdsaErrorBranch,ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
      apply ExecBlock.consRevert
      apply ExecStmt.iteTrue
      · simp only [ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
      exact ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?,pure]))
    · simp only [show ¬ (2 = (0 : Nat) ∨ 2 = 4) by decide,if_false]
      apply ExecFuncBody.execBlockRevert
      refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
      · simp only [ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
      apply ExecBlock.consRevert
      apply ExecStmt.iteFalse
      · simp only [ecdsaErrorBranch,ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
      apply ExecBlock.consRevert
      apply ExecStmt.iteFalse
      · simp only [ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
      apply ExecBlock.consRevert
      apply ExecStmt.iteTrue
      · simp only [ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
      exact ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?,pure]))
    · simp only [show ¬ (3 = (0 : Nat) ∨ 3 = 4) by decide,if_false]
      apply ExecFuncBody.execBlockRevert
      refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
      · simp only [ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
      apply ExecBlock.consRevert
      apply ExecStmt.iteFalse
      · simp only [ecdsaErrorBranch,ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
      apply ExecBlock.consRevert
      apply ExecStmt.iteFalse
      · simp only [ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
      apply ExecBlock.consRevert
      apply ExecStmt.iteFalse
      · simp only [ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
      apply ExecBlock.consRevert
      apply ExecStmt.requireFalse
      simp only [ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
    · simp only [if_pos (Or.inr rfl)]
      apply ExecFuncBody.execBlockRet
      refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
      · simp only [ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
      apply ExecBlock.consNormal
      · apply ExecStmt.iteFalse
        · simp only [ecdsaErrorBranch,ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
        apply ExecBlock.consNormal
        · apply ExecStmt.iteFalse
          · simp only [ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
          apply ExecBlock.consNormal
          · apply ExecStmt.iteFalse
            · simp only [ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
            refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil
            simp only [ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?] <;> rfl
          exact ExecBlock.nil
        exact ExecBlock.nil
      exact ExecBlock.consReturn (ecdsaError_return hh)
  · rw [if_neg (by omega)]
    apply ExecFuncBody.execBlockRevert
    apply ExecBlock.consRevert
    apply ExecStmt.requireFalse
    have hn' : ¬ (Int.ofNat n < (5 : Int)) := by simp only [Int.ofNat_eq_natCast]; omega
    simp only [ecdsaErrorGuard,evalExpr?,he,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?,hn',decide_false]

def ecdsaErrorArgs (n heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "error" (.int (Int.ofNat n))
theorem ecdsaError_lookup : lookupCallable? contract "ECDSA__throwError" = some ecdsaErrorFunction.toCallable := rfl
theorem ecdsaError_bind (n heap : Nat) : bindParams? ecdsaErrorFunction.params
    [.int (Int.ofNat n),.int (Int.ofNat heap)] = some (ecdsaErrorArgs n heap) := rfl

theorem ecdsaErrorCall {cfg : Config} {L imms : Store} {evm : EVM.State}
    {args : List Expr} {retVar : Ident} {n heap : Nat}
    (he : evalExprs? cfg {contract := contract,locals := L,immutables := imms} evm args =
      .ok [.int (Int.ofNat n),.int (Int.ofNat heap)]) :
    if n = 0 ∨ n = 4 then
      ExecStmt fork cfg {contract := contract,locals := L,immutables := imms} evm
        (.internalCall "ECDSA__throwError" args retVar)
        (.ok (resumeAfterInternalCall {contract := contract,locals := L,immutables := imms} retVar
          (some [.tuple [],.int (Int.ofNat heap)])) evm)
    else ExecStmt fork cfg {contract := contract,locals := L,immutables := imms} evm
      (.internalCall "ECDSA__throwError" args retVar) .reverted := by
  have hs := ecdsaErrorSource (fork := fork) (cfg := cfg) (evm := evm) (n := n) (heap := heap)
    (frame := {contract := contract,locals := ecdsaErrorArgs n heap,immutables := imms})
    (by simp only [ecdsaErrorArgs,store_get_self])
    (by simp only [ecdsaErrorArgs,store_get_ne _ _ (by decide : ("error" == "$EAS.freeMemory") = false),store_get_self])
  split_ifs with hn
  · rw [if_pos hn] at hs
    exact internalCallFunctionReturn he ecdsaError_lookup (ecdsaError_bind n heap) hs
  · rw [if_neg hn] at hs
    exact internalCallFunctionRevert he ecdsaError_lookup (ecdsaError_bind n heap) hs

end Benchmarks.EAS.EAS
