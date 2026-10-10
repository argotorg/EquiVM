import Benchmarks.UniswapV4PoolManager.NarrowWords
import Benchmarks.UniswapV4PoolManager.CallComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev lpFeeDynamicFunction : FunctionDecl := contract.functions[48]!
abbrev lpFeeValidateFunction : FunctionDecl := contract.functions[49]!
abbrev lpFeeValidFunction : FunctionDecl := contract.functions[86]!

theorem lpFeeDynamic_lookup : lookupCallable? contract "LPFeeLibrary_isDynamicFee" =
    some lpFeeDynamicFunction.toCallable := rfl
theorem lpFeeValidate_lookup : lookupCallable? contract "LPFeeLibrary_validate" =
    some lpFeeValidateFunction.toCallable := rfl
theorem lpFeeValid_lookup : lookupCallable? contract "LPFeeLibrary_isValid" =
    some lpFeeValidFunction.toCallable := rfl

-- LIBRARY CANDIDATE: compare two natural-valued expressions with <=.
theorem evalNatLe {cfg : Config} {f : Frame} {evm : EVM.State} {e0 e1 : Expr} {a b : Nat}
    (h0 : evalExpr? cfg f evm e0 = .ok (.int (Int.ofNat a)))
    (h1 : evalExpr? cfg f evm e1 = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg f evm (.binary .le e0 e1) = .ok (.bool (decide (a ≤ b))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), h0, h1]
  simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast, Nat.cast_le]

theorem lpFeeDynamicBody {f : Frame} {evm : EVM.State} {fee : UInt256}
    (hs : f.locals.get? "self" = some (.int (Int.ofNat fee.toNat))) :
    ExecFuncBody config f evm lpFeeDynamicFunction.body
      (.returned f evm (some [.bool (decide (fee.toNat = 8388608))])) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  have he := evalIntEq (cfg := config) (f := f) (evm := evm) (evalLocalValue hs)
    (show evalExpr? config f evm (.intLit 8388608) = .ok (.int (Int.ofNat 8388608)) by
      simp only [evalExpr?, pure]; rfl)
  simpa only [Int.ofNat_eq_natCast, Int.natCast_inj] using he

theorem lpFeeDynamicCall {f : Frame} {evm : EVM.State} {fee : UInt256} {e : Expr}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (.int (Int.ofNat fee.toNat)))
    (retVar : Ident) :
    ExecStmt config f evm (.internalCall "LPFeeLibrary_isDynamicFee" [e] retVar)
      (.ok {f with locals := f.locals.insert retVar (.bool (decide (fee.toNat = 8388608)))} evm) := by
  apply internalCallFunctionReturn (argVals := [.int (Int.ofNat fee.toNat)])
    (value := some [.bool (decide (fee.toNat = 8388608))])
    (evalExprs?_singleton he) (by rw [hf]; exact lpFeeDynamic_lookup) rfl
  exact lpFeeDynamicBody (store_get_self _ _ _)

theorem lpFeeValidBody {f : Frame} {evm : EVM.State} {fee : UInt256}
    (hs : f.locals.get? "self" = some (.int (Int.ofNat fee.toNat))) :
    ExecFuncBody config f evm lpFeeValidFunction.body
      (.returned f evm (some [.bool (decide (fee.toNat ≤ 1000000))])) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  exact evalNatLe (evalLocalValue hs) (by simp only [evalExpr?, pure]; rfl)

theorem lpFeeValidCall {f : Frame} {evm : EVM.State} {fee : UInt256} {e : Expr}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (.int (Int.ofNat fee.toNat)))
    (retVar : Ident) :
    ExecStmt config f evm (.internalCall "LPFeeLibrary_isValid" [e] retVar)
      (.ok {f with locals := f.locals.insert retVar (.bool (decide (fee.toNat ≤ 1000000)))} evm) := by
  apply internalCallFunctionReturn (argVals := [.int (Int.ofNat fee.toNat)])
    (value := some [.bool (decide (fee.toNat ≤ 1000000))])
    (evalExprs?_singleton he) (by rw [hf]; exact lpFeeValid_lookup) rfl
  exact lpFeeValidBody (store_get_self _ _ _)

theorem lpFeeValidateBody {f : Frame} {evm : EVM.State} {fee : UInt256}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (.int (Int.ofNat fee.toNat))) :
    ExecFuncBody config f evm lpFeeValidateFunction.body
      (if fee.toNat ≤ 1000000 then
        .returned {f with locals := f.locals.insert "__c0" (.bool true)} evm none else .reverted) := by
  have hc := lpFeeValidCall (evm := evm) hf (evalLocalValue hs) "__c0"
  by_cases hv : fee.toNat ≤ 1000000
  · rw [if_pos hv]
    simp only [hv, decide_true] at hc
    exact ExecFuncBody.execBlockOK (ExecBlock.consNormal hc
      (ExecBlock.consNormal (ExecStmt.iteFalse (evalNotBool (va := true) (evalLocalValue (store_get_self _ _ _)))
        ExecBlock.nil) ExecBlock.nil))
  · rw [if_neg hv]
    simp only [hv, decide_false] at hc
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal hc
      (ExecBlock.consRevert (ExecStmt.iteTrue (evalNotBool (va := false) (evalLocalValue (store_get_self _ _ _)))
        (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure]))))))

theorem lpFeeValidateCall {f : Frame} {evm : EVM.State} {fee : UInt256} {e : Expr}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (.int (Int.ofNat fee.toNat)))
    (retVar : Ident) :
    ExecStmt config f evm (.internalCall "LPFeeLibrary_validate" [e] retVar)
      (if fee.toNat ≤ 1000000 then .ok {f with locals := f.locals.insert retVar .unit} evm else .reverted) := by
  have hl : lookupCallable? f.contract "LPFeeLibrary_validate" = some lpFeeValidateFunction.toCallable := by
    rw [hf]; exact lpFeeValidate_lookup
  have hb := lpFeeValidateBody (f := {f with locals := (∅ : Store).insert "self" (.int (Int.ofNat fee.toNat))})
    (evm := evm) hf (store_get_self _ _ _)
  by_cases hv : fee.toNat ≤ 1000000
  · rw [if_pos hv] at hb ⊢
    exact internalCallFunctionReturn (evalExprs?_singleton he) hl rfl hb
  · rw [if_neg hv] at hb ⊢
    exact internalCallFunctionRevert (evalExprs?_singleton he) hl rfl hb

end Benchmarks.UniswapV4PoolManager
