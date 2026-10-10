import Benchmarks.UniswapV4PoolManager.PoolStorage
import Benchmarks.UniswapV4PoolManager.Slot0Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev poolCheckFunction : FunctionDecl := contract.functions[16]!
theorem poolCheck_lookup : lookupCallable? contract "Pool_checkPoolInitialized" = some poolCheckFunction.toCallable := rfl

-- LIBRARY CANDIDATE: equality of unsigned word-valued source expressions.
theorem evalEqWords {cfg : Config} {f : Frame} {evm : EVM.State} {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg f evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg f evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg f evm (.binary .eq lhs rhs) = .ok (.bool (decide (a = b))) := by
  have he : (Int.ofNat a.toNat = Int.ofNat b.toNat) ↔ a = b :=
    ⟨fun h => u256_inj (Int.ofNat.inj h), fun h => by rw [h]⟩
  simpa only [he] using evalIntEq ha hb

def poolSqrtPriceWord (evm : EVM.State) (id : UInt256) : UInt256 := slot0SqrtPriceWord (poolSlot0Word evm id)

theorem poolCheckBody {f : Frame} {evm : EVM.State} {id : UInt256}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id)) :
    ExecFuncBody config f evm poolCheckFunction.body
      (if poolSqrtPriceWord evm id = ⟨0⟩ then .reverted else
        .returned {f with locals := f.locals.insert "__c0" (.int (Int.ofNat (poolSqrtPriceWord evm id).toNat))} evm none) := by
  have hcall := slot0SqrtCall (evm := evm) hf (poolSlot0_read hs) "__c0"
  let f1 : Frame := {f with locals := f.locals.insert "__c0" (.int (Int.ofNat (poolSqrtPriceWord evm id).toNat))}
  have hcond := evalEqWords (evalLocalValue (cfg := config) (f := f1) (evm := evm) (store_get_self _ _ _))
    (show evalExpr? config f1 evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  by_cases hz : poolSqrtPriceWord evm id = ⟨0⟩
  · rw [if_pos hz]
    simp only [hz, decide_true] at hcond
    exact .execBlockRevert (ExecBlock.consNormal hcall (ExecBlock.consRevert
      (ExecStmt.iteTrue hcond (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure]))))))
  · rw [if_neg hz]
    simp only [hz, decide_false] at hcond
    exact .execBlockOK (ExecBlock.consNormal hcall
      (ExecBlock.consNormal (ExecStmt.iteFalse hcond ExecBlock.nil) ExecBlock.nil))

theorem poolCheckCall {f : Frame} {evm : EVM.State} {e : Expr} {id : UInt256}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (poolRefValue id)) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Pool_checkPoolInitialized" [e] retVar)
      (if poolSqrtPriceWord evm id = ⟨0⟩ then .reverted else .ok {f with locals := f.locals.insert retVar .unit} evm) := by
  have hb := poolCheckBody (f := {f with locals := (∅ : Store).insert "self" (poolRefValue id)})
    (evm := evm) hf (store_get_self _ _ _)
  have hl : lookupCallable? f.contract "Pool_checkPoolInitialized" = some poolCheckFunction.toCallable := by
    rw [hf]; exact poolCheck_lookup
  by_cases hz : poolSqrtPriceWord evm id = ⟨0⟩
  · rw [if_pos hz] at hb ⊢
    exact internalCallFunctionRevert (evalExprs?_singleton he) hl rfl hb
  · rw [if_neg hz] at hb ⊢
    exact internalCallFunctionReturn (evalExprs?_singleton he) hl rfl hb

end Benchmarks.UniswapV4PoolManager
