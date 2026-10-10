import Benchmarks.UniswapV4PoolManager.LPFeeSource
import Benchmarks.UniswapV4PoolManager.Slot0Source
import Benchmarks.UniswapV4PoolManager.Values
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def lpFeeIsOverride (fee : UInt256) : Bool := decide (UInt256.land fee (UInt256.ofNat 4194304) ≠ ⟨0⟩)
def lpFeeRemoveOverride (fee : UInt256) : UInt256 := UInt256.land fee (UInt256.ofNat 12582911)

theorem lpFeeRemoveOverride_bound (fee : UInt256) : (lpFeeRemoveOverride fee).toNat < 2^24 := by
  rw [lpFeeRemoveOverride, uland_toNat]
  exact lt_of_le_of_lt (nat_land_le_right _ _) (by decide)

abbrev lpFeeOverrideFunction : FunctionDecl := contract.functions[98]!
abbrev lpFeeRemoveOverrideFunction : FunctionDecl := contract.functions[110]!
abbrev lpFeeOverrideValidateFunction : FunctionDecl := contract.functions[99]!
theorem lpFeeOverride_lookup : lookupCallable? contract "LPFeeLibrary_isOverride" = some lpFeeOverrideFunction.toCallable := rfl
theorem lpFeeRemoveOverride_lookup : lookupCallable? contract "LPFeeLibrary_removeOverrideFlag" = some lpFeeRemoveOverrideFunction.toCallable := rfl
theorem lpFeeOverrideValidate_lookup : lookupCallable? contract "LPFeeLibrary_removeOverrideFlagAndValidate" = some lpFeeOverrideValidateFunction.toCallable := rfl

theorem lpFeeOverrideBody {f : Frame} {evm : State} {fee : UInt256}
    (hs : f.locals.get? "self" = some (.int (Int.ofNat fee.toNat))) (hc : fee.toNat < 2^24) :
    ExecFuncBody config f evm lpFeeOverrideFunction.body (.returned f evm (some [.bool (lpFeeIsOverride fee)])) := by
  have he := evalUintWordAnd (y := UInt256.ofNat 4194304) ⟨24, by decide⟩ hc (by decide)
    (evalLocalValue (cfg := config) (evm := evm) hs)
    (show evalExpr? config f evm (.intLit 4194304) = .ok (.int (Int.ofNat (UInt256.ofNat 4194304).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  exact .execBlockRet (ABlock.start.returns (evalNeWords he
    (show evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)))

theorem lpFeeRemoveOverrideBody {f : Frame} {evm : State} {fee : UInt256}
    (hs : f.locals.get? "self" = some (.int (Int.ofNat fee.toNat))) (hc : fee.toNat < 2^24) :
    ExecFuncBody config f evm lpFeeRemoveOverrideFunction.body
      (.returned f evm (some [.int (Int.ofNat (lpFeeRemoveOverride fee).toNat)])) := by
  exact .execBlockRet (ABlock.start.returns
    (evalUintWordAnd (y := UInt256.ofNat 12582911) ⟨24, by decide⟩ hc (by decide)
      (evalLocalValue hs) (by simp only [evalExpr?, pure]; rfl)))

theorem lpFeeOverrideCall {f : Frame} {evm : State} {e : Expr} {fee : UInt256}
    (hf : f.contract = contract) (hc : fee.toNat < 2^24)
    (he : evalExpr? config f evm e = .ok (.int (Int.ofNat fee.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "LPFeeLibrary_isOverride" [e] ret)
      (.ok (valueLocal f ret (.bool (lpFeeIsOverride fee))) evm) := by
  apply internalCallFunctionReturn (argVals := [.int (Int.ofNat fee.toNat)])
    (value := some [.bool (lpFeeIsOverride fee)]) (evalExprs?_singleton he)
    (by rw [hf]; exact lpFeeOverride_lookup) rfl
  exact lpFeeOverrideBody (store_get_self _ _ _) hc

theorem lpFeeRemoveOverrideCall {f : Frame} {evm : State} {e : Expr} {fee : UInt256}
    (hf : f.contract = contract) (hc : fee.toNat < 2^24)
    (he : evalExpr? config f evm e = .ok (.int (Int.ofNat fee.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "LPFeeLibrary_removeOverrideFlag" [e] ret)
      (.ok (valueLocal f ret (.int (Int.ofNat (lpFeeRemoveOverride fee).toNat))) evm) := by
  apply internalCallFunctionReturn (argVals := [.int (Int.ofNat fee.toNat)])
    (value := some [.int (Int.ofNat (lpFeeRemoveOverride fee).toNat)]) (evalExprs?_singleton he)
    (by rw [hf]; exact lpFeeRemoveOverride_lookup) rfl
  exact lpFeeRemoveOverrideBody (store_get_self _ _ _) hc

theorem lpFeeOverrideValidateBody {f : Frame} {evm : State} {fee : UInt256}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (.int (Int.ofNat fee.toNat)))
    (hc : fee.toNat < 2^24) :
    ∃ f', ExecFuncBody config f evm lpFeeOverrideValidateFunction.body
      (if (lpFeeRemoveOverride fee).toNat ≤ 1000000 then
        .returned f' evm (some [.int (Int.ofNat (lpFeeRemoveOverride fee).toNat)]) else .reverted) := by
  let f1 := valueLocal f "fee" (.int 0)
  let f2 := valueLocal f1 "__c0" (.int (Int.ofNat (lpFeeRemoveOverride fee).toNat))
  let f3 := valueLocal f2 "fee" (.int (Int.ofNat (lpFeeRemoveOverride fee).toNat))
  let f4 := valueLocal f3 "__c1" .unit
  have hself1 : f1.locals.get? "self" = some (.int (Int.ofNat fee.toNat)) :=
    (store_get_ne _ _ (by decide : ("fee" == "self") = false)).trans hs
  have hremove := lpFeeRemoveOverrideCall (f := f1) (evm := evm) hf hc (evalLocalValue hself1) "__c0"
  have hpre : ExecBlock config f evm (lpFeeOverrideValidateFunction.body.take 3) (.ok f3 evm) :=
    ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
      (ExecBlock.consNormal hremove (execBlock_singleton (ExecStmt.assign
        (evalLocalValue (store_get_self _ _ _)) (assignLocalValue
          ((store_get_ne _ _ (by decide : ("__c0" == "fee") = false)).trans (store_get_self _ _ _))))))
  have hvalidate := lpFeeValidateCall (f := f3) (evm := evm) hf
    (evalLocalValue (store_get_self _ _ _)) "__c1"
  by_cases hv : (lpFeeRemoveOverride fee).toNat ≤ 1000000
  · rw [if_pos hv] at hvalidate
    refine ⟨f4, ?_⟩
    rw [if_pos hv]
    exact .execBlockRet (execBlock_append hpre (ExecBlock.consNormal hvalidate
      (ABlock.start.returns (evalLocalValue
        ((store_get_ne _ _ (by decide : ("__c1" == "fee") = false)).trans (store_get_self _ _ _))))))
  · rw [if_neg hv] at hvalidate
    refine ⟨f3, ?_⟩
    rw [if_neg hv]
    exact .execBlockRevert (execBlock_append hpre (ExecBlock.consRevert hvalidate))

theorem lpFeeOverrideValidateCall {f : Frame} {evm : State} {fee : UInt256} {e : Expr}
    (hf : f.contract = contract) (hc : fee.toNat < 2^24)
    (he : evalExpr? config f evm e = .ok (.int (Int.ofNat fee.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "LPFeeLibrary_removeOverrideFlagAndValidate" [e] ret)
      (if (lpFeeRemoveOverride fee).toNat ≤ 1000000 then
        .ok (valueLocal f ret (.int (Int.ofNat (lpFeeRemoveOverride fee).toNat))) evm else .reverted) := by
  obtain ⟨f', hb⟩ := lpFeeOverrideValidateBody
    (f := {f with locals := (∅ : Store).insert "self" (.int (Int.ofNat fee.toNat))})
    (evm := evm) hf (store_get_self _ _ _) hc
  have hl : lookupCallable? f.contract "LPFeeLibrary_removeOverrideFlagAndValidate" =
      some lpFeeOverrideValidateFunction.toCallable := by rw [hf]; exact lpFeeOverrideValidate_lookup
  by_cases hv : (lpFeeRemoveOverride fee).toNat ≤ 1000000
  · rw [if_pos hv] at hb ⊢
    exact internalCallFunctionReturn (evalExprs?_singleton he) hl rfl hb
  · rw [if_neg hv] at hb ⊢
    exact internalCallFunctionRevert (evalExprs?_singleton he) hl rfl hb

end Benchmarks.UniswapV4PoolManager
