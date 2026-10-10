import Benchmarks.UniswapV3.Pool.ModifyPositionOutsideModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem modifyPositionOutsideSqrtsSource (imms : Store) (a : ModifyPositionArgs)
    (evm evm' : EVM.State) (second : Bool) (ha : a.Fits) (ht : validTicks a.lower a.upper) :
    ExecBlock config (modifyPositionUpdatedFrame imms a evm) evm'
      ((modifyPositionOutsideBody second).take 2)
      (.ok (modifyPositionOutsideUpperFrame imms a evm second) evm') := by
  have hpl : evalExpr? config (modifyPositionUpdatedFrame imms a evm) evm' (.var "params") =
      .ok a.value := evalExpr_var_get (by modify_position_updated_get)
  have hpu : evalExpr? config (modifyPositionOutsideLowerFrame imms a evm second) evm'
      (.var "params") = .ok a.value :=
    evalExpr_var_get (by cases second <;> modify_position_outside_get)
  have hel := evalExpr_structField (name := "tickLower") hpl rfl
  have heu := evalExpr_structField (name := "tickUpper") hpu rfl
  have hl := tickSqrtInternalSource a.lower (modifyPositionUpdatedFrame imms a evm) evm'
    [.field (.var "params") "tickLower"] (modifyPositionOutsideLowerName second) rfl
    (by simp only [evalExprs?, hel, bind, EvalResult.bind, pure])
    ha.1.1 ha.1.2 (modifyPositionTickValid a ht false)
  have hu := tickSqrtInternalSource a.upper (modifyPositionOutsideLowerFrame imms a evm second) evm'
    [.field (.var "params") "tickUpper"] (modifyPositionOutsideUpperName second)
    (by cases second <;> rfl)
    (by simp only [evalExprs?, heu, bind, EvalResult.bind, pure])
    ha.2.1.1 ha.2.1.2 (modifyPositionTickValid a ht true)
  exact ExecBlock.consNormal hl (ExecBlock.consNormal hu ExecBlock.nil)

theorem modifyPositionOutsideSource (imms : Store) (a : ModifyPositionArgs)
    (evm evm' : EVM.State) (second : Bool) (ha : a.Fits) (ht : validTicks a.lower a.upper)
    (hv : signedAmountDeltaValid second (modifyPositionOutsideArgs a)) :
    ExecBlock config (modifyPositionUpdatedFrame imms a evm) evm' (modifyPositionOutsideBody second)
      (.ok (modifyPositionOutsideFinalFrame imms a evm second) evm') := by
  have hf := modifyPositionOutsideUpperFrame_eq imms a evm second
  have hc : {modifyPositionOutsideUpperFrame imms a evm second with
      locals := signedAmountDeltaLocals (modifyPositionOutsideArgs a)} =
      signedAmountDeltaFrame imms (modifyPositionOutsideArgs a) := by rw [hf]; rfl
  have hl : lookupCallable? (modifyPositionOutsideUpperFrame imms a evm second).contract
      (signedAmountDeltaName second) = some (signedAmountDeltaFunction second).toCallable := by
    rw [hf]; exact signedAmountDeltaLookup second
  have hcall := internalCallFunctionReturn (callee := signedAmountDeltaFunction second)
    (calleeSolm := signedAmountDeltaReturnFrame imms second (modifyPositionOutsideArgs a))
    (retVar := modifyPositionOutsideAmountName second)
    (value := some [.int (signedAmountDeltaResult second (modifyPositionOutsideArgs a))])
    (evalModifyPositionOutsideAmountExprs imms a evm evm' second) hl
    (signedAmountDeltaBind second (modifyPositionOutsideArgs a))
    (by
      rw [hc]
      exact signedAmountDeltaReturns imms evm' second _ (modifyPositionOutsideArgs_fits a ha) hv)
  rw [← List.take_append_drop 2 (modifyPositionOutsideBody second)]
  apply execBlock_append_ok (modifyPositionOutsideSqrtsSource imms a evm evm' second ha ht)
  exact ExecBlock.consNormal hcall
    (ExecBlock.consNormal (modifyPositionOutsideAssignSource imms a evm evm' second) ExecBlock.nil)

theorem modifyPositionOutsideReverts (imms : Store) (a : ModifyPositionArgs)
    (evm evm' : EVM.State) (second : Bool) (ha : a.Fits) (ht : validTicks a.lower a.upper)
    (hv : ¬signedAmountDeltaValid second (modifyPositionOutsideArgs a)) :
    ExecBlock config (modifyPositionUpdatedFrame imms a evm) evm'
      (modifyPositionOutsideBody second) .reverted := by
  have hf := modifyPositionOutsideUpperFrame_eq imms a evm second
  have hc : {modifyPositionOutsideUpperFrame imms a evm second with
      locals := signedAmountDeltaLocals (modifyPositionOutsideArgs a)} =
      signedAmountDeltaFrame imms (modifyPositionOutsideArgs a) := by rw [hf]; rfl
  have hl : lookupCallable? (modifyPositionOutsideUpperFrame imms a evm second).contract
      (signedAmountDeltaName second) = some (signedAmountDeltaFunction second).toCallable := by
    rw [hf]; exact signedAmountDeltaLookup second
  have hcall := internalCallFunctionRevert (callee := signedAmountDeltaFunction second)
    (retVar := modifyPositionOutsideAmountName second)
    (evalModifyPositionOutsideAmountExprs imms a evm evm' second) hl
    (signedAmountDeltaBind second (modifyPositionOutsideArgs a))
    (by
      rw [hc]
      exact signedAmountDeltaReverts imms evm' second _ (modifyPositionOutsideArgs_fits a ha) hv)
  rw [← List.take_append_drop 2 (modifyPositionOutsideBody second)]
  apply execBlock_append_ok (modifyPositionOutsideSqrtsSource imms a evm evm' second ha ht)
  exact ExecBlock.consRevert hcall

end Benchmarks.UniswapV3.Pool
