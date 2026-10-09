import Benchmarks.Morpho.MorphoBlue.AccrueFunctionRefine
import Benchmarks.Morpho.MorphoBlue.CreateMarketSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoAccrueInternalOk (p : MarketParamsWords) (locals imms : Store) (evm evm' : EVM.State)
    (frame' : Frame) (value : Option (List Value)) (params id : Expr) (retVar : Ident)
    (hp : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm params = .ok p.value)
    (hi : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm id =
      .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id)))
    (hb : ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body (.returned frame' evm' value)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_accrueInterest" [params, id] retVar)
      (.ok (resumeAfterInternalCall { contract := contract, locals := locals, immutables := imms } retVar value) evm') := by
  exact internalCallFunctionReturn (callee := accrueInterestFunction) (value := value)
    (by simp only [evalExprs?, hp, hi, pure, bind, EvalResult.bind]; rfl) rfl rfl hb

theorem morphoAccrueInternalRevert (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (params id : Expr) (retVar : Ident)
    (hp : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm params = .ok p.value)
    (hi : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm id =
      .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id)))
    (hb : ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body .reverted) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_accrueInterest" [params, id] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := accrueInterestFunction)
    (by simp only [evalExprs?, hp, hi, pure, bind, EvalResult.bind]; rfl) rfl rfl hb

theorem morphoAccrueInternalStatic (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (params id : Expr) (retVar : Ident)
    (hp : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm params = .ok p.value)
    (hi : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm id =
      .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id)))
    (hb : ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body .staticViolation) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_accrueInterest" [params, id] retVar) .staticViolation := by
  exact ExecStmt.internalCallStatic (callee := accrueInterestFunction.toCallable)
    (by simp only [evalExprs?, hp, hi, pure, bind, EvalResult.bind]; rfl) rfl rfl hb

theorem accruePublic_locals (p : MarketParamsWords) (cd : ByteArray) (imms : Store) :
    MarketLocals p (createMarketFrame p cd imms).locals := by
  constructor
  · simp only [createMarketFrame, createMarketArgs, store_get_ne (k := "id") (a := "marketParams") _ _ (by decide),
      store_get_ne (k := "__calldata") (a := "marketParams") _ _ (by decide), store_get_self]
  · exact store_get_self _ _ _
  · simp [createMarketFrame, createMarketArgs]
  · simp [createMarketFrame, createMarketArgs]
  · simp [createMarketFrame, createMarketArgs]

theorem morphoAccruePublicPrelude (p : MarketParamsWords) (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm { contract := contract, locals := createMarketArgs p, immutables := imms }
      accrueInterestTransition.body (createMarketFrame p evm.executionEnv.calldata imms)
      (accrueInterestTransition.body.drop 4) := by
  refine ⟨fun h => (calldataPrelude_ok hcv hsize).run (ExecBlock.consNormal ?_ h)⟩
  exact morphoMarketParamsIdCall p hc evm _ imms (.var "marketParams") "id"
    (by simp only [evalExpr?, createMarketArgs,
      store_get_ne (k := "__calldata") (a := "marketParams") _ _ (by decide), store_get_self, EvalResult.ofOption])

theorem morphoAccruePublicGuard (p : MarketParamsWords) (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hcreated : marketFieldWord evm.accountMap evm.executionEnv p.id 4 ≠ ⟨0⟩) :
    ABlock config evm { contract := contract, locals := createMarketArgs p, immutables := imms }
      accrueInterestTransition.body (createMarketFrame p evm.executionEnv.calldata imms)
      (accrueInterestTransition.body.drop 5) := by
  apply (morphoAccruePublicPrelude p hc evm imms hcv hsize).requireStep
  simpa only [decide_eq_true hcreated] using
    evalWordNeZero ((accruePublic_locals p evm.executionEnv.calldata imms).evalField imms evm ⟨4, by decide⟩)

theorem morphoAccruePublicReject (p : MarketParamsWords) (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hcreated : marketFieldWord evm.accountMap evm.executionEnv p.id 4 = ⟨0⟩) :
    ExecTransitionBody config contract evm (createMarketArgs p) accrueInterestTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (morphoAccruePublicPrelude p hc evm imms hcv hsize).requireRevert
  simpa only [hcreated, ne_eq, not_true_eq_false, decide_false] using
    evalWordNeZero ((accruePublic_locals p evm.executionEnv.calldata imms).evalField imms evm ⟨4, by decide⟩)

end Benchmarks.Morpho.MorphoBlue
