import Benchmarks.Morpho.MorphoBlue.HealthyPriceSource
import Benchmarks.Morpho.MorphoBlue.OraclePriceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev healthyFunction : FunctionDecl := contract.functions[9]!

def healthyBeforeCall (p : MarketParamsWords) (account : UInt256) (imms : Store) : Frame :=
  { healthyFrame p account imms with locals :=
    ((healthyFrame p account imms).locals.insert "oracle" (.address (AccountAddress.ofNat p.oracle.toNat))) }

def healthyAfterCall (p : MarketParamsWords) (account price : UInt256) (imms : Store) : Frame :=
  { healthyBeforeCall p account imms with locals :=
    ((healthyBeforeCall p account imms).locals.insert "collateralPrice" (.int (Int.ofNat price.toNat))) }

theorem healthyBeforeCall_locals (p : MarketParamsWords) (account : UInt256) (imms : Store) :
    HealthyLocals p account (healthyBeforeCall p account imms).locals :=
  (healthyFrame_locals p account imms).insert "oracle" _ (by decide) (by decide)

theorem healthyAfterCall_locals (p : MarketParamsWords) (account price : UInt256) (imms : Store) :
    HealthyLocals p account (healthyAfterCall p account price imms).locals :=
  (healthyBeforeCall_locals p account imms).insert "collateralPrice" _ (by decide) (by decide)

theorem morphoHealthySourceZero (p : MarketParamsWords) (account : UInt256) (imms : Store) (evm : EVM.State)
    (hc : account.toNat < EVM.addressModulus)
    (hz : positionFieldWord evm.accountMap evm.executionEnv p.id account 1 = ⟨0⟩) :
    ExecFuncBody config (healthyFrame p account imms) evm healthyFunction.body
      (.returned (healthyFrame p account imms) evm (some [.bool true])) := by
  have he := evalWordEqZero ((healthyFrame_locals p account imms).evalPosition imms evm ⟨1, by decide⟩ hc)
  have hz' : positionFieldWord evm.accountMap evm.executionEnv p.id account ⟨1, by decide⟩ = ⟨0⟩ := hz
  rw [decide_eq_true hz'] at he
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn (ExecStmt.iteTrue he ?_)
  exact ExecBlock.consReturn (ExecStmt.return (by simp only [evalExprs?, evalExpr?, pure, bind, EvalResult.bind]))

theorem morphoHealthySourcePrelude (p : MarketParamsWords) (account : UInt256) (imms : Store) (evm : EVM.State)
    (hc : account.toNat < EVM.addressModulus)
    (hn : positionFieldWord evm.accountMap evm.executionEnv p.id account 1 ≠ ⟨0⟩) :
    ABlock config evm (healthyFrame p account imms) healthyFunction.body
      (healthyBeforeCall p account imms) (healthyFunction.body.drop 2) := by
  have hl := healthyFrame_locals p account imms
  have he := evalWordEqZero (hl.evalPosition imms evm ⟨1, by decide⟩ hc)
  have hn' : positionFieldWord evm.accountMap evm.executionEnv p.id account ⟨1, by decide⟩ ≠ ⟨0⟩ := hn
  rw [decide_eq_false hn'] at he
  have pref : ABlock config evm (healthyFrame p account imms) healthyFunction.body
      (healthyFrame p account imms) (healthyFunction.body.drop 1) :=
    ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.iteFalse he ExecBlock.nil) h⟩
  apply pref.letStep
  simp only [evalExpr?, hl.params, MarketParamsWords.value, tupleGetValue?,
    EvalResult.bind, EvalResult.ofOption, bind]
  rfl

theorem healthy_eval_receiver (p : MarketParamsWords) (account : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (healthyBeforeCall p account imms) evm (.var "oracle") =
      .ok (.address (AccountAddress.ofNat p.oracle.toNat)) := by
  simp only [evalExpr?, healthyBeforeCall, store_get_self, EvalResult.ofOption]

theorem morphoHealthySourceCallOk (p : MarketParamsWords) (account : UInt256) (imms : Store)
    (evm evm' : EVM.State) (out : ByteArray)
    (hcall : typedCallViaEVM config evm (AccountAddress.ofNat p.oracle.toNat) "price" 0 [] (true, evm', out) false)
    (hlen : 32 ≤ out.size) (hout : out.size < 2 ^ 138) :
    ExecStmt config (healthyBeforeCall p account imms) evm healthyFunction.body[2]!
      (.ok (healthyAfterCall p account (calldataWord out 0) imms) evm') := by
  exact oraclePriceSourceOk "collateralPrice" out (healthy_eval_receiver p account imms evm) hcall hlen hout

theorem morphoHealthySourceCallReverts (p : MarketParamsWords) (account : UInt256) (imms : Store)
    (evm evm' : EVM.State) (z : Bool) (out : ByteArray)
    (hcall : typedCallViaEVM config evm (AccountAddress.ofNat p.oracle.toNat) "price" 0 [] (z, evm', out) false)
    (hbad : ¬ (z = true ∧ 32 ≤ out.size)) :
    ExecStmt config (healthyBeforeCall p account imms) evm healthyFunction.body[2]! .reverted := by
  exact oraclePriceSourceReverts "collateralPrice" z out (healthy_eval_receiver p account imms evm) hcall hbad

theorem healthy_price_args (p : MarketParamsWords) (account price : UInt256) (imms : Store) (evm : EVM.State) :
    evalExprs? config (healthyAfterCall p account price imms) evm
      [.var "marketParams", .var "id", .var "borrower", .var "collateralPrice"] =
      .ok [p.value, .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id),
        .address (AccountAddress.ofNat account.toNat), .int (Int.ofNat price.toNat)] := by
  have hl := healthyAfterCall_locals p account price imms
  have hp := hl.evalParams imms evm
  have hi := hl.evalId imms evm
  have hb := hl.evalBorrower imms evm
  change evalExpr? config (healthyAfterCall p account price imms) evm (.var "marketParams") = _ at hp
  change evalExpr? config (healthyAfterCall p account price imms) evm (.var "id") = _ at hi
  change evalExpr? config (healthyAfterCall p account price imms) evm (.var "borrower") = _ at hb
  have hprice : evalExpr? config (healthyAfterCall p account price imms) evm (.var "collateralPrice") =
      .ok (.int (Int.ofNat price.toNat)) := by
    simp only [evalExpr?, healthyAfterCall, store_get_self, EvalResult.ofOption]
  simp only [evalExprs?, hp, hi, hb, hprice, pure, bind, EvalResult.bind]

theorem morphoHealthySourceFinish (p : MarketParamsWords) (account price : UInt256) (imms : Store)
    (evm evm' : EVM.State) (frame' : Frame) (z : Bool)
    (hb : ExecFuncBody config (healthyPriceFrame p account price imms) evm healthyPriceFunction.body
      (.returned frame' evm' (some [.bool z]))) :
    ExecBlock config (healthyAfterCall p account price imms) evm (healthyFunction.body.drop 3)
      (.returned { healthyAfterCall p account price imms with locals :=
        ((healthyAfterCall p account price imms).locals.insert "__c1" (.bool z)) } evm' (some [.bool z])) := by
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := healthyPriceFunction)
    (healthy_price_args p account price imms evm) rfl rfl hb)
  apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
  change evalExpr? config { contract := contract, locals := (healthyAfterCall p account price imms).locals.insert "__c1" (.bool z), immutables := imms } evm' (.var "__c1") = .ok (.bool z)
  simp only [evalExpr?, store_get_self, EvalResult.ofOption]

theorem morphoHealthySourceFinishReverts (p : MarketParamsWords) (account price : UInt256) (imms : Store) (evm : EVM.State)
    (hb : ExecFuncBody config (healthyPriceFrame p account price imms) evm healthyPriceFunction.body .reverted) :
    ExecBlock config (healthyAfterCall p account price imms) evm (healthyFunction.body.drop 3) .reverted :=
  ExecBlock.consRevert (internalCallFunctionRevert (callee := healthyPriceFunction)
    (healthy_price_args p account price imms evm) rfl rfl hb)

end Benchmarks.Morpho.MorphoBlue
