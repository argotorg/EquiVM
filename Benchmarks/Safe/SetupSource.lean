import Benchmarks.Safe.SetupContext

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def setupFallbackStmt : Stmt :=
  .ite (neE (.var "fallbackHandler") zeroAddr)
    [.internalCall "internalSetFallbackHandler" [.var "fallbackHandler"] "_fallbackSet"] []

def setupPaymentStmt : Stmt :=
  .ite (gtE (.var "payment") (.intLit 0))
    [.internalCall "handlePayment" [.var "payment", .intLit 0, .intLit 1,
      .var "paymentToken", .var "paymentReceiver"] "_paymentDone"] []

theorem safeSetupEventValues (p : SetupInput) (evm : EVM.State) :
    evalExprs? config p.frame evm
      [sender, .var "_owners", .var "_threshold", .var "to", .var "fallbackHandler"] =
      .ok [.address evm.executionEnv.source, .array (p.owners.map addressArrayValue),
        uint256Value p.threshold, addressArrayValue p.target,
        addressArrayValue p.fallbackHandler] := by
  have hl := SetupLocals.initial p
  have ho : evalExpr? config p.frame evm (.var "_owners") =
      .ok (.array (p.owners.map addressArrayValue)) := evalLocalValue hl.owners
  have ht : evalExpr? config p.frame evm (.var "_threshold") =
      .ok (uint256Value p.threshold) := evalLocalValue hl.threshold
  have hto : evalExpr? config p.frame evm (.var "to") =
      .ok (addressArrayValue p.target) := evalLocalValue hl.target
  have hf : evalExpr? config p.frame evm (.var "fallbackHandler") =
      .ok (addressArrayValue p.fallbackHandler) := evalLocalValue hl.fallbackHandler
  simp only [evalExprs?, ho, ht, hto, hf, sender, evalExpr?, envValue,
    EvalResult.bind, bind, pure]

theorem safeSetupPrefix (p : SetupInput) (evm : EVM.State) {result : ExecResult}
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (ht : ExecBlock config p.frame evm (setupTransition.body.drop 2) result) :
    ExecBlock config p.frame evm setupTransition.body result :=
  .consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.emit (safeSetupEventValues p evm)) ht)

theorem safeSetupStatic (p : SetupInput) (evm : EVM.State)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hp : evm.executionEnv.perm = false) :
    ExecBlock config p.frame evm setupTransition.body .staticViolation :=
  .consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consStatic (.emitStatic (safeSetupEventValues p evm) hp))

theorem safeSetupOwnersCall (p : SetupInput) (evm : EVM.State) {locals : Store}
    {result : ExecResult} (hl : SetupLocals p locals)
    (hb : ExecFuncBody config p.ownersInput.frame evm setupOwnersFunction.body result) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "setupOwners" [.var "_owners", .var "_threshold"] "_ownersSetup")
      (internalCallResult { contract := contract, locals := locals } "_ownersSetup" result) :=
  safeInternalSetupOwners rfl rfl (evalLocalValue hl.owners) (evalLocalValue hl.threshold) hb

theorem safeSetupModulesCall (p : SetupInput) (evm : EVM.State) {locals : Store}
    {result : ExecResult} (hl : SetupLocals p locals)
    (hb : ExecFuncBody config p.modulesInput.frame evm setupModulesFunction.body result) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "setupModules" [.var "to", .var "data"] "_modulesSetup")
      (internalCallResult { contract := contract, locals := locals } "_modulesSetup" result) :=
  safeInternalSetupModules (p := p.modulesInput) rfl rfl
    (evalLocalValue hl.target) (evalLocalValue hl.payload) hb

theorem safeSetupFallbackSkip (p : SetupInput) (evm : EVM.State) {locals : Store}
    (hl : SetupLocals p locals) (hc : p.fallbackHandler.toNat < EVM.addressModulus)
    (hz : p.fallbackHandler = ⟨0⟩) :
    ExecStmt config { contract := contract, locals := locals } evm setupFallbackStmt
      (.ok { contract := contract, locals := locals } evm) := by
  exact .iteFalse (by simpa only [hz, ne_self_iff_false, decide_false] using
    safeSetupFallbackCondition evm hl hc) .nil

theorem safeSetupFallbackCall (p : SetupInput) (evm : EVM.State) {locals : Store}
    {result : ExecResult} (hl : SetupLocals p locals)
    (hc : p.fallbackHandler.toNat < EVM.addressModulus) (hn : p.fallbackHandler ≠ ⟨0⟩)
    (hb : ExecFuncBody config (fallbackHandlerFrame p.fallbackHandler) evm
      internalSetFallbackHandlerFunction.body result) :
    ExecStmt config { contract := contract, locals := locals } evm setupFallbackStmt
      (internalCallResult { contract := contract, locals := locals } "_fallbackSet" result) := by
  apply ExecStmt.iteTrue (by
    have he := safeSetupFallbackCondition evm hl hc
    rw [decide_eq_true hn] at he
    exact he)
  exact execBlock_singleton (safeInternalSetupFallback rfl rfl
    (evalLocalValue hl.fallbackHandler) hb)

theorem safeSetupPaymentSkip (p : SetupInput) (evm : EVM.State) {locals : Store}
    (hl : SetupLocals p locals) (hz : p.payment = ⟨0⟩) :
    ExecStmt config { contract := contract, locals := locals } evm setupPaymentStmt
      (.ok { contract := contract, locals := locals } evm) := by
  exact .iteFalse (by simpa only [hz, ne_self_iff_false, decide_false] using
    safeSetupPaymentCondition evm hl) .nil

theorem safeSetupPaymentCall (p : SetupInput) (evm : EVM.State) {locals : Store}
    {result : ExecResult} (hl : SetupLocals p locals) (hn : p.payment ≠ ⟨0⟩)
    (hb : ExecFuncBody config p.paymentInput.frame evm handlePaymentFunction.body result) :
    ExecStmt config { contract := contract, locals := locals } evm setupPaymentStmt
      (internalCallResult { contract := contract, locals := locals } "_paymentDone" result) := by
  apply ExecStmt.iteTrue (by
    have he := safeSetupPaymentCondition evm hl
    rw [decide_eq_true hn] at he
    exact he)
  apply execBlock_singleton
  exact safeInternalPayment (p := p.paymentInput) rfl rfl (evalLocalValue hl.payment)
    (by simp only [evalExpr?]; rfl) (by simp only [evalExpr?]; rfl)
    (evalLocalValue hl.paymentToken) (evalLocalValue hl.paymentReceiver) hb

end Benchmarks.Safe
