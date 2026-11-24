import Benchmarks.Safe.ViaIR.SetupContext

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

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

def setupAllocationExpr : Expr :=
  leE (addE (mulE (.intLit 32) (localLength "_owners")) (localLength "data"))
    (.ite (andE (gtE (.var "payment") (.intLit 0))
      (neE (.var "paymentToken") zeroAddr))
      (.intLit (2 ^ 64 - 352)) (.intLit (2 ^ 64 - 224)))

def SetupInput.allocationLimit (p : SetupInput) : Nat :=
  if p.payment ≠ ⟨0⟩ ∧ AccountAddress.ofNat p.paymentToken.toNat ≠ EVM.address 0
    then 2 ^ 64 - 352 else 2 ^ 64 - 224

theorem safeSetupAllocationLimit_le (p : SetupInput) : p.allocationLimit ≤ 2 ^ 64 - 224 := by
  unfold SetupInput.allocationLimit
  split <;> decide

theorem safeSetupAllocationLimit_token (p : SetupInput) (hpay : p.payment ≠ ⟨0⟩)
    (htoken : p.paymentInput.gasToken ≠ EVM.address 0) :
    p.allocationLimit = 2 ^ 64 - 352 := if_pos ⟨hpay, htoken⟩

theorem safeSetupAllocationCondition (p : SetupInput) (evm : EVM.State) :
    evalExpr? config p.frame evm setupAllocationExpr =
      .ok (.bool (decide (32 * p.owners.length + p.payload.size ≤ p.allocationLimit))) := by
  have hl := SetupLocals.initial p
  have ho := evalLocalArrayLength (cfg := config) (frame := p.frame) (evm := evm) hl.owners
  have hd := evalLocalBytesLength (cfg := config) (frame := p.frame) (evm := evm) hl.payload
  simp only [List.length_map] at ho
  change evalExpr? config p.frame evm (localLength "_owners") =
    .ok (.int (Int.ofNat p.owners.length)) at ho
  change evalExpr? config p.frame evm (localLength "data") =
    .ok (.int (Int.ofNat p.payload.size)) at hd
  have hp := safeSetupPaymentCondition evm hl
  have htv : evalExpr? config p.frame evm (.var "paymentToken") =
      .ok (addressArrayValue p.paymentToken) := evalLocalValue hl.paymentToken
  have ht : evalExpr? config p.frame evm (neE (.var "paymentToken") zeroAddr) =
      .ok (.bool (decide (AccountAddress.ofNat p.paymentToken.toNat ≠ EVM.address 0))) := by
    rw [neE, evalExpr_binary_nonshort (by decide) (by decide), htv]
    simp [zeroAddr, addrSt, evalExpr?, castValue?, evalBinaryOpNeAddress,
      addressArrayValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq]
    rfl
  have hc := evalBoolAnd hp ht
  change evalExpr? config p.frame evm
    (andE (gtE (.var "payment") (.intLit 0)) (neE (.var "paymentToken") zeroAddr)) =
    .ok (.bool (decide (p.payment ≠ ⟨0⟩) &&
      decide (AccountAddress.ofNat p.paymentToken.toNat ≠ EVM.address 0))) at hc
  rw [setupAllocationExpr, leE, evalExpr_binary_nonshort (by decide) (by decide),
    addE, evalExpr_binary_nonshort (by decide) (by decide),
    mulE, evalExpr_binary_nonshort (by decide) (by decide), ho, hd]
  simp only [evalExpr?, hc, EvalResult.bind, bind, pure]
  by_cases hpay : p.payment = ⟨0⟩ <;>
    by_cases htoken : AccountAddress.ofNat p.paymentToken.toNat = EVM.address 0 <;>
      simp [hpay, htoken, SetupInput.allocationLimit, evalBinaryOp?, Int.ofNat_eq_natCast] <;>
        omega

theorem safeSetupPrefix (p : SetupInput) (evm : EVM.State) {result : ExecResult}
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (ha : 32 * p.owners.length + p.payload.size ≤ p.allocationLimit)
    (ht : ExecBlock fork config p.frame evm (setupTransition.body.drop 3) result)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config p.frame evm setupTransition.body result :=
  .consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.emit (hperm := hperm) (safeSetupEventValues p evm))
      (.consNormal (.requireTrue (by
        simpa only [ha, decide_true] using safeSetupAllocationCondition p evm)) ht))

theorem safeSetupAllocationRevert (p : SetupInput) (evm : EVM.State)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (ha : ¬32 * p.owners.length + p.payload.size ≤ p.allocationLimit)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config p.frame evm setupTransition.body .reverted :=
  .consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.emit (hperm := hperm) (safeSetupEventValues p evm))
      (.consRevert (.requireFalse (by
        simpa only [ha, decide_false] using safeSetupAllocationCondition p evm))))

theorem safeSetupStatic (p : SetupInput) (evm : EVM.State)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hp : evm.executionEnv.perm = false) :
    ExecBlock fork config p.frame evm setupTransition.body .staticViolation :=
  .consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consStatic (.emitStatic (safeSetupEventValues p evm) hp))

theorem safeSetupOwnersCall (p : SetupInput) (evm : EVM.State) {locals : Store}
    {result : ExecResult} (hl : SetupLocals p locals)
    (hb : ExecFuncBody fork config p.ownersInput.frame evm setupOwnersFunction.body result) :
    ExecStmt fork config { contract := contract, locals := locals } evm
      (.internalCall "setupOwners" [.var "_owners", .var "_threshold"] "_ownersSetup")
      (internalCallResult { contract := contract, locals := locals } "_ownersSetup" result) :=
  safeInternalSetupOwners rfl rfl (evalLocalValue hl.owners) (evalLocalValue hl.threshold) hb

theorem safeSetupModulesCall (p : SetupInput) (evm : EVM.State) {locals : Store}
    {result : ExecResult} (hl : SetupLocals p locals)
    (hb : ExecFuncBody fork config p.modulesInput.frame evm setupModulesFunction.body result) :
    ExecStmt fork config { contract := contract, locals := locals } evm
      (.internalCall "setupModules" [.var "to", .var "data"] "_modulesSetup")
      (internalCallResult { contract := contract, locals := locals } "_modulesSetup" result) :=
  safeInternalSetupModules (p := p.modulesInput) rfl rfl
    (evalLocalValue hl.target) (evalLocalValue hl.payload) hb

theorem safeSetupFallbackSkip (p : SetupInput) (evm : EVM.State) {locals : Store}
    (hl : SetupLocals p locals) (hc : p.fallbackHandler.toNat < EVM.addressModulus)
    (hz : p.fallbackHandler = ⟨0⟩) :
    ExecStmt fork config { contract := contract, locals := locals } evm setupFallbackStmt
      (.ok { contract := contract, locals := locals } evm) := by
  exact .iteFalse (by simpa only [hz, ne_self_iff_false, decide_false] using
    safeSetupFallbackCondition evm hl hc) .nil

theorem safeSetupFallbackCall (p : SetupInput) (evm : EVM.State) {locals : Store}
    {result : ExecResult} (hl : SetupLocals p locals)
    (hc : p.fallbackHandler.toNat < EVM.addressModulus) (hn : p.fallbackHandler ≠ ⟨0⟩)
    (hb : ExecFuncBody fork config (fallbackHandlerFrame p.fallbackHandler) evm
      internalSetFallbackHandlerFunction.body result) :
    ExecStmt fork config { contract := contract, locals := locals } evm setupFallbackStmt
      (internalCallResult { contract := contract, locals := locals } "_fallbackSet" result) := by
  apply ExecStmt.iteTrue (by
    have he := safeSetupFallbackCondition evm hl hc
    rw [decide_eq_true hn] at he
    exact he)
  exact execBlock_singleton (safeInternalSetupFallback rfl rfl
    (evalLocalValue hl.fallbackHandler) hb)

theorem safeSetupPaymentSkip (p : SetupInput) (evm : EVM.State) {locals : Store}
    (hl : SetupLocals p locals) (hz : p.payment = ⟨0⟩) :
    ExecStmt fork config { contract := contract, locals := locals } evm setupPaymentStmt
      (.ok { contract := contract, locals := locals } evm) := by
  exact .iteFalse (by simpa only [hz, ne_self_iff_false, decide_false] using
    safeSetupPaymentCondition evm hl) .nil

theorem safeSetupPaymentCall (p : SetupInput) (evm : EVM.State) {locals : Store}
    {result : ExecResult} (hl : SetupLocals p locals) (hn : p.payment ≠ ⟨0⟩)
    (hb : ExecFuncBody fork config p.paymentInput.frame evm handlePaymentFunction.body result) :
    ExecStmt fork config { contract := contract, locals := locals } evm setupPaymentStmt
      (internalCallResult { contract := contract, locals := locals } "_paymentDone" result) := by
  apply ExecStmt.iteTrue (by
    have he := safeSetupPaymentCondition evm hl
    rw [decide_eq_true hn] at he
    exact he)
  apply execBlock_singleton
  exact safeInternalPayment (p := p.paymentInput) rfl rfl (evalLocalValue hl.payment)
    (by simp only [evalExpr?]; rfl) (by simp only [evalExpr?]; rfl)
    (evalLocalValue hl.paymentToken) (evalLocalValue hl.paymentReceiver) hb

end Benchmarks.Safe.ViaIR
