import Benchmarks.CurveVault.TokenReturnSource
import Benchmarks.CurveVault.TokenMemory

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultTokenFunction : FunctionDecl := contract.functions[30]!

def vaultTokenLocals (token : AccountAddress) (sender recipient amount : UInt256) : Store :=
  ((((∅ : Store).insert "amount" (.int (Int.ofNat amount.toNat))).insert
    "_to" (.int (Int.ofNat recipient.toNat))).insert
    "_from" (.int (Int.ofNat sender.toNat))).insert "token" (.address token)

def vaultTokenCalledLocals (locals : Store) (sender recipient amount : UInt256)
    (z : Bool) (out : ByteArray) : Store :=
  ((locals.insert "payload" (.bytes (vaultTokenPayload sender recipient amount))).insert
    "success" (.bool z)).insert "returned" (.bytes out)

theorem vaultTokenPayloadEval (evm : State) (locals : Store) (sender recipient amount : UInt256)
    (hf : locals.get? "_from" = some (.int (Int.ofNat sender.toNat)))
    (ht : locals.get? "_to" = some (.int (Int.ofNat recipient.toNat)))
    (ha : locals.get? "amount" = some (.int (Int.ofNat amount.toNat))) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.abiEncodeCall "transferFrom" [.var "_from", .var "_to", .var "amount"]) =
      .ok (.bytes (vaultTokenPayload sender recipient amount)) := by
  rw [evalExpr?]
  simp only [evalExprList?, evalExpr?, hf, ht, ha, EvalResult.ofOption,
    EvalResult.bind, bind, pure, vaultTokenPayload_encode]

theorem vaultTokenSourceZero (evm : State) (locals : Store)
    (ha : locals.get? "amount" = some (.int 0)) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm vaultTokenFunction.body
      (.returned {contract := contract, locals := locals} evm none) := by
  apply ExecFuncBody.execBlockOK
  apply ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ExecBlock.nil
  exact evalExpr_uint256_var_positive evm "amount" ⟨0⟩ ha

theorem vaultTokenSourceCallStmt (evm evm' : State) (locals : Store)
    (token sender recipient amount : UInt256) (z : Bool) (out : ByteArray) (result : ExecResult)
    (htoken : locals.get? "token" = some (.address (AccountAddress.ofUInt256 token)))
    (hf : locals.get? "_from" = some (.int (Int.ofNat sender.toNat)))
    (ht : locals.get? "_to" = some (.int (Int.ofNat recipient.toNat)))
    (ha : locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hpos : 0 < amount.toNat)
    (hcall : callViaEVM fork evm (AccountAddress.ofUInt256 token) 0
      (vaultTokenPayload sender recipient amount) (z, evm', out))
    (hrest : ExecBlock fork config
      {contract := contract, locals := vaultTokenCalledLocals locals sender recipient amount z out} evm'
      [.require (.var "success"), vaultTokenReturnStmt] result) :
    ExecStmt fork config {contract := contract, locals := locals} evm vaultTokenFunction.body[0]! result := by
  apply ExecStmt.iteTrue
    (by simpa only [hpos, decide_true] using evalExpr_uint256_var_positive evm "amount" amount ha)
  apply ExecBlock.consNormal (ExecStmt.letDecl (vaultTokenPayloadEval evm locals sender recipient amount hf ht ha))
  apply ExecBlock.consNormal ?_ hrest
  refine lowLevelCallSource (cfg := config)
    (frame := {contract := contract, locals := locals.insert "payload" (.bytes (vaultTokenPayload sender recipient amount))})
    (hperm := Or.inl rfl) ?_ (by rw [evalExpr?]; rfl) ?_ hcall
  · have hg : (locals.insert "payload" (.bytes (vaultTokenPayload sender recipient amount))).get? "token" =
        some (.address (AccountAddress.ofUInt256 token)) := by
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      exact htoken
    rw [evalExpr?]
    simp only [hg, EvalResult.ofOption]
  · rw [evalExpr?]
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self, EvalResult.ofOption]

theorem vaultTokenSourceSuccess {s0 evm evm' : State} {I : ExecutionEnv} {σ' : AccountMap}
    (hs' : SourceState s0 I σ' evm') (locals : Store) (token sender recipient amount : UInt256)
    (out : ByteArray)
    (htoken : locals.get? "token" = some (.address (AccountAddress.ofUInt256 token)))
    (hf : locals.get? "_from" = some (.int (Int.ofNat sender.toNat)))
    (ht : locals.get? "_to" = some (.int (Int.ofNat recipient.toNat)))
    (ha : locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hpos : 0 < amount.toNat)
    (hcall : callViaEVM fork evm (AccountAddress.ofUInt256 token) 0
      (vaultTokenPayload sender recipient amount) (true, evm', out))
    (haccept : vaultTokenReturnAccepted σ' token out) :
    ∃ locals', ExecFuncBody fork config {contract := contract, locals := locals} evm vaultTokenFunction.body
      (.returned {contract := contract, locals := locals'} evm' none) := by
  let afterCall := vaultTokenCalledLocals locals sender recipient amount true out
  obtain ⟨locals', hreturn⟩ := vaultTokenReturnSourceSuccess hs' afterCall token out
    (by simp only [afterCall, vaultTokenCalledLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; exact htoken)
    (by simp [afterCall, vaultTokenCalledLocals]) haccept
  refine ⟨locals', ExecFuncBody.execBlockOK (ExecBlock.consNormal
    (vaultTokenSourceCallStmt evm evm' locals token sender recipient amount true out _
      htoken hf ht ha hpos hcall ?_) ExecBlock.nil)⟩
  exact ExecBlock.consNormal (ExecStmt.requireTrue (by
    simp only [vaultTokenCalledLocals, evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl))
    (ExecBlock.consNormal hreturn ExecBlock.nil)

theorem vaultTokenSourceCallFailure (evm evm' : State) (locals : Store)
    (token sender recipient amount : UInt256) (out : ByteArray)
    (htoken : locals.get? "token" = some (.address (AccountAddress.ofUInt256 token)))
    (hf : locals.get? "_from" = some (.int (Int.ofNat sender.toNat)))
    (ht : locals.get? "_to" = some (.int (Int.ofNat recipient.toNat)))
    (ha : locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hpos : 0 < amount.toNat)
    (hcall : callViaEVM fork evm (AccountAddress.ofUInt256 token) 0
      (vaultTokenPayload sender recipient amount) (false, evm', out)) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm vaultTokenFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  apply vaultTokenSourceCallStmt evm evm' locals token sender recipient amount false out _ htoken hf ht ha hpos hcall
  exact ExecBlock.consRevert (ExecStmt.requireFalse (by
    simp only [vaultTokenCalledLocals, evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl))

theorem vaultTokenSourceReturnFailure {s0 evm evm' : State} {I : ExecutionEnv} {σ' : AccountMap}
    (hs' : SourceState s0 I σ' evm') (locals : Store) (token sender recipient amount : UInt256)
    (out : ByteArray)
    (htoken : locals.get? "token" = some (.address (AccountAddress.ofUInt256 token)))
    (hf : locals.get? "_from" = some (.int (Int.ofNat sender.toNat)))
    (ht : locals.get? "_to" = some (.int (Int.ofNat recipient.toNat)))
    (ha : locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hpos : 0 < amount.toNat)
    (hcall : callViaEVM fork evm (AccountAddress.ofUInt256 token) 0
      (vaultTokenPayload sender recipient amount) (true, evm', out))
    (hreject : ¬ vaultTokenReturnAccepted σ' token out) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm vaultTokenFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  apply vaultTokenSourceCallStmt evm evm' locals token sender recipient amount true out _ htoken hf ht ha hpos hcall
  apply ExecBlock.consNormal (ExecStmt.requireTrue (by
    simp only [vaultTokenCalledLocals, evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl))
  apply ExecBlock.consRevert (vaultTokenReturnSourceRevert hs' _ token out ?_ ?_ hreject)
  · simp only [vaultTokenCalledLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    exact htoken
  · simp [vaultTokenCalledLocals]

end Benchmarks.CurveVault
