import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalSource

/-! Internal-call composition for the two approval overloads and the caller accessor. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

theorem approvalCall {locals imms : Store} {evm : State} {owner spender : AccountAddress}
    {value : UInt256} {emitEvent : Bool} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address owner, .address spender, uint256Value value, .bool emitEvent])
    (ho : owner ≠ ⟨0, by decide⟩) (hs : spender ≠ ⟨0, by decide⟩) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall "_approve_address_address_uint256_bool" args ret)
      (.ok ⟨contract, locals.insert ret .unit, imms⟩ (approvalState evm owner spender value)) :=
  internalCallFunctionReturn (callee := approvalFunction) hargs rfl rfl
    (approvalBody imms evm owner spender value emitEvent ho hs)

theorem approvalCallStatic {locals imms : Store} {evm : State} {owner spender : AccountAddress}
    {value : UInt256} {emitEvent : Bool} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address owner, .address spender, uint256Value value, .bool emitEvent])
    (ho : owner ≠ ⟨0, by decide⟩) (hs : spender ≠ ⟨0, by decide⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall "_approve_address_address_uint256_bool" args ret) .staticViolation :=
  ExecStmt.internalCallStatic (callee := approvalFunction.toCallable) hargs rfl rfl
    (approvalBodyStatic imms evm owner spender value emitEvent ho hs hperm)

theorem approvalCallReverts {locals imms : Store} {evm : State} {owner spender : AccountAddress}
    {value : UInt256} {emitEvent : Bool} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address owner, .address spender, uint256Value value, .bool emitEvent])
    (hbad : ¬ (owner ≠ ⟨0, by decide⟩ ∧ spender ≠ ⟨0, by decide⟩)) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall "_approve_address_address_uint256_bool" args ret) .reverted :=
  internalCallFunctionRevert (callee := approvalFunction) hargs rfl rfl
    (approvalBodyReverts imms evm owner spender value emitEvent hbad)

def approveFrame (imms : Store) (owner spender : AccountAddress) (value : UInt256) : Frame :=
  { contract := contract
    locals := (((∅ : Store).insert "value" (uint256Value value)).insert "spender"
      (.address spender)).insert "owner" (.address owner)
    immutables := imms }

theorem approveInternalArgs (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256) :
    evalExprs? config (approveFrame imms owner spender value) evm
      [.var "owner", .var "spender", .var "value", .boolLit true] =
      .ok [.address owner, .address spender, uint256Value value, .bool true] := by
  simp [evalExprs?, evalExpr?, approveFrame, Std.HashMap.getElem_insert,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem approveBody (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256)
    (ho : owner ≠ ⟨0, by decide⟩) (hs : spender ≠ ⟨0, by decide⟩) :
    ExecFuncBody config (approveFrame imms owner spender value) evm approveFunction.body
      (.returned { approveFrame imms owner spender value with
        locals := (approveFrame imms owner spender value).locals.insert "__c0" .unit }
        (approvalState evm owner spender value) none) := by
  apply ExecFuncBody.execBlockOK
  exact ExecBlock.consNormal (approvalCall (approveInternalArgs imms evm owner spender value)
    ho hs) ExecBlock.nil

theorem approveBodyStatic (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256)
    (ho : owner ≠ ⟨0, by decide⟩) (hs : spender ≠ ⟨0, by decide⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (approveFrame imms owner spender value) evm approveFunction.body
      .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  exact ExecBlock.consStatic (approvalCallStatic (approveInternalArgs imms evm owner spender value)
    ho hs hperm)

theorem approveBodyReverts (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256)
    (hbad : ¬ (owner ≠ ⟨0, by decide⟩ ∧ spender ≠ ⟨0, by decide⟩)) :
    ExecFuncBody config (approveFrame imms owner spender value) evm approveFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact ExecBlock.consRevert (approvalCallReverts (approveInternalArgs imms evm owner spender value)
    hbad)

theorem approveCall {locals imms : Store} {evm : State} {owner spender : AccountAddress}
    {value : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address owner, .address spender, uint256Value value])
    (ho : owner ≠ ⟨0, by decide⟩) (hs : spender ≠ ⟨0, by decide⟩) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_approve" args ret)
      (.ok ⟨contract, locals.insert ret .unit, imms⟩ (approvalState evm owner spender value)) :=
  internalCallFunctionReturn (callee := approveFunction) hargs rfl rfl
    (approveBody imms evm owner spender value ho hs)

theorem approveCallStatic {locals imms : Store} {evm : State} {owner spender : AccountAddress}
    {value : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address owner, .address spender, uint256Value value])
    (ho : owner ≠ ⟨0, by decide⟩) (hs : spender ≠ ⟨0, by decide⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_approve" args ret)
      .staticViolation :=
  ExecStmt.internalCallStatic (callee := approveFunction.toCallable) hargs rfl rfl
    (approveBodyStatic imms evm owner spender value ho hs hperm)

theorem approveCallReverts {locals imms : Store} {evm : State} {owner spender : AccountAddress}
    {value : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address owner, .address spender, uint256Value value])
    (hbad : ¬ (owner ≠ ⟨0, by decide⟩ ∧ spender ≠ ⟨0, by decide⟩)) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_approve" args ret) .reverted :=
  internalCallFunctionRevert (callee := approveFunction) hargs rfl rfl
    (approveBodyReverts imms evm owner spender value hbad)

theorem msgSenderCall (locals imms : Store) (evm : State) (ret : Ident) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_msgSender" [] ret)
      (.ok ⟨contract, locals.insert ret (.address evm.executionEnv.source), imms⟩ evm) := by
  apply internalCallFunctionReturn (callee := contract.functions[4]!) (argVals := [])
    (value := some [.address evm.executionEnv.source])
    (calleeSolm := ⟨contract, ∅, imms⟩) rfl rfl rfl
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, envValue, bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1
