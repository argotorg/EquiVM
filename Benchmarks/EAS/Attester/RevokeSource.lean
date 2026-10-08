import Benchmarks.EAS.Attester.Decode
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

def revokeLocals (schema uid : UInt256) : Store :=
  (((∅ : Store).insert "schema" (wordBytes32Value schema)).insert "uid" (wordBytes32Value uid))

theorem attesterRevokeDecode {cd : ByteArray} (hlen : 68 ≤ cd.size)
    (hhi : cd.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode config.abiDecodeMode (revokeTransition.params.map Param.name)
      (transitionSignature revokeTransition).paramTypes cd =
        some (revokeLocals (calldataWord cd 4) (calldataWord cd 36)) := by
  have hlenList : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have h0 := decodeABIValue_bytes32_ok (bytes := cd.toList.drop 4) (start := 0)
    (by simp only [List.drop_zero, List.length_take, List.length_drop, hlenList]; omega)
  have h32 := decodeABIValue_bytes32_ok (bytes := cd.toList.drop 4) (start := 32)
    (by simp only [List.length_take, List.length_drop, hlenList]; omega)
  have hd := decodeCalldata_twoWords_ok (x := "schema") (y := "uid")
    (by rfl) (by rfl) (by rfl) (by rfl) hlen hhi h0 h32
  simpa only [List.drop_zero, List.drop_drop, Nat.reduceAdd,
    calldata_bytes32_value (cd := cd) (off := 4) (by omega) (by decide),
    calldata_bytes32_value (cd := cd) (off := 36) (by omega) (by decide)] using hd

theorem attesterRevokeDecodeShort {cd : ByteArray} (hshort : cd.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (revokeTransition.params.map Param.name)
      (transitionSignature revokeTransition).paramTypes cd = none :=
  decodeCalldata_head_none_short (headSize := 64) (by native_decide) hshort

theorem attesterRevokeDecodeHuge {cd : ByteArray} (hhi : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldataWithMode config.abiDecodeMode (revokeTransition.params.map Param.name)
      (transitionSignature revokeTransition).paramTypes cd = none :=
  decodeCalldata_nonempty_none_huge hhi

def revokeRequest (schema uid : UInt256) : Value :=
  .tuple [wordBytes32Value schema, .tuple [wordBytes32Value uid, .int 0]]

def revokeFrame (imms : Store) (schema uid : UInt256) : Frame :=
  ⟨contract, revokeLocals schema uid, imms⟩

def revokeCallFrame (imms : Store) (eas : EVM.Address) (schema uid : UInt256) : Frame :=
  { revokeFrame imms schema uid with locals :=
      (revokeLocals schema uid).insert "eas" (.address eas) }

def revokeFinalFrame (imms : Store) (eas : EVM.Address) (schema uid : UInt256) : Frame :=
  { revokeCallFrame imms eas schema uid with
    locals := (revokeCallFrame imms eas schema uid).locals.insert "_revoke" Value.unit }

theorem revokeSourcePrefix {imms : Store} {eas : EVM.Address} {schema uid : UInt256}
    {evm : State} {result : ExecResult} (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hget : imms.get? "_eas" = some (.address eas))
    (hrest : ExecBlock config (revokeCallFrame imms eas schema uid) evm
      (revokeTransition.body.drop 2) result) :
    ExecBlock config (revokeFrame imms schema uid) evm revokeTransition.body result := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl ?_) hrest
  change evalExpr? config (revokeFrame imms schema uid) evm (.immutable "_eas") = _
  simp only [evalExpr?, revokeFrame, hget, EvalResult.ofOption]

theorem revokeSourceReceiver {imms : Store} {eas : EVM.Address} {schema uid : UInt256}
    {evm : State} :
    evalExpr? config (revokeCallFrame imms eas schema uid) evm (.var "eas") =
      .ok (.address eas) := by
  simp [evalExpr?, revokeCallFrame, EvalResult.ofOption]

theorem revokeSourceArgs {imms : Store} {eas : EVM.Address} {schema uid : UInt256}
    {evm : State} :
    evalExprs? config (revokeCallFrame imms eas schema uid) evm
      [.tupleLit [.var "schema", .tupleLit [.var "uid", .intLit 0]]] =
        .ok [revokeRequest schema uid] := by
  simp [evalExprs?, evalExprList?, evalExpr?, revokeCallFrame, revokeLocals, revokeRequest,
    EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]

theorem revokeSourceNoCode {imms : Store} {eas : EVM.Address} {schema uid : UInt256}
    {evm : State} (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hget : imms.get? "_eas" = some (.address eas))
    (hguard : evalExpr? config (revokeCallFrame imms eas schema uid) evm
      (.binary .gt (.extCodeSize (.var "eas")) (.intLit 0)) = .ok (.bool false)) :
    ExecTransitionBody config contract evm (revokeLocals schema uid) revokeTransition.body
      .reverted imms :=
  .execBlockRevert (revokeSourcePrefix hvalue hget
    (ExecBlock.consRevert (ExecStmt.requireFalse hguard)))

theorem revokeSourceFailure {imms : Store} {eas : EVM.Address} {schema uid : UInt256}
    {evm evm' : State} {out : ByteArray} (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hget : imms.get? "_eas" = some (.address eas))
    (hguard : evalExpr? config (revokeCallFrame imms eas schema uid) evm
      (.binary .gt (.extCodeSize (.var "eas")) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm eas "revoke" 0 [revokeRequest schema uid]
      (false, evm', out)) :
    ExecTransitionBody config contract evm (revokeLocals schema uid) revokeTransition.body
      .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply revokeSourcePrefix hvalue hget
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact ExecBlock.consRevert (ExecStmt.externalCallFailure (sendVal := 0) revokeSourceReceiver
    (by simp only [evalExpr?, pure]) revokeSourceArgs
    (by simpa only [address_of_val] using hcall))

theorem revokeSourceSuccess {imms : Store} {eas : EVM.Address} {schema uid : UInt256}
    {evm evm' : State} {out : ByteArray} (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hget : imms.get? "_eas" = some (.address eas))
    (hguard : evalExpr? config (revokeCallFrame imms eas schema uid) evm
      (.binary .gt (.extCodeSize (.var "eas")) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm eas "revoke" 0 [revokeRequest schema uid]
      (true, evm', out)) :
    ExecTransitionBody config contract evm (revokeLocals schema uid) revokeTransition.body
      (.returned (revokeFinalFrame imms eas schema uid) evm' none) imms := by
  apply ExecFuncBody.execBlockOK
  apply revokeSourcePrefix hvalue hget
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact ExecBlock.consNormal (ExecStmt.externalCallSuccess (sendVal := 0) (value := [])
    revokeSourceReceiver
    (by simp only [evalExpr?, pure]) revokeSourceArgs
    (by simpa only [address_of_val] using hcall) (by rfl)) ExecBlock.nil

end Benchmarks.EAS.Attester
