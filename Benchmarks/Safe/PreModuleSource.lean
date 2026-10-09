import Benchmarks.Safe.ModuleStorage
import Reasoning.ExternalCall
import Reasoning.ABIViews
import Reasoning.SolmArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def preModuleArgs (target : EVM.Address) (value : UInt256) (payload : ByteArray)
    (operation : UInt256) : Store :=
  ((((∅ : Store).insert "operation" (.int (Int.ofNat operation.toNat))).insert
    "data" (.bytes payload)).insert "value" (.int (Int.ofNat value.toNat))).insert
      "to" (.address target)

def preModuleFrame (target : EVM.Address) (value : UInt256) (payload : ByteArray)
    (operation : UInt256) : Frame :=
  { contract := contract, locals := preModuleArgs target value payload operation }

def preModuleLocals (target : EVM.Address) (value : UInt256) (payload : ByteArray)
    (operation guard hash : UInt256) : Store :=
  ((preModuleArgs target value payload operation).insert
    "guard" (.address (AccountAddress.ofUInt256 guard))).insert
      "guardHash" (.fixedBytes bytes32Width (EVM.Word.toBytesBE hash))

def preModuleGuardWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner moduleGuardSlot

def preModuleCheck : Stmt :=
  .ite (neE (.var "guard") zeroAddr)
    [.externalCall (.var "guard") "checkModuleTransaction" (.intLit 0)
      [.var "to", .var "value", .var "data", .var "operation", sender] "guardHashCall",
      .assign .localVar (varRef "guardHash") (.var "guardHashCall")] []

def preModuleAuthorized (evm : EVM.State) : Prop :=
  UInt256.ofNat evm.executionEnv.source.val ≠ ⟨1⟩ ∧
    moduleLink evm (UInt256.ofNat evm.executionEnv.source.val) ≠ ⟨0⟩

instance (evm : EVM.State) : Decidable (preModuleAuthorized evm) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- GENERALIZES storageLocLoad_address_offset0 to assembly's full-slot address loads.
theorem storageLocLoad_address_word (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
      { slot := slot, offset := 0, size := 32, hbound := by decide, type := .address } =
      .address (AccountAddress.ofUInt256
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  have ht : (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0 32 =
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1 := by
    rw [List.extract_eq_take_drop, List.drop_zero]
    exact List.take_of_length_le (le_of_eq
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2)
  unfold storageLocLoad wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  change Value.address (AccountAddress.ofNat (fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0 32))) = _
  rw [ht, fromBytes'_toBytesLEWithSizeProof, accountAddress_ofUInt256_eq_ofNat_toNat]

theorem safePreModuleLoadGuard (evm : EVM.State) (locals : Store)
    (hb : locals["_moduleGuard"]? = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage moduleGuardRef) =
      .ok (.address (AccountAddress.ofUInt256 (preModuleGuardWord evm))) := by
  apply evalExpr_storage_scalar_value (er := { base := "_moduleGuard" })
    (loc := wordLoc moduleGuardSlot .address)
  · exact hb
  · simp [evalStorageRef, evalStorageRefSteps, moduleGuardRef, EvalResult.bind, bind, pure]
  · rfl
  · rfl
  · rfl
  · exact storageLocLoad_address_word evm moduleGuardSlot

theorem safePreModulePrefix (evm : EVM.State) (target : EVM.Address) (value : UInt256)
    (payload : ByteArray) (operation : UInt256) {result : ExecResult}
    (htail : ExecBlock config
      { contract := contract, locals :=
        preModuleLocals target value payload operation (preModuleGuardWord evm) ⟨0⟩ } evm
      [.require (andE (neE sender sentinelAddr) (neE (.storage (modulesRef sender)) zeroAddr)),
        preModuleCheck, .return [.var "guard", .var "guardHash"]] result) :
    ExecBlock config (preModuleFrame target value payload operation) evm
      preModuleExecutionFunction.body result := by
  refine .consNormal (.letDecl (safePreModuleLoadGuard evm _ ?_))
    (.consNormal (.letDecl ?_) htail)
  · simp [preModuleFrame, preModuleArgs, Std.HashMap.getElem_insert]
  · simp only [zeroBytes32, evalExpr?, pure]
    decide +kernel

theorem safePreModuleAuthorization (evm : EVM.State) (locals : Store)
    (hb : locals["modules"]? = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (andE (neE sender sentinelAddr) (neE (.storage (modulesRef sender)) zeroAddr)) =
      .ok (.bool (decide (preModuleAuthorized evm))) := by
  have he : evalExpr? config { contract := contract, locals := locals } evm sender =
      .ok (.address (AccountAddress.ofNat (UInt256.ofNat evm.executionEnv.source.val).toNat)) := by
    simp only [sender, evalExpr?, envValue, pure]
    congr 2
    rw [ulit_toNat' _ (lt_trans evm.executionEnv.source.isLt (by decide))]
    exact (Fin.ext (Nat.mod_eq_of_lt evm.executionEnv.source.isLt)).symm
  have hsent := evalAddressNe (sourceWord_canonical evm.executionEnv) (by decide)
    he (safeEvalModuleSentinel evm locals)
  have hlink := safeEvalModuleLink evm locals sender _ hb
    (sourceWord_canonical evm.executionEnv) he
  have hnonzero := evalAddressNe (solcAddrMask_result_canonical _) (by decide) hlink
    (show evalExpr? config { contract := contract, locals := locals } evm zeroAddr =
      .ok (.address (AccountAddress.ofNat (⟨0⟩ : UInt256).toNat)) by
      simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
        EvalResult.bind, bind, pure])
  rw [andE, evalExpr?, hsent]
  by_cases hs : UInt256.ofNat evm.executionEnv.source.val = ⟨1⟩ <;>
    simp [hs, hnonzero, preModuleAuthorized, moduleLink, EvalResult.bind, bind, pure]

def preModuleCheckingFrame (target : EVM.Address) (value : UInt256) (payload : ByteArray)
    (operation guard : UInt256) : Frame :=
  { contract := contract, locals := preModuleLocals target value payload operation guard ⟨0⟩ }

def preModuleCalledFrame (target : EVM.Address) (value : UInt256) (payload : ByteArray)
    (operation guard hash : UInt256) : Frame :=
  { contract := contract, locals :=
    ((preModuleLocals target value payload operation guard ⟨0⟩).insert
      "guardHashCall" (.fixedBytes bytes32Width (EVM.Word.toBytesBE hash))).insert
        "guardHash" (.fixedBytes bytes32Width (EVM.Word.toBytesBE hash)) }

theorem safePreModuleReceiver (evm : EVM.State) (target : EVM.Address) (value : UInt256)
    (payload : ByteArray) (operation guard : UInt256) :
    evalExpr? config (preModuleCheckingFrame target value payload operation guard) evm
      (.var "guard") = .ok (.address (AccountAddress.ofUInt256 guard)) := by
  simp [preModuleCheckingFrame, preModuleLocals, evalExpr?, EvalResult.ofOption,
    pure, Std.HashMap.getElem_insert]

theorem safePreModuleCondition (evm : EVM.State) (target : EVM.Address) (value : UInt256)
    (payload : ByteArray) (operation guard : UInt256) :
    evalExpr? config (preModuleCheckingFrame target value payload operation guard) evm
      (neE (.var "guard") zeroAddr) =
      .ok (.bool (decide (UInt256.land guard solcAddrMask ≠ ⟨0⟩))) := by
  apply evalAddressNe (solcAddrMask_result_canonical _) (by decide)
  · rw [← addressOfNat_eq_of_masked_word guard,
      ← accountAddress_ofUInt256_eq_ofNat_toNat]
    exact safePreModuleReceiver evm target value payload operation guard
  · simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
      EvalResult.bind, bind, pure]

theorem safePreModuleArguments (evm : EVM.State) (target : EVM.Address) (value : UInt256)
    (payload : ByteArray) (operation guard : UInt256) :
    evalExprs? config (preModuleCheckingFrame target value payload operation guard) evm
      [.var "to", .var "value", .var "data", .var "operation", sender] =
      .ok [.address target, .int (Int.ofNat value.toNat), .bytes payload,
        .int (Int.ofNat operation.toNat), .address evm.executionEnv.source] := by
  simp [preModuleCheckingFrame, preModuleLocals, preModuleArgs, evalExprs?, evalExpr?,
    sender, envValue, EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]

theorem safePreModuleCheckZero (evm : EVM.State) (target : EVM.Address) (value : UInt256)
    (payload : ByteArray) (operation guard : UInt256)
    (hz : UInt256.land guard solcAddrMask = ⟨0⟩) :
    ExecStmt config (preModuleCheckingFrame target value payload operation guard) evm
      preModuleCheck (.ok (preModuleCheckingFrame target value payload operation guard) evm) :=
  .iteFalse (by simpa only [hz, ne_eq, not_true_eq_false, decide_false] using
    safePreModuleCondition evm target value payload operation guard) .nil

theorem safePreModuleCheckFailed {evm evm' : EVM.State} {target : EVM.Address}
    {value operation guard : UInt256} {payload out : ByteArray}
    (hz : UInt256.land guard solcAddrMask ≠ ⟨0⟩)
    (hc : typedCallViaEVM config evm (EVM.address (AccountAddress.ofUInt256 guard))
      "checkModuleTransaction" 0 [.address target, .int (Int.ofNat value.toNat), .bytes payload,
        .int (Int.ofNat operation.toNat), .address evm.executionEnv.source] (false, evm', out)) :
    ExecStmt config (preModuleCheckingFrame target value payload operation guard) evm
      preModuleCheck .reverted := by
  apply ExecStmt.iteTrue (by
    simpa [hz] using
      safePreModuleCondition evm target value payload operation guard)
  exact .consRevert (.externalCallFailure (sendVal := 0)
    (safePreModuleReceiver evm target value payload operation guard) (by simp [evalExpr?, pure])
    (safePreModuleArguments evm target value payload operation guard) hc)

theorem safePreModuleCheckInvalid {evm evm' : EVM.State} {target : EVM.Address}
    {value operation guard : UInt256} {payload out : ByteArray}
    (hz : UInt256.land guard solcAddrMask ≠ ⟨0⟩)
    (hc : typedCallViaEVM config evm (EVM.address (AccountAddress.ofUInt256 guard))
      "checkModuleTransaction" 0 [.address target, .int (Int.ofNat value.toNat), .bytes payload,
        .int (Int.ofNat operation.toNat), .address evm.executionEnv.source] (true, evm', out))
    (hd : config.externalABI.decode? "checkModuleTransaction" out = none) :
    ExecStmt config (preModuleCheckingFrame target value payload operation guard) evm
      preModuleCheck .reverted := by
  apply ExecStmt.iteTrue (by
    simpa [hz] using
      safePreModuleCondition evm target value payload operation guard)
  exact .consRevert (.externalCallReturnDecodeRevert (sendVal := 0)
    (safePreModuleReceiver evm target value payload operation guard) (by simp [evalExpr?, pure])
    (safePreModuleArguments evm target value payload operation guard) hc hd)

theorem safePreModuleCheckSuccess {evm evm' : EVM.State} {target : EVM.Address}
    {value operation guard hash : UInt256} {payload out : ByteArray}
    (hz : UInt256.land guard solcAddrMask ≠ ⟨0⟩)
    (hc : typedCallViaEVM config evm (EVM.address (AccountAddress.ofUInt256 guard))
      "checkModuleTransaction" 0 [.address target, .int (Int.ofNat value.toNat), .bytes payload,
        .int (Int.ofNat operation.toNat), .address evm.executionEnv.source] (true, evm', out))
    (hd : config.externalABI.decode? "checkModuleTransaction" out =
      some [.fixedBytes bytes32Width (EVM.Word.toBytesBE hash)]) :
    ExecStmt config (preModuleCheckingFrame target value payload operation guard) evm
      preModuleCheck
        (.ok (preModuleCalledFrame target value payload operation guard hash) evm') := by
  apply ExecStmt.iteTrue (by
    simpa [hz] using
      safePreModuleCondition evm target value payload operation guard)
  refine .consNormal (.externalCallSuccess (sendVal := 0)
    (safePreModuleReceiver evm target value payload operation guard) (by simp [evalExpr?, pure])
    (safePreModuleArguments evm target value payload operation guard) hc hd)
    (.consNormal (.assign (value := .fixedBytes bytes32Width (EVM.Word.toBytesBE hash))
      (by simp [evalExpr?, EvalResult.ofOption, collapseReturns]) ?_) .nil)
  apply assignLocalVarBase_ok (old := .fixedBytes bytes32Width (EVM.Word.toBytesBE ⟨0⟩))
  simp [preModuleCheckingFrame, preModuleLocals, Std.HashMap.getElem_insert]

theorem safePreModuleUnauthorized (evm : EVM.State) (target : EVM.Address) (value : UInt256)
    (payload : ByteArray) (operation : UInt256) (ha : ¬preModuleAuthorized evm) :
    ExecFuncBody config (preModuleFrame target value payload operation) evm
      preModuleExecutionFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply safePreModulePrefix
  exact .consRevert (.requireFalse (by
    simpa only [ha, decide_false] using
      safePreModuleAuthorization evm _ (by
        simp [preModuleLocals, preModuleArgs, Std.HashMap.getElem_insert])))

theorem safePreModuleSourceRevert {evm : EVM.State} {target : EVM.Address}
    {value operation : UInt256} {payload : ByteArray} (ha : preModuleAuthorized evm)
    (hc : ExecStmt config
      (preModuleCheckingFrame target value payload operation (preModuleGuardWord evm)) evm
      preModuleCheck .reverted) :
    ExecFuncBody config (preModuleFrame target value payload operation) evm
      preModuleExecutionFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply safePreModulePrefix
  exact .consNormal (.requireTrue (by
    simpa only [ha, decide_true] using
      safePreModuleAuthorization evm _ (by
        simp [preModuleLocals, preModuleArgs, Std.HashMap.getElem_insert]))) (.consRevert hc)

theorem safePreModuleSourceReturn {evm evm' : EVM.State} {target : EVM.Address}
    {value operation hash : UInt256} {payload : ByteArray} {frame : Frame}
    (ha : preModuleAuthorized evm)
    (hc : ExecStmt config
      (preModuleCheckingFrame target value payload operation (preModuleGuardWord evm)) evm
      preModuleCheck (.ok frame evm'))
    (hg : frame.locals["guard"]? =
      some (.address (AccountAddress.ofUInt256 (preModuleGuardWord evm))))
    (hh : frame.locals["guardHash"]? =
      some (.fixedBytes bytes32Width (EVM.Word.toBytesBE hash))) :
    ExecFuncBody config (preModuleFrame target value payload operation) evm
      preModuleExecutionFunction.body (.returned frame evm'
        (some [.address (AccountAddress.ofUInt256 (preModuleGuardWord evm)),
          .fixedBytes bytes32Width (EVM.Word.toBytesBE hash)])) := by
  apply ExecFuncBody.execBlockRet
  apply safePreModulePrefix
  refine .consNormal (.requireTrue (by
    simpa only [ha, decide_true] using
      safePreModuleAuthorization evm _ (by
        simp [preModuleLocals, preModuleArgs, Std.HashMap.getElem_insert])))
    (.consNormal hc (.consReturn (.return ?_)))
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure, hg, hh]

end Benchmarks.Safe
