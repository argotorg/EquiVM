import Benchmarks.Safe.GuardKind
import Benchmarks.Safe.Authorization
import Benchmarks.Safe.ModuleStorage
import Reasoning.ExternalCall
import Reasoning.ABIComposite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def guardArgs (kind : GuardKind) (guard : UInt256) : Store :=
  (∅ : Store).insert (guardName kind) (.address (AccountAddress.ofNat guard.toNat))

def guardFrame (kind : GuardKind) (guard : UInt256) : Frame :=
  { contract := contract, locals := guardArgs kind guard }

def guardCheck (kind : GuardKind) : Stmt :=
  .ite (neE (.var (guardName kind)) zeroAddr)
    [.externalCall (.var (guardName kind)) "supportsInterface" (.intLit 0)
      [guardInterfaceExpr kind] "supported" (perm := false), .require (.var "supported")] []

theorem guardTransition_body (kind : GuardKind) :
    (guardTransition kind).body = nonpayable ++ authorized ++
      [guardCheck kind, .assign .storage (guardStorageRef kind) (.var (guardName kind)),
        .emit (guardEvent kind) [.var (guardName kind)]] := by
  cases kind <;> rfl

variable {kind : GuardKind}

-- Shared source semantics for the transaction guard and module guard setters.
theorem safeEvalGuard (evm : EVM.State) (guard : UInt256) :
    evalExpr? config (guardFrame kind guard) evm (.var (guardName kind)) =
      .ok (.address (AccountAddress.ofNat guard.toNat)) := by
  simp [guardFrame, guardArgs, evalExpr?, EvalResult.ofOption]

theorem safeGuardCondition (evm : EVM.State) (guard : UInt256)
    (hc : guard.toNat < EVM.addressModulus) :
    evalExpr? config (guardFrame kind guard) evm (neE (.var (guardName kind)) zeroAddr) =
      .ok (.bool (decide (guard ≠ ⟨0⟩))) := by
  apply evalAddressNe hc (by decide) (safeEvalGuard evm guard)
  simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem safeGuardInterface (evm : EVM.State) (frame : Frame) :
    evalExprs? config frame evm [guardInterfaceExpr kind] = .ok [guardInterfaceValue kind] := by
  cases kind <;> simp [guardInterfaceExpr, evalExprs?, evalExpr?,
    transactionGuardInterfaceId, moduleGuardInterfaceId, fixedBytes4Lit,
    guardInterfaceValue, EvalResult.bind, bind, pure]

theorem safeGuardCheckZero (evm : EVM.State) :
    ExecStmt config (guardFrame kind ⟨0⟩) evm (guardCheck kind)
      (.ok (guardFrame kind ⟨0⟩) evm) := by
  exact .iteFalse (by simpa using safeGuardCondition evm ⟨0⟩ (by decide)) .nil

theorem safeGuardCheckFailed {evm evm' : EVM.State} {guard : UInt256} {out : ByteArray}
    (hc : guard.toNat < EVM.addressModulus) (hz : guard ≠ ⟨0⟩)
    (hcall : typedCallViaEVM config evm (AccountAddress.ofNat guard.toNat)
      "supportsInterface" 0 [guardInterfaceValue kind] (false, evm', out) false) :
    ExecStmt config (guardFrame kind guard) evm (guardCheck kind) .reverted := by
  exact .iteTrue (by simpa [hz] using safeGuardCondition evm guard hc)
    (.consRevert (.externalCallFailure (sendVal := 0) (safeEvalGuard evm guard)
      (by simp [evalExpr?, pure])
      (safeGuardInterface evm _) (by simpa only [addressOfAddress] using hcall)))

theorem safeGuardCheckInvalid {evm evm' : EVM.State} {guard : UInt256} {out : ByteArray}
    (hc : guard.toNat < EVM.addressModulus) (hz : guard ≠ ⟨0⟩)
    (hcall : typedCallViaEVM config evm (AccountAddress.ofNat guard.toNat)
      "supportsInterface" 0 [guardInterfaceValue kind] (true, evm', out) false)
    (hdecode : config.externalABI.decode? "supportsInterface" out = none) :
    ExecStmt config (guardFrame kind guard) evm (guardCheck kind) .reverted := by
  exact .iteTrue (by simpa [hz] using safeGuardCondition evm guard hc)
    (.consRevert (.externalCallReturnDecodeRevert (sendVal := 0) (safeEvalGuard evm guard)
      (by simp [evalExpr?, pure])
      (safeGuardInterface evm _) (by simpa only [addressOfAddress] using hcall) hdecode))

theorem safeGuardCheckFalse {evm evm' : EVM.State} {guard : UInt256} {out : ByteArray}
    (hc : guard.toNat < EVM.addressModulus) (hz : guard ≠ ⟨0⟩)
    (hcall : typedCallViaEVM config evm (AccountAddress.ofNat guard.toNat)
      "supportsInterface" 0 [guardInterfaceValue kind] (true, evm', out) false)
    (hdecode : config.externalABI.decode? "supportsInterface" out = some [.bool false]) :
    ExecStmt config (guardFrame kind guard) evm (guardCheck kind) .reverted := by
  exact .iteTrue (by simpa [hz] using safeGuardCondition evm guard hc)
    (.consNormal (.externalCallSuccess (sendVal := 0) (safeEvalGuard evm guard)
      (by simp [evalExpr?, pure])
      (safeGuardInterface evm _) (by simpa only [addressOfAddress] using hcall) hdecode)
      (.consRevert (.requireFalse (by
        simp [evalExpr?, EvalResult.ofOption, collapseReturns]))))

theorem safeGuardCheckTrue {evm evm' : EVM.State} {guard : UInt256} {out : ByteArray}
    (hc : guard.toNat < EVM.addressModulus) (hz : guard ≠ ⟨0⟩)
    (hcall : typedCallViaEVM config evm (AccountAddress.ofNat guard.toNat)
      "supportsInterface" 0 [guardInterfaceValue kind] (true, evm', out) false)
    (hdecode : config.externalABI.decode? "supportsInterface" out = some [.bool true]) :
    ExecStmt config (guardFrame kind guard) evm (guardCheck kind)
      (.ok { contract := contract, locals :=
          (guardArgs kind guard).insert "supported" (.bool true) }
        evm') := by
  exact .iteTrue (by simpa [hz] using safeGuardCondition evm guard hc)
    (.consNormal (.externalCallSuccess (sendVal := 0) (safeEvalGuard evm guard)
      (by simp [evalExpr?, pure])
      (safeGuardInterface evm _) (by simpa only [addressOfAddress] using hcall) hdecode)
      (.consNormal (.requireTrue (by
        simp [evalExpr?, EvalResult.ofOption, collapseReturns])) .nil))

theorem safeAssignGuard (evm : EVM.State) (locals : Store) (guard : UInt256)
    (hc : guard.toNat < EVM.addressModulus) (hb : locals.get? (guardField kind) = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (guardStorageRef kind)
      (.address (AccountAddress.ofNat guard.toNat)) =
      .ok ({ contract := contract, locals := locals },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (guardStorageSlot kind) guard) := by
  apply assignStorageRef_storage_scalar_value (er := { base := (guardField kind) })
    (ty := .elem .address) (layout := storageLayout)
    (loc := wordLoc (guardStorageSlot kind) .address)
  · exact hb
  · simp [evalStorageRef, evalStorageRefSteps, guardStorageRef, EvalResult.bind, bind, pure]
  · cases kind <;> rfl
  · rfl
  · cases kind <;> rfl
  · exact .inl ⟨.address, rfl⟩
  · exact storageLocStore_bytes32 evm (guardStorageSlot kind) guard _
      (valueToWord_address_ofNat_canonical guard hc)

theorem safeGuardSourceSuccess {evm evm' : EVM.State} {guard : UInt256} {locals : Store}
    (hc : guard.toNat < EVM.addressModulus)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (ha : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hg : locals[(guardName kind)]? = some (.address (AccountAddress.ofNat guard.toNat)))
    (hb : locals.get? (guardField kind) = none)
    (hcheck : ExecStmt config (guardFrame kind guard) evm (guardCheck kind)
      (.ok { contract := contract, locals := locals } evm')) :
    ExecTransitionBody config contract evm (guardArgs kind guard) (guardTransition kind).body
      (.returned { contract := contract, locals := locals }
        (Solm.EVM.storageStore evm' evm'.executionEnv.codeOwner (guardStorageSlot kind) guard)
        none) := by
  rw [guardTransition_body]
  have he : evalExpr? config { contract := contract, locals := locals } evm'
      (.var (guardName kind)) =
      .ok (.address (AccountAddress.ofNat guard.toNat)) := by
    simp [evalExpr?, EvalResult.ofOption, hg]
  refine .execBlockOK (.consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.requireTrue (by simpa [ha] using safeEvalAuthorized evm _))
      (.consNormal hcheck (.consNormal (.assign he (safeAssignGuard evm' locals guard hc hb))
        (.consNormal (.emit (vals := [.address (AccountAddress.ofNat guard.toNat)]) ?_) .nil)))))
  apply evalExprs?_singleton
  simp [evalExpr?, EvalResult.ofOption, hg]

theorem safeGuardSourceStatic {evm evm' : EVM.State} {guard : UInt256} {locals : Store}
    (hc : guard.toNat < EVM.addressModulus)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (ha : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hg : locals[(guardName kind)]? = some (.address (AccountAddress.ofNat guard.toNat)))
    (hb : locals.get? (guardField kind) = none) (hperm : evm'.executionEnv.perm = false)
    (hcheck : ExecStmt config (guardFrame kind guard) evm (guardCheck kind)
      (.ok { contract := contract, locals := locals } evm')) :
    ExecTransitionBody config contract evm (guardArgs kind guard) (guardTransition kind).body
      .staticViolation := by
  rw [guardTransition_body]
  have he : evalExpr? config { contract := contract, locals := locals } evm'
      (.var (guardName kind)) =
      .ok (.address (AccountAddress.ofNat guard.toNat)) := by
    simp [evalExpr?, EvalResult.ofOption, hg]
  exact .execBlockStatic (.consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.requireTrue (by simpa [ha] using safeEvalAuthorized evm _))
      (.consNormal hcheck
        (.consStatic (.assignStatic he (safeAssignGuard evm' locals guard hc hb) hperm)))))

theorem safeGuardSourceRevert {evm : EVM.State} {guard : UInt256}
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (ha : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hcheck : ExecStmt config (guardFrame kind guard) evm (guardCheck kind) .reverted) :
    ExecTransitionBody config contract evm (guardArgs kind guard) (guardTransition kind).body
      .reverted := by
  rw [guardTransition_body]
  exact .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.requireTrue (by simpa [ha] using safeEvalAuthorized evm _))
      (.consRevert hcheck)))

theorem safeGuardSourceUnauthorized {evm : EVM.State} (locals : Store)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (ha : evm.executionEnv.source ≠ evm.executionEnv.codeOwner) :
    ExecTransitionBody config contract evm locals (guardTransition kind).body
      .reverted := by
  rw [guardTransition_body]
  exact .execBlockRevert (nonpayableSecondRequireReverts hv
    (by simpa [ha] using safeEvalAuthorized evm _))

theorem safeGuardDecodeLong {out : ByteArray} (hl : 32 ≤ out.size) (hb : out.size < 2 ^ 255) :
    config.externalABI.decode? "supportsInterface" out =
      if calldataWord out 0 = ⟨0⟩ then some [.bool false]
      else if calldataWord out 0 = ⟨1⟩ then some [.bool true] else none := by
  change (ABI.decodeReturnValue? abiBool out).map (fun v ↦ [v]) = _
  rw [decodeReturnBool_long hl hb]
  split
  · rfl
  · split <;> rfl

theorem safeGuardDecodeShort {out : ByteArray} (hl : out.size < 32) :
    config.externalABI.decode? "supportsInterface" out = none := by
  change (ABI.decodeReturnValue? abiBool out).map (fun v ↦ [v]) = _
  rw [decodeReturnBool_short hl]
  rfl

end Benchmarks.Safe
