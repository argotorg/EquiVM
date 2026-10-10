import Benchmarks.Morpho.MetaMorphoV1_1.PackedDeletion

/-! The guardian setter stores its value, emits its event, and clears the pending record. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

abbrev setGuardianFunction : FunctionDecl := contract.functions[5]!

def setGuardianFrame (imms : Store) (value : AccountAddress) : Frame :=
  { contract := contract
    locals := (∅ : Store).insert "newGuardian" (.address value)
    immutables := imms }

def setGuardianValueState (evm : EVM.State) (value : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨12⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩)
      (UInt256.ofNat value.val))

def setGuardianState (evm : EVM.State) (value : AccountAddress) : EVM.State :=
  let changed := setGuardianValueState evm value
  Solm.EVM.storageStore changed changed.executionEnv.codeOwner ⟨15⟩ ⟨0⟩

def setGuardianFinalFrame (evm : EVM.State) (imms : Store) (value : AccountAddress) : Frame :=
  { contract := contract
    locals := (setGuardianFrame imms value).locals.insert "__c0"
      (.address (setGuardianValueState evm value).executionEnv.source)
    immutables := imms }

theorem setGuardianAssign (evm : EVM.State) (imms : Store) (value : AccountAddress) :
    ExecStmt config (setGuardianFrame imms value) evm
      (.assign .storage ⟨"guardian", []⟩ (.var "newGuardian"))
      (.ok (setGuardianFrame imms value) (setGuardianValueState evm value)) := by
  apply ExecStmt.assign (value := .address value)
  · simp [evalExpr?, setGuardianFrame, EvalResult.ofOption]
  · exact assignStorageRef_storage_scalar_value (er := ⟨"guardian", []⟩)
      (ty := .elem .address)
      (by simp [setGuardianFrame])
      (by simp [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure])
      rfl rfl rfl (.inl ⟨_, rfl⟩) (by
        have h := storageLocStore_address_offset0 evm ⟨12⟩ (UInt256.ofNat value.val)
          (addressWord_val_canonical value)
        have ha : AccountAddress.ofNat (UInt256.ofNat value.val).toNat = value :=
          accountAddress_of_word_val value
        rw [ha] at h
        exact h)

theorem setGuardianBody (evm : EVM.State) (imms : Store) (value : AccountAddress) :
    ExecFuncBody config (setGuardianFrame imms value) evm setGuardianFunction.body
      (.returned (setGuardianFinalFrame evm imms value) (setGuardianState evm value) none) := by
  apply ExecFuncBody.execBlockOK
  refine ExecBlock.consNormal (setGuardianAssign evm imms value) ?_
  refine ExecBlock.consNormal
    (internalCallReturnExpr (retTy := [.elem .address]) (expr := .env .caller)
      (value := .address (setGuardianValueState evm value).executionEnv.source)
      rfl (by simp only [evalExpr?, envValue, pure])) ?_
  apply (ABlock.start.emitStep (vals := [
    .address (setGuardianValueState evm value).executionEnv.source, .address value]) ?_).run
  · exact ExecBlock.consNormal (ExecStmt.delete (deleteStorage_pendingGuardian _ _ imms
      (by simp [setGuardianFrame]))) ExecBlock.nil
  · simp only [evalExprs?, evalExpr?, setGuardianFrame, store_get_self,
      store_get_ne _ _ (by decide : ("__c0" == "newGuardian") = false),
      EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem setGuardianBodyStatic (evm : EVM.State) (imms : Store) (value : AccountAddress)
    (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (setGuardianFrame imms value) evm setGuardianFunction.body
      .staticViolation := by
  exact ExecFuncBody.execBlockStatic (ExecBlock.consStatic
    (execStmt_assign_static (setGuardianAssign evm imms value) hperm))

theorem setGuardianCall (evm : EVM.State) (locals imms : Store) (value : AccountAddress)
    (arg : Expr) (retVar : Ident)
    (heval : evalExpr? config ⟨contract, locals, imms⟩ evm arg = .ok (.address value)) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_setGuardian" [arg] retVar)
      (.ok ⟨contract, locals.insert retVar .unit, imms⟩ (setGuardianState evm value)) := by
  exact internalCallFunctionReturn (caller := ⟨contract, locals, imms⟩)
    (callee := setGuardianFunction) (argVals := [.address value]) (value := none)
    (by simp only [evalExprs?, heval, bind, EvalResult.bind, pure]) rfl rfl
    (setGuardianBody evm imms value)

theorem setGuardianCallStatic (evm : EVM.State) (locals imms : Store) (value : AccountAddress)
    (arg : Expr) (retVar : Ident)
    (heval : evalExpr? config ⟨contract, locals, imms⟩ evm arg = .ok (.address value))
    (hperm : evm.executionEnv.perm = false) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_setGuardian" [arg] retVar)
      .staticViolation := by
  exact ExecStmt.internalCallStatic (callee := setGuardianFunction.toCallable)
    (argVals := [.address value])
    (by simp only [evalExprs?, heval, bind, EvalResult.bind, pure]) rfl rfl
    (setGuardianBodyStatic evm imms value hperm)

end Benchmarks.Morpho.MetaMorphoV1_1
