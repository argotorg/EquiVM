import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl
import Benchmarks.Morpho.MetaMorphoV1_1.Mutation

/-! Internal ownership changes shared by acceptance and renunciation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def ownableTransferFunction : FunctionDecl := contract.functions[68]!

def transferOwnershipFunction : FunctionDecl := contract.functions[32]!

def clearPendingOwnerState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨9⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩) ⟨0⟩)

def setOwnerState (evm : EVM.State) (w : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩) w)

def ownershipState (evm : EVM.State) (w : UInt256) : EVM.State :=
  setOwnerState (clearPendingOwnerState evm) w

def ownershipAccounts (I : ExecutionEnv) (accounts : AccountMap) (w : UInt256) : AccountMap :=
  let cleared := sstoreAccountMap I.codeOwner accounts ⟨9⟩
    (setAddressOffset0Word (codeOwnerStorageWord I accounts ⟨9⟩) ⟨0⟩)
  sstoreAccountMap I.codeOwner cleared ⟨8⟩
    (setAddressOffset0Word (codeOwnerStorageWord I cleared ⟨8⟩) w)

theorem ownershipState_accounts (evm : EVM.State) (w : UInt256) :
    (ownershipState evm w).accountMap = ownershipAccounts evm.executionEnv evm.accountMap w := by
  simp only [ownershipState, setOwnerState, clearPendingOwnerState, ownershipAccounts,
    storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, codeOwnerStorageWord]


def ownableTransferFrame (evm : EVM.State) (imms : Store) (w : UInt256) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert "newOwner" (.address (AccountAddress.ofNat w.toNat))).insert
      "oldOwner" (.address (ownerAddress evm))
    immutables := imms }

theorem ownableTransferBody (evm : EVM.State) (imms : Store) (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    ExecFuncBody config
      { contract := contract
        locals := (∅ : Store).insert "newOwner" (.address (AccountAddress.ofNat w.toNat))
        immutables := imms } evm ownableTransferFunction.body
      (.returned (ownableTransferFrame evm imms w) (setOwnerState evm w) none) := by
  apply ExecFuncBody.execBlockOK
  apply (ABlock.start.letStep (evalStorage_owner evm _ imms (by simp))).run
  refine ExecBlock.consNormal
    (ExecStmt.assign ?_ (assignStorage_owner evm _ imms w (by simp) hcanon)) ?_
  · simp only [evalExpr?,
      store_get_ne _ _ (show ("oldOwner" == "newOwner") = false from by decide),
      store_get_self, EvalResult.ofOption]
  · apply (ABlock.start.emitStep
      (vals := [.address (ownerAddress evm), .address (AccountAddress.ofNat w.toNat)]) ?_).run
    · exact ExecBlock.nil
    · simp only [evalExprs?, evalExpr?,
        store_get_ne _ _ (show ("oldOwner" == "newOwner") = false from by decide),
        store_get_self, EvalResult.ofOption, EvalResult.bind, bind, pure]
      rfl

theorem ownableTransferCall (evm : EVM.State) (locals imms : Store) (w : UInt256)
    (retVar : Ident) (arg : Expr) (hcanon : w.toNat < EVM.addressModulus)
    (heval : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm arg = .ok (.address (AccountAddress.ofNat w.toNat))) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "Ownable__transferOwnership" [arg] retVar)
      (.ok { contract := contract, locals := locals.insert retVar .unit, immutables := imms }
        (setOwnerState evm w)) := by
  exact internalCallFunctionReturn
    (caller := { contract := contract, locals := locals, immutables := imms })
    (callee := ownableTransferFunction) (value := none)
    (argVals := [.address (AccountAddress.ofNat w.toNat)])
    (by simp [evalExprs?, heval, bind, EvalResult.bind, pure]) rfl rfl
    (ownableTransferBody evm imms w hcanon)

def ownershipFrame (imms : Store) (w : UInt256) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert "newOwner" (.address (AccountAddress.ofNat w.toNat))).insert
      "__c0" .unit
    immutables := imms }

theorem ownershipBody (evm : EVM.State) (imms : Store) (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    ExecFuncBody config
      { contract := contract
        locals := (∅ : Store).insert "newOwner" (.address (AccountAddress.ofNat w.toNat))
        immutables := imms } evm transferOwnershipFunction.body
      (.returned (ownershipFrame imms w) (ownershipState evm w) none) := by
  apply ExecFuncBody.execBlockOK
  refine ExecBlock.consNormal (ExecStmt.delete (deleteStorage_pendingOwner evm _ imms
    (by simp))) ?_
  refine ExecBlock.consNormal
    (ownableTransferCall _ _ imms w "__c0" (.var "newOwner") hcanon ?_) ExecBlock.nil
  simp [evalExpr?, EvalResult.ofOption]

theorem ownershipCall (evm : EVM.State) (locals imms : Store) (w : UInt256)
    (retVar : Ident) (arg : Expr) (hcanon : w.toNat < EVM.addressModulus)
    (heval : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm arg = .ok (.address (AccountAddress.ofNat w.toNat))) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_transferOwnership" [arg] retVar)
      (.ok { contract := contract, locals := locals.insert retVar .unit, immutables := imms }
        (ownershipState evm w)) := by
  exact internalCallFunctionReturn
    (caller := { contract := contract, locals := locals, immutables := imms })
    (callee := transferOwnershipFunction) (value := none)
    (argVals := [.address (AccountAddress.ofNat w.toNat)])
    (by simp [evalExprs?, heval, bind, EvalResult.bind, pure]) rfl rfl
    (ownershipBody evm imms w hcanon)

theorem ownershipBodyStatic (evm : EVM.State) (imms : Store) (w : UInt256)
    (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config
      { contract := contract
        locals := (∅ : Store).insert "newOwner" (.address (AccountAddress.ofNat w.toNat))
        immutables := imms } evm transferOwnershipFunction.body .staticViolation := by
  exact ExecFuncBody.execBlockStatic (ExecBlock.consStatic
    (ExecStmt.deleteStatic (deleteStorage_pendingOwner evm _ imms (by simp)) hperm))

theorem ownershipCallStatic (evm : EVM.State) (locals imms : Store) (w : UInt256)
    (retVar : Ident) (arg : Expr) (hperm : evm.executionEnv.perm = false)
    (heval : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm arg = .ok (.address (AccountAddress.ofNat w.toNat))) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_transferOwnership" [arg] retVar) .staticViolation := by
  exact ExecStmt.internalCallStatic (callee := transferOwnershipFunction.toCallable)
    (argVals := [.address (AccountAddress.ofNat w.toNat)])
    (by simp [evalExprs?, heval, bind, EvalResult.bind, pure]) rfl rfl
    (ownershipBodyStatic evm imms w hperm)

end Benchmarks.Morpho.MetaMorphoV1_1
