import Benchmarks.Morpho.MetaMorphoV1_1.BalanceMutation

/-! Consume a nonce with wrapping increment, including static execution. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def useNonceFunction : FunctionDecl := contract.functions[33]!

def nonceSlot (owner : AccountAddress) : UInt256 :=
  solcMappingSlot ⟨7⟩ (UInt256.ofNat owner.toNat)

def nonceWord (evm : State) (owner : AccountAddress) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (nonceSlot owner)

def consumeNonceState (evm : State) (owner : AccountAddress) : State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (nonceSlot owner) (nonceWord evm owner + ⟨1⟩)

def useNonceFrame (imms : Store) (owner : AccountAddress) : Frame :=
  ⟨contract, (∅ : Store).insert "owner" (.address owner), imms⟩

def useNonceReadFrame (evm : State) (imms : Store) (owner : AccountAddress) : Frame :=
  { useNonceFrame imms owner with
    locals := (useNonceFrame imms owner).locals.insert "nonce" (uint256Value (nonceWord evm owner)) }

def useNonceAssignStmt : Stmt :=
  .assign .storage ⟨"_nonces", [.mindex (.var "owner")]⟩
    (.cast (.binary .add (.var "nonce") (.intLit 1)) (.elem (.int (.uint ⟨256, by decide⟩))))

theorem useNonceFunction_body : useNonceFunction.body =
    [.letDecl "nonce" (some abiUInt256) (.storage ⟨"_nonces", [.mindex (.var "owner")]⟩),
      useNonceAssignStmt, .return [.var "nonce"]] := by
  decide +kernel

theorem nonceReadSource (evm : State) (locals imms : Store) (owner : AccountAddress)
    (hbase : locals.get? "_nonces" = none)
    (howner : locals.get? "owner" = some (.address owner)) :
    evalExpr? config ⟨contract, locals, imms⟩ evm
      (.storage ⟨"_nonces", [.mindex (.var "owner")]⟩) =
      .ok (uint256Value (nonceWord evm owner)) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"_nonces", [.mindex (.address owner)]⟩) (t := .int (.uint ⟨256, by decide⟩))
    hbase (evalStorageRef_addressIndex "_nonces" "owner" owner howner) rfl rfl
    (loc := uint256Loc (nonceSlot owner))
  · change some (StorageAddr.leaf (uint256Loc
      (solcMappingSlot ⟨7⟩ (keyValueToWord (.address owner))))) = _
    rw [keyValueToWord_address]
    rfl
  · exact storageLocLoad_uint256 evm _

theorem nonceWriteSource (evm : State) (locals imms : Store) (owner : AccountAddress)
    (value : UInt256) (hbase : locals.get? "_nonces" = none)
    (howner : locals.get? "owner" = some (.address owner)) :
    assignStorageRef? config ⟨contract, locals, imms⟩ evm .storage
      ⟨"_nonces", [.mindex (.var "owner")]⟩ (uint256Value value) =
      .ok (⟨contract, locals, imms⟩,
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (nonceSlot owner) value) := by
  apply assignStorageRef_storage_scalar_value
    (er := ⟨"_nonces", [.mindex (.address owner)]⟩)
    (ty := .elem (.int (.uint ⟨256, by decide⟩))) hbase
    (evalStorageRef_addressIndex "_nonces" "owner" owner howner) rfl rfl
    (loc := uint256Loc (nonceSlot owner))
  · change some (StorageAddr.leaf (uint256Loc
      (solcMappingSlot ⟨7⟩ (keyValueToWord (.address owner))))) = _
    rw [keyValueToWord_address]
    rfl
  · exact .inl ⟨_, rfl⟩
  · exact storageLocStore_uint256 evm _ value

theorem useNonceAssign (evm : State) (imms : Store) (owner : AccountAddress) :
    ExecStmt config (useNonceReadFrame evm imms owner) evm useNonceAssignStmt
      (.ok (useNonceReadFrame evm imms owner) (consumeNonceState evm owner)) := by
  apply ExecStmt.assign (value := uint256Value (nonceWord evm owner + ⟨1⟩))
  · apply wrappingAddSource
    · simp only [evalExpr?, useNonceReadFrame, store_get_self, EvalResult.ofOption]
    · simp only [evalExpr?, pure]; rfl
  · exact nonceWriteSource evm _ imms owner _
      (by simp only [useNonceFrame]
          rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_empty])
      (by simp only [useNonceFrame]
          rw [store_get_ne _ _ (by decide), store_get_self])

theorem useNonceBody (evm : State) (imms : Store) (owner : AccountAddress) :
    ExecFuncBody config (useNonceFrame imms owner) evm useNonceFunction.body
      (.returned (useNonceReadFrame evm imms owner) (consumeNonceState evm owner)
        (some [uint256Value (nonceWord evm owner)])) := by
  apply ExecFuncBody.execBlockRet
  rw [useNonceFunction_body]
  refine ExecBlock.consNormal (ExecStmt.letDecl (nonceReadSource evm _ imms owner
    (by rw [store_get_ne _ _ (by decide), store_get_empty])
    (store_get_self _ _ _))) ?_
  refine ExecBlock.consNormal (useNonceAssign evm imms owner) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by
    simp only [evalExprs?, evalExpr?, useNonceReadFrame, store_get_self,
      EvalResult.ofOption, bind, EvalResult.bind, pure]))

theorem useNonceBodyStatic (evm : State) (imms : Store) (owner : AccountAddress)
    (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (useNonceFrame imms owner) evm useNonceFunction.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  rw [useNonceFunction_body]
  refine ExecBlock.consNormal (ExecStmt.letDecl (nonceReadSource evm _ imms owner
    (by rw [store_get_ne _ _ (by decide), store_get_empty])
    (store_get_self _ _ _))) ?_
  exact ExecBlock.consStatic (execStmt_assign_static (useNonceAssign evm imms owner) hperm)

theorem useNonceCall {evm : State} {locals imms : Store} {owner : AccountAddress}
    {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args = .ok [.address owner]) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_useNonce" args ret)
      (.ok ⟨contract, locals.insert ret (uint256Value (nonceWord evm owner)), imms⟩
        (consumeNonceState evm owner)) :=
  internalCallFunctionReturn (callee := useNonceFunction) hargs rfl rfl (useNonceBody evm imms owner)

theorem useNonceCallStatic {evm : State} {locals imms : Store} {owner : AccountAddress}
    {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args = .ok [.address owner])
    (hperm : evm.executionEnv.perm = false) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_useNonce" args ret)
      .staticViolation :=
  ExecStmt.internalCallStatic (callee := useNonceFunction.toCallable) hargs rfl rfl
    (useNonceBodyStatic evm imms owner hperm)

end Benchmarks.Morpho.MetaMorphoV1_1
