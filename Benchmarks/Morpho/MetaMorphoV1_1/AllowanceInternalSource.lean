import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalSource

/-! The internal allowance reader used before a delegated transfer or withdrawal. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def allowanceInternalFunction : FunctionDecl := contract.functions[74]!

def allowanceWord (evm : State) (owner spender : AccountAddress) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (approvalSlot owner spender)

def allowanceInternalFrame (imms : Store) (owner spender : AccountAddress) : Frame :=
  ⟨contract, ((∅ : Store).insert "spender" (.address spender)).insert "owner" (.address owner),
    imms⟩

theorem allowanceInternalBody (imms : Store) (evm : State) (owner spender : AccountAddress) :
    ExecFuncBody config (allowanceInternalFrame imms owner spender) evm
      allowanceInternalFunction.body
      (.returned (allowanceInternalFrame imms owner spender) evm
        (some [uint256Value (allowanceWord evm owner spender)])) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  apply evalExpr_storage_scalar_value
    (er := ⟨"_allowances", [.mindex (.address owner), .mindex (.address spender)]⟩)
    (t := .int (.uint ⟨256, by decide⟩)) (by simp [allowanceInternalFrame])
    (evalStorageRef_twoAddressIndices "_allowances" "owner" "spender" owner spender
      (by simp [allowanceInternalFrame])
      (by simp [allowanceInternalFrame, Std.HashMap.getElem_insert])) rfl rfl
    (loc := uint256Loc (approvalSlot owner spender))
  · change some (StorageAddr.leaf (uint256Loc
      (solcMappingSlot (solcMappingSlot ⟨1⟩ (keyValueToWord (.address owner)))
        (keyValueToWord (.address spender))))) = _
    rw [keyValueToWord_address, keyValueToWord_address]
    rfl
  · exact storageLocLoad_uint256 evm _

theorem allowanceInternalCall {locals imms : Store} {evm : State}
    {owner spender : AccountAddress} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address owner, .address spender]) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "allowance_body" args ret)
      (.ok ⟨contract, locals.insert ret (uint256Value (allowanceWord evm owner spender)), imms⟩
        evm) :=
  internalCallFunctionReturn (callee := allowanceInternalFunction) hargs rfl rfl
    (allowanceInternalBody imms evm owner spender)

end Benchmarks.Morpho.MetaMorphoV1_1
