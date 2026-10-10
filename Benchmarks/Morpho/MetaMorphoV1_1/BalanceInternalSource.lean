import Benchmarks.Morpho.MetaMorphoV1_1.MappingStorage

/-! The internal ERC20 balance reader used by the withdrawal limit. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def balanceInternalFunction : FunctionDecl := contract.functions[58]!

def balanceInternalFrame (imms : Store) (owner : AccountAddress) : Frame :=
  { contract := contract
    locals := (∅ : Store).insert "account" (.address owner)
    immutables := imms }

def balanceInternalWord (evm : State) (owner : AccountAddress) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
    (solcMappingSlot ⟨0⟩ (UInt256.ofNat owner.toNat))

theorem balanceInternalBody (evm : State) (imms : Store) (owner : AccountAddress) :
    ExecFuncBody config (balanceInternalFrame imms owner) evm balanceInternalFunction.body
      (.returned (balanceInternalFrame imms owner) evm
        (some [uint256Value (balanceInternalWord evm owner)])) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  apply evalStorage_balanceOf evm _ imms (UInt256.ofNat owner.toNat) (by simp)
  · have ho : AccountAddress.ofNat (UInt256.ofNat owner.toNat).toNat = owner := by
      rw [UInt256.toNat_ofNat_of_lt (n := owner.toNat) (lt_trans owner.isLt (by decide))]
      exact accountAddress_ofNat_toNat owner
    rw [ho]
    exact store_get_self _ _ _
  · exact addressWord_val_canonical owner

theorem balanceInternalCall (evm : State) (locals imms : Store) (owner : AccountAddress)
    (ret : Ident) (ownerExpr : Expr)
    (ho : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm ownerExpr = .ok (.address owner)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "balanceOf_body" [ownerExpr] ret)
      (.ok
        { contract := contract
          locals := locals.insert ret (uint256Value (balanceInternalWord evm owner))
          immutables := imms } evm) := by
  have hargs : evalExprs? config
      { contract := contract, locals := locals, immutables := imms } evm [ownerExpr] =
      .ok [.address owner] := by
    simp only [evalExprs?, ho, bind, EvalResult.bind, pure]
  exact internalCallFunctionReturn (callee := balanceInternalFunction)
    hargs rfl rfl (balanceInternalBody evm imms owner)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
