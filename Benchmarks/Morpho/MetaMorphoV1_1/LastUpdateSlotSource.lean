import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSlots

/-! The checked offset in Morpho's last-update storage-slot helper. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def lastUpdateSlotFunction : FunctionDecl := contract.functions[50]!

def lastUpdateSlotFrame (imms : Store) (id : UInt256) : Frame :=
  ⟨contract, (∅ : Store).insert "id" (wordBytes32Value id), imms⟩

def lastUpdateSlot (id : UInt256) : UInt256 := solcMappingSlot ⟨3⟩ id + ⟨2⟩

def lastUpdateHashExpr : Expr :=
  .cast (.keccak256 (.abiEncodePacked
    [(.elem (.bytes abiBytes32Width), .var "id"), (abiUInt256, .intLit 3)]))
      (.elem (.int (.uint ⟨256, by decide⟩)))

theorem lastUpdateHashSource (evm : State) (imms : Store) (id : UInt256) :
    evalExpr? config (lastUpdateSlotFrame imms id) evm lastUpdateHashExpr =
      .ok (uint256Value (solcMappingSlot ⟨3⟩ id)) := by
  apply evalExpr_bytes32ToUint
  exact evalExpr_keccakWord (evalExpr_packedTwoWords
    (by simp only [evalExpr?, lastUpdateSlotFrame, store_get_self, EvalResult.ofOption])
    (show evalExpr? config (lastUpdateSlotFrame imms id) evm (.intLit 3) =
      .ok (uint256Value ⟨3⟩) by simp only [evalExpr?, uint256Value, pure]; rfl)
    (encodePacked_bytes32 id) (encodePacked_uint256 ⟨3⟩))

theorem lastUpdateSlotBody (evm : State) (imms : Store) (id : UInt256)
    (hfit : (solcMappingSlot ⟨3⟩ id).toNat + 2 < UInt256.size) :
    ExecFuncBody config (lastUpdateSlotFrame imms id) evm lastUpdateSlotFunction.body
      (.returned (lastUpdateSlotFrame imms id) evm (some [wordBytes32Value (lastUpdateSlot id)])) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  apply evalExpr_uintToBytes32
  exact checkedAddSourceOk (lastUpdateHashSource evm imms id)
    (show evalExpr? config (lastUpdateSlotFrame imms id) evm (.intLit 2) =
      .ok (uint256Value ⟨2⟩) by simp only [evalExpr?, uint256Value, pure]; rfl) hfit

theorem lastUpdateSlotBodyReverts (evm : State) (imms : Store) (id : UInt256)
    (hbad : UInt256.size ≤ (solcMappingSlot ⟨3⟩ id).toNat + 2) :
    ExecFuncBody config (lastUpdateSlotFrame imms id) evm lastUpdateSlotFunction.body
      .reverted := by
  have hsum := checkedAddSourceOverflow (lastUpdateHashSource evm imms id)
    (show evalExpr? config (lastUpdateSlotFrame imms id) evm (.intLit 2) =
      .ok (uint256Value ⟨2⟩) by simp only [evalExpr?, uint256Value, pure]; rfl) hbad
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert (ExecStmt.returnRevert ?_)
  change evalExprs? config (lastUpdateSlotFrame imms id) evm
    [.cast (.inRange (.uint ⟨256, by decide⟩)
      (.binary .add lastUpdateHashExpr (.intLit 2))) (.elem (.bytes abiBytes32Width))] = _
  simp only [evalExprs?, evalExpr?, hsum, bind, EvalResult.bind]

theorem lastUpdateSlotCall (evm : State) (locals imms : Store) (id : UInt256)
    (retVar : Ident) (idExpr : Expr)
    (hid : evalExpr? config ⟨contract, locals, imms⟩ evm idExpr = .ok (wordBytes32Value id))
    (hfit : (solcMappingSlot ⟨3⟩ id).toNat + 2 < UInt256.size) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall lastUpdateSlotFunction.name [idExpr] retVar)
      (.ok ⟨contract, locals.insert retVar (wordBytes32Value (lastUpdateSlot id)), imms⟩ evm) := by
  exact internalCallFunctionReturn (callee := lastUpdateSlotFunction)
    (evalExprs?_singleton hid) rfl rfl (lastUpdateSlotBody evm imms id hfit)

theorem lastUpdateSlotCallReverts (evm : State) (locals imms : Store) (id : UInt256)
    (retVar : Ident) (idExpr : Expr)
    (hid : evalExpr? config ⟨contract, locals, imms⟩ evm idExpr = .ok (wordBytes32Value id))
    (hbad : UInt256.size ≤ (solcMappingSlot ⟨3⟩ id).toNat + 2) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall lastUpdateSlotFunction.name [idExpr] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := lastUpdateSlotFunction)
    (evalExprs?_singleton hid) rfl rfl (lastUpdateSlotBodyReverts evm imms id hbad)

end Benchmarks.Morpho.MetaMorphoV1_1
