import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.AllocatorRoleSource
import Benchmarks.Morpho.MetaMorphoV1_1.ArrayStorage
import Benchmarks.Morpho.MetaMorphoV1_1.UintArrayCalldata

/-! Source entry through the role check and the two queue lengths. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def updateWithdrawQueuePrefixFrame (evm : State) (imms : Store) (values : List Value) : Frame :=
  { contract := contract
    locals := (((((∅ : Store).insert "indexes" (.array values)).insert "__calldata"
      (.bytes evm.executionEnv.calldata)).insert "__role" .unit).insert "newLength"
      (.int (Int.ofNat values.length))).insert "currLength"
      (uint256Value (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨21⟩))
    immutables := imms }

theorem updateWithdrawQueuePrefix (evm : State) (imms : Store) (values : List Value)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : allocatorRoleAllowed evm) :
    ABlock config evm ⟨contract, (∅ : Store).insert "indexes" (.array values), imms⟩
      updateWithdrawQueueBody (updateWithdrawQueuePrefixFrame evm imms values)
      (updateWithdrawQueueAllocation ++
        [updateWithdrawQueueBuildLoop, updateWithdrawQueueRemoveLoop] ++
          updateWithdrawQueueTail) := by
  constructor
  intro result htail
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consNormal (allocatorRoleCall evm _ imms "__role" hrole)
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalLocalArrayLength (values := values) (by
    simp only [store_get_ne _ _ (by decide : ("__role" == "indexes") = false),
      store_get_ne _ _ (by decide : ("__calldata" == "indexes") = false), store_get_self]))) ?_
  refine ExecBlock.consNormal ?_ htail
  apply ExecStmt.letDecl
  apply evalStorage_withdrawQueueLength
  simp only [store_get_ne _ _ (by decide : ("newLength" == "withdrawQueue") = false),
    store_get_ne _ _ (by decide : ("__role" == "withdrawQueue") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "withdrawQueue") = false),
    store_get_ne _ _ (by decide : ("indexes" == "withdrawQueue") = false), store_get_empty]

theorem updateWithdrawQueueBodyRoleReverts (evm : State) (imms : Store) (values : List Value)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hrole : ¬ allocatorRoleAllowed evm) :
    ExecTransitionBody config contract evm ((∅ : Store).insert "indexes" (.array values))
      updateWithdrawQueueBody .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consRevert (allocatorRoleCallReverts evm _ imms "__role" hrole)

end Benchmarks.Morpho.MetaMorphoV1_1
