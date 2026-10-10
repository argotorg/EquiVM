import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalCalls
import Benchmarks.Morpho.MetaMorphoV1_1.TransferInternalSource

/-! Source execution of the public transfer transition. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def transferPublicFrame (evm : State) (locals imms : Store) : Frame :=
  { contract := contract
    locals := (locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).insert "owner"
      (.address evm.executionEnv.source)
    immutables := imms }

def transferPublicTail : List Stmt :=
  [.internalCall "_transfer" [.var "owner", .var "to", .var "value"] "__c1",
    .return [.boolLit true]]

theorem transferPublicPrefix (evm : State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm ⟨contract, locals, imms⟩ transferTransition.body
      (transferPublicFrame evm locals imms) transferPublicTail := by
  refine ⟨fun h ↦ ?_⟩
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consNormal (msgSenderCall _ imms evm "owner") h

theorem transferPublicArgs (evm : State) (locals imms : Store)
    (recipient : AccountAddress) (value : UInt256)
    (hs : locals.get? "to" = some (.address recipient))
    (hv : locals.get? "value" = some (uint256Value value)) :
    evalExprs? config (transferPublicFrame evm locals imms) evm
      [.var "owner", .var "to", .var "value"] =
      .ok [.address evm.executionEnv.source, .address recipient, uint256Value value] := by
  simp only [evalExprs?, evalExpr?, transferPublicFrame, store_get_self,
    store_get_ne _ _ (by decide : ("owner" == "to") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "to") = false),
    store_get_ne _ _ (by decide : ("owner" == "value") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "value") = false),
    hs, hv, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem transferPublicBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : State) (locals : Store) (recipient : AccountAddress) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hs : locals.get? "to" = some (.address recipient))
    (hv : locals.get? "value" = some (uint256Value value))
    (hgood : transferAllowed evm evm.executionEnv.source recipient value) :
    ExecTransitionBody config contract evm locals transferTransition.body
      (.returned { transferPublicFrame evm locals (immStore v) with
        locals := (transferPublicFrame evm locals (immStore v)).locals.insert "__c1" .unit }
        (balanceMoveState evm evm.executionEnv.source recipient value) [Value.bool true])
      (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (transferPublicPrefix evm locals (immStore v) hwv hhi).run
  apply ExecBlock.consNormal (transferCall (transferPublicArgs evm locals (immStore v)
    recipient value hs hv) hgood)
  exact ExecBlock.consReturn (ExecStmt.return
    (by simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]))

theorem transferPublicBodyReverts (v : MetaMorphoV1_1Immutables)
    (evm : State) (locals : Store) (recipient : AccountAddress) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hs : locals.get? "to" = some (.address recipient))
    (hv : locals.get? "value" = some (uint256Value value))
    (hbad : ¬ transferAllowed evm evm.executionEnv.source recipient value) :
    ExecTransitionBody config contract evm locals transferTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (transferPublicPrefix evm locals (immStore v) hwv hhi).run
  exact ExecBlock.consRevert (transferCallReverts
    (transferPublicArgs evm locals (immStore v) recipient value hs hv) hbad)

theorem transferPublicBodyStatic (v : MetaMorphoV1_1Immutables)
    (evm : State) (locals : Store) (recipient : AccountAddress) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hs : locals.get? "to" = some (.address recipient))
    (hv : locals.get? "value" = some (uint256Value value))
    (hgood : transferAllowed evm evm.executionEnv.source recipient value)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm locals transferTransition.body .staticViolation
      (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  apply (transferPublicPrefix evm locals (immStore v) hwv hhi).run
  exact ExecBlock.consStatic (transferCallStatic
    (transferPublicArgs evm locals (immStore v) recipient value hs hv) hgood hperm)

end Benchmarks.Morpho.MetaMorphoV1_1
