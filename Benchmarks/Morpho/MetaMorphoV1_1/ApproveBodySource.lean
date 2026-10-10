import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalCalls

/-! Source execution of the public approval transition. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def approvePublicFrame (evm : State) (locals imms : Store) : Frame :=
  { contract := contract
    locals := (locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).insert "owner"
      (.address evm.executionEnv.source)
    immutables := imms }

def approvePublicTail : List Stmt :=
  [.internalCall "_approve" [.var "owner", .var "spender", .var "value"] "__c1",
    .return [.boolLit true]]

theorem approvePublicPrefix (evm : State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm ⟨contract, locals, imms⟩ approveTransition.body
      (approvePublicFrame evm locals imms) approvePublicTail := by
  refine ⟨fun h ↦ ?_⟩
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consNormal (msgSenderCall _ imms evm "owner") h

theorem approvePublicArgs (evm : State) (locals imms : Store)
    (spender : AccountAddress) (value : UInt256)
    (hs : locals.get? "spender" = some (.address spender))
    (hv : locals.get? "value" = some (uint256Value value)) :
    evalExprs? config (approvePublicFrame evm locals imms) evm
      [.var "owner", .var "spender", .var "value"] =
      .ok [.address evm.executionEnv.source, .address spender, uint256Value value] := by
  simp only [evalExprs?, evalExpr?, approvePublicFrame, store_get_self,
    store_get_ne _ _ (by decide : ("owner" == "spender") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "spender") = false),
    store_get_ne _ _ (by decide : ("owner" == "value") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "value") = false),
    hs, hv, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem approvePublicBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : State) (locals : Store) (spender : AccountAddress) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hs : locals.get? "spender" = some (.address spender))
    (hv : locals.get? "value" = some (uint256Value value))
    (ho : evm.executionEnv.source ≠ ⟨0, by decide⟩) (hsp : spender ≠ ⟨0, by decide⟩) :
    ExecTransitionBody config contract evm locals approveTransition.body
      (.returned { approvePublicFrame evm locals (immStore v) with
        locals := (approvePublicFrame evm locals (immStore v)).locals.insert "__c1" .unit }
        (approvalState evm evm.executionEnv.source spender value) [Value.bool true])
      (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (approvePublicPrefix evm locals (immStore v) hwv hhi).run
  apply ExecBlock.consNormal (approveCall (approvePublicArgs evm locals (immStore v)
    spender value hs hv) ho hsp)
  exact ExecBlock.consReturn (ExecStmt.return
    (by simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]))

theorem approvePublicBodyReverts (v : MetaMorphoV1_1Immutables)
    (evm : State) (locals : Store) (spender : AccountAddress) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hs : locals.get? "spender" = some (.address spender))
    (hv : locals.get? "value" = some (uint256Value value))
    (hbad : ¬ (evm.executionEnv.source ≠ ⟨0, by decide⟩ ∧ spender ≠ ⟨0, by decide⟩)) :
    ExecTransitionBody config contract evm locals approveTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (approvePublicPrefix evm locals (immStore v) hwv hhi).run
  exact ExecBlock.consRevert (approveCallReverts
    (approvePublicArgs evm locals (immStore v) spender value hs hv) hbad)

theorem approvePublicBodyStatic (v : MetaMorphoV1_1Immutables)
    (evm : State) (locals : Store) (spender : AccountAddress) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hs : locals.get? "spender" = some (.address spender))
    (hv : locals.get? "value" = some (uint256Value value))
    (ho : evm.executionEnv.source ≠ ⟨0, by decide⟩) (hsp : spender ≠ ⟨0, by decide⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm locals approveTransition.body .staticViolation
      (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  apply (approvePublicPrefix evm locals (immStore v) hwv hhi).run
  exact ExecBlock.consStatic (approveCallStatic
    (approvePublicArgs evm locals (immStore v) spender value hs hv) ho hsp hperm)

end Benchmarks.Morpho.MetaMorphoV1_1
