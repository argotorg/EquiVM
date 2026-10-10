import Benchmarks.Morpho.MetaMorphoV1_1.PermitData

/-! Source guards, nonce consumption, and the digest prefix of permit. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

theorem permitDeadlineSource (p : PermitData) (evm : State) (v : MetaMorphoV1_1Immutables) :
    evalExpr? config (p.entryFrame evm v) evm
      (.binary .le (.env .timestamp) (.var "deadline")) =
      .ok (.bool (decide ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        p.deadline.toNat))) := by
  apply naturalLeSource
  · simp only [evalExpr?, envValue, pure]
  · simp [evalExpr?, PermitData.entryFrame, PermitData.locals, Std.HashMap.getElem_insert,
      EvalResult.ofOption, uint256Value]

theorem permitPublicPrefix (p : PermitData) (evm : State) (v : MetaMorphoV1_1Immutables)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (htime : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤ p.deadline.toNat) :
    ABlock config evm ⟨contract, p.locals, immStore v⟩ permitTransition.body
      (p.entryFrame evm v) (permitTransition.body.drop 4) := by
  refine ⟨fun h ↦ ?_⟩
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consNormal (ExecStmt.requireTrue (by
    simpa only [decide_eq_true htime] using permitDeadlineSource p evm v)) h

theorem permitDeadlineReverts (p : PermitData) (evm : State) (v : MetaMorphoV1_1Immutables)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (htime : ¬ (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤ p.deadline.toNat) :
    ExecTransitionBody config contract evm p.locals permitTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consRevert (ExecStmt.requireFalse (by
    simpa only [decide_eq_false htime] using permitDeadlineSource p evm v))

theorem permitNonceArgs (p : PermitData) (evm : State) (v : MetaMorphoV1_1Immutables) :
    evalExprs? config (p.entryFrame evm v) evm [.var "owner"] = .ok [.address p.owner] := by
  simp [evalExprs?, evalExpr?, PermitData.entryFrame, PermitData.locals,
    Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem permitPublicStatic (p : PermitData) (evm : State) (v : MetaMorphoV1_1Immutables)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (htime : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤ p.deadline.toNat)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm p.locals permitTransition.body .staticViolation
      (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  apply (permitPublicPrefix p evm v hwv hhi htime).run
  exact ExecBlock.consStatic (useNonceCallStatic (permitNonceArgs p evm v) hperm)

theorem permitHashPrefix {result : ExecResult} (p : PermitData) (evm : State)
    (v : MetaMorphoV1_1Immutables)
    (htail : ExecBlock config (p.hashFrame evm v) (consumeNonceState evm p.owner)
      (permitTransition.body.drop 7) result) :
    ExecBlock config (p.entryFrame evm v) evm (permitTransition.body.drop 4) result := by
  apply ExecBlock.consNormal (useNonceCall (permitNonceArgs p evm v))
  have hhash : evalExpr? config (p.nonceFrame evm v) (consumeNonceState evm p.owner)
      permitStructHashExpr = .ok (wordBytes32Value (p.structHash evm)) := by
    apply permitStructHashSource <;>
      simp [PermitData.nonceFrame, PermitData.entryFrame, PermitData.locals,
        Std.HashMap.getElem_insert]
  apply ExecBlock.consNormal (ExecStmt.letDecl hhash)
  have henv : (consumeNonceState evm p.owner).executionEnv = evm.executionEnv :=
    storageStore_executionEnv _ _ _ _
  have hcall := hashTypedDataCall v (evm := consumeNonceState evm p.owner)
    (structHash := p.structHash evm)
    (locals := (p.nonceFrame evm v).locals.insert "structHash"
      (wordBytes32Value (p.structHash evm)))
    (args := [.var "structHash"]) (ret := "hash")
    (evalExprs?_singleton (by simp only [evalExpr?, domainFrame, store_get_self,
      EvalResult.ofOption]))
  rw [henv] at hcall
  exact ExecBlock.consNormal hcall htail

end Benchmarks.Morpho.MetaMorphoV1_1
