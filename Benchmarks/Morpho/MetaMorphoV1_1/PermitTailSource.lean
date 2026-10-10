import Benchmarks.Morpho.MetaMorphoV1_1.PermitPrefixSource
import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalCalls
import Benchmarks.Morpho.MetaMorphoV1_1.ECDSARecoverSource

/-! Source composition from signature recovery through the final permit approval. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

theorem permitRecoverArgs (p : PermitData) (evm state : State) (v : MetaMorphoV1_1Immutables) :
    evalExprs? config (p.hashFrame evm v) state
      [.var "hash", .var "v", .var "r", .var "s"] =
      .ok [wordBytes32Value (p.digest v evm), uint256Value p.sigV,
        wordBytes32Value p.sigR, wordBytes32Value p.sigS] := by
  simp [evalExprs?, evalExpr?, PermitData.hashFrame, PermitData.nonceFrame,
    PermitData.entryFrame, PermitData.locals, Std.HashMap.getElem_insert,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem permitRecoverPrefix {p : PermitData} {evm state : State} {v : MetaMorphoV1_1Immutables}
    {signer : AccountAddress} {frame : Frame} {result : ExecResult}
    (hbody : ExecFuncBody config (ecdsaFrame (immStore v) (p.digest v evm) p.sigV p.sigR p.sigS)
      (consumeNonceState evm p.owner) ecdsaRecoverFunction.body
      (.returned frame state (some [.address signer])))
    (htail : ExecBlock config (p.signerFrame evm v signer) state
      (permitTransition.body.drop 8) result) :
    ExecBlock config (p.hashFrame evm v) (consumeNonceState evm p.owner)
      (permitTransition.body.drop 7) result :=
  ExecBlock.consNormal (internalCallFunctionReturn (callee := ecdsaRecoverFunction)
    (permitRecoverArgs p evm _ v) rfl rfl hbody) htail

theorem permitRecoverReverts {p : PermitData} {evm : State} {v : MetaMorphoV1_1Immutables}
    (hbody : ExecFuncBody config (ecdsaFrame (immStore v) (p.digest v evm) p.sigV p.sigR p.sigS)
      (consumeNonceState evm p.owner) ecdsaRecoverFunction.body .reverted) :
    ExecBlock config (p.hashFrame evm v) (consumeNonceState evm p.owner)
      (permitTransition.body.drop 7) .reverted :=
  ExecBlock.consRevert (ecdsaRecoverCallReverts (permitRecoverArgs p evm _ v) hbody)

theorem permitSignerSource (p : PermitData) (evm state : State)
    (v : MetaMorphoV1_1Immutables) (signer : AccountAddress) :
    evalExpr? config (p.signerFrame evm v signer) state
      (.binary .eq (.var "signer") (.var "owner")) = .ok (.bool (decide (signer = p.owner))) := by
  apply evalExpr_addressEq <;>
    simp [evalExpr?, PermitData.signerFrame, PermitData.hashFrame, PermitData.nonceFrame,
      PermitData.entryFrame, PermitData.locals, Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem permitSignerReverts {p : PermitData} {evm state : State}
    {v : MetaMorphoV1_1Immutables} {signer : AccountAddress} (hne : signer ≠ p.owner) :
    ExecBlock config (p.signerFrame evm v signer) state
      (permitTransition.body.drop 8) .reverted :=
  ExecBlock.consRevert (ExecStmt.requireFalse (by
    simpa only [decide_eq_false hne] using permitSignerSource p evm state v signer))

theorem permitApprovalArgs (p : PermitData) (evm state : State)
    (v : MetaMorphoV1_1Immutables) :
    evalExprs? config (p.signerFrame evm v p.owner) state
      [.var "owner", .var "spender", .var "value"] =
      .ok [.address p.owner, .address p.spender, uint256Value p.value] := by
  simp [evalExprs?, evalExpr?, PermitData.signerFrame, PermitData.hashFrame,
    PermitData.nonceFrame, PermitData.entryFrame, PermitData.locals, Std.HashMap.getElem_insert,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem permitApprovalReverts {p : PermitData} {evm state : State}
    {v : MetaMorphoV1_1Immutables}
    (hbad : ¬ (p.owner ≠ AccountAddress.ofNat 0 ∧ p.spender ≠ AccountAddress.ofNat 0)) :
    ExecBlock config (p.signerFrame evm v p.owner) state
      (permitTransition.body.drop 8) .reverted := by
  apply ExecBlock.consNormal (ExecStmt.requireTrue (by
    simpa only [decide_true] using permitSignerSource p evm state v p.owner))
  exact ExecBlock.consRevert (approveCallReverts (permitApprovalArgs p evm state v) hbad)

theorem permitApprovalReturns {p : PermitData} {evm state : State}
    {v : MetaMorphoV1_1Immutables}
    (ho : p.owner ≠ AccountAddress.ofNat 0) (hsp : p.spender ≠ AccountAddress.ofNat 0) :
    ∃ frame, ExecBlock config (p.signerFrame evm v p.owner) state
      (permitTransition.body.drop 8) (.ok frame (approvalState state p.owner p.spender p.value)) :=
      by
  refine ⟨_, ExecBlock.consNormal (ExecStmt.requireTrue ?_)
    (ExecBlock.consNormal (approveCall (permitApprovalArgs p evm state v) ho hsp) ExecBlock.nil)⟩
  simpa only [decide_true] using permitSignerSource p evm state v p.owner

end Benchmarks.Morpho.MetaMorphoV1_1
