import Benchmarks.Safe.OwnerCount
import Benchmarks.Safe.Threshold

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def thresholdChangeStmt : Stmt :=
  .ite (neE (.storage thresholdRef) (.var "_threshold"))
    [.internalCall "changeThresholdBody" [.var "_threshold"] "_thresholdChanged"] []

theorem safeThresholdChangeGuard (evm : EVM.State) (locals : Store) (value : UInt256)
    (hb : locals["threshold"]? = none)
    (he : evalExpr? config { contract := contract, locals := locals } evm (.var "_threshold") =
      .ok (.int (Int.ofNat value.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm
      (neE (.storage thresholdRef) (.var "_threshold")) =
      .ok (.bool (decide (storedThreshold evm ≠ value))) := by
  rw [neE, evalExpr_binary_nonshort (by decide) (by decide), safeEvalStoredThreshold evm locals
    hb, he]
  simp [evalBinaryOp?, EvalResult.bind, bind, pure]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, Int.natCast_inj, decide_eq_true_eq]
  exact ⟨u256_inj, congrArg UInt256.toNat⟩

theorem safeThresholdChangeUnchanged (evm : EVM.State) (locals : Store) (value : UInt256)
    (hb : locals["threshold"]? = none)
    (he : evalExpr? config { contract := contract, locals := locals } evm (.var "_threshold") =
      .ok (.int (Int.ofNat value.toNat)))
    (ht : storedThreshold evm = value) :
    ExecStmt config { contract := contract, locals := locals } evm thresholdChangeStmt
      (.ok { contract := contract, locals := locals } evm) :=
  .iteFalse (by simpa only [ht, ne_eq, not_true_eq_false, decide_false] using
    safeThresholdChangeGuard evm locals value hb he) .nil

theorem safeThresholdChangeChanged (evm : EVM.State) (locals : Store) (value : UInt256)
    (hb : locals["threshold"]? = none)
    (he : evalExpr? config { contract := contract, locals := locals } evm (.var "_threshold") =
      .ok (.int (Int.ofNat value.toNat)))
    (ht : storedThreshold evm ≠ value)
    (hle : value.toNat ≤ (ownerCount evm).toNat) (hnz : value ≠ ⟨0⟩) :
    ExecStmt config { contract := contract, locals := locals } evm thresholdChangeStmt
      (.ok (resumeAfterInternalCall { contract := contract, locals := locals }
        "_thresholdChanged" none)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ value)) := by
  have hcall := internalCallFunctionReturn
    (caller := { contract := contract, locals := locals })
    (name := "changeThresholdBody") (retVar := "_thresholdChanged")
    (callee := changeThresholdBodyFunction) (evalExprs?_singleton he) rfl rfl
    (safeThresholdSource evm value hle hnz)
  exact .iteTrue (by simpa [ht] using safeThresholdChangeGuard evm locals value hb he)
    (.consNormal hcall .nil)

theorem safeThresholdChangeRevert (evm : EVM.State) (locals : Store) (value : UInt256)
    (hb : locals["threshold"]? = none)
    (he : evalExpr? config { contract := contract, locals := locals } evm (.var "_threshold") =
      .ok (.int (Int.ofNat value.toNat)))
    (ht : storedThreshold evm ≠ value)
    (hbody : ExecFuncBody config (thresholdFrame value) evm changeThresholdBodyFunction.body
      .reverted) :
    ExecStmt config { contract := contract, locals := locals } evm thresholdChangeStmt
      .reverted := by
  have hcall := internalCallFunctionRevert
    (caller := { contract := contract, locals := locals })
    (name := "changeThresholdBody") (retVar := "_thresholdChanged")
    (callee := changeThresholdBodyFunction) (evalExprs?_singleton he) rfl rfl hbody
  exact .iteTrue (by simpa [ht] using safeThresholdChangeGuard evm locals value hb he)
    (.consRevert hcall)

end Benchmarks.Safe
