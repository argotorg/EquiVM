import Benchmarks.Safe.SetupOwnersContext

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeSetupOwnersDifferent (evm : EVM.State) {p locals i current}
    (h : SetupOwnersLocals p locals i current) (owner : UInt256)
    (hc : current.toNat < EVM.addressModulus) (ho : owner.toNat < EVM.addressModulus) :
    evalExpr? config
      { contract := contract, locals := locals.insert "owner" (addressArrayValue owner) } evm
      (neE (.var "owner") (.var "currentOwner")) =
      .ok (.bool (decide (owner ≠ current))) := by
  apply evalAddressNe ho hc
  · exact evalLocalValue (by simp [addressArrayValue])
  · exact evalLocalValue (h.set "owner" (addressArrayValue owner) (by decide)).current

theorem safeSetupOwnersRepeated (evm : EVM.State) {p locals i current}
    (h : SetupOwnersLocals p locals i current) (hi : i < p.owners.length)
    (hc : current.toNat < EVM.addressModulus) (he : p.owners[i] = current) :
    ExecBlock config { contract := contract, locals := locals } evm setupOwnersLoopBody
      .reverted := by
  refine .consNormal (.letDecl (safeSetupOwnersIndex evm h hi))
    (.consRevert (.requireFalse ?_))
  simpa only [he, ne_eq, not_true_eq_false, decide_false] using
    safeSetupOwnersDifferent evm h p.owners[i] hc (by rwa [he])

theorem safeSetupOwnersGuardRevert (evm : EVM.State) {p locals i current}
    (h : SetupOwnersLocals p locals i current) (hi : i < p.owners.length)
    (hc : current.toNat < EVM.addressModulus) (ho : p.owners[i].toNat < EVM.addressModulus)
    (he : p.owners[i] ≠ current)
    (hbody : ExecFuncBody config (canAddOwnerFrame p.owners[i]) evm
      requireCanAddOwnerFunction.body .reverted) :
    ExecBlock config { contract := contract, locals := locals } evm setupOwnersLoopBody
      .reverted := by
  refine .consNormal (.letDecl (safeSetupOwnersIndex evm h hi))
    (.consNormal (.requireTrue (by
      have hg := safeSetupOwnersDifferent evm h p.owners[i] hc ho
      rw [decide_eq_true he] at hg
      exact hg))
      (.consRevert ?_))
  exact safeInternalCanAddOwner rfl rfl (evalLocalValue (by simp)) hbody

theorem safeSetupOwnersWrite (evm : EVM.State) {p locals i current}
    (h : SetupOwnersLocals p locals i current) (owner : UInt256)
    (hc : current.toNat < EVM.addressModulus) (ho : owner.toNat < EVM.addressModulus)
    (hfit : i + 1 < UInt256.size) :
    ExecBlock config { contract := contract, locals := setupOwnersCheckedLocals locals owner } evm
      (setupOwnersLoopBody.drop 3)
      (.ok { contract := contract, locals := setupOwnersNextLocals locals owner i }
        (writeOwnerLink evm current owner)) := by
  have hh := h.checked owner
  have howner : (setupOwnersCheckedLocals locals owner)["owner"]? =
      some (addressArrayValue owner) := by
    simp [setupOwnersCheckedLocals, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  have hassign := safeAssignOwnerLink evm _ (.var "currentOwner") current owner
    hh.ownersAbsent hc ho (evalLocalValue hh.current)
  have hindex : ((setupOwnersCheckedLocals locals owner).insert "currentOwner"
      (addressArrayValue owner))["i"]? = some (.int (Int.ofNat i)) := by
    simpa [Std.HashMap.getElem?_insert] using hh.index
  exact .consNormal (.assign (evalLocalValue howner) hassign)
    (.consNormal (.assign (evalLocalValue howner) (assignLocalVarBase_ok hh.current))
      (.consNormal (.assign (evalNatIncrement (evalLocalValue hindex) hfit)
        (assignLocalVarBase_ok hindex)) .nil))

theorem safeSetupOwnersStep (evm : EVM.State) {p locals i current}
    (h : SetupOwnersLocals p locals i current) (hi : i < p.owners.length)
    (hc : current.toNat < EVM.addressModulus) (ho : p.owners[i].toNat < EVM.addressModulus)
    (he : p.owners[i] ≠ current) (hfit : i + 1 < UInt256.size)
    (hv : validOwner evm.accountMap evm.executionEnv p.owners[i])
    (hempty : ownerLink evm p.owners[i] = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := locals } evm setupOwnersLoopBody
      (.ok { contract := contract, locals := setupOwnersNextLocals locals p.owners[i] i }
        (writeOwnerLink evm current p.owners[i])) := by
  have hcall := safeInternalCanAddOwner (caller := {
      contract := contract
      locals := locals.insert "owner" (addressArrayValue p.owners[i]) })
    (expr := .var "owner") (retVar := "_ok") rfl rfl (evalLocalValue (by simp))
    (safeCanAddOwnerSource evm p.owners[i] ho hv hempty)
  exact .consNormal (.letDecl (safeSetupOwnersIndex evm h hi))
    (.consNormal (.requireTrue (by
      have hg := safeSetupOwnersDifferent evm h p.owners[i] hc ho
      rw [decide_eq_true he] at hg
      exact hg))
      (.consNormal hcall (safeSetupOwnersWrite evm h p.owners[i] hc ho hfit)))

end Benchmarks.Safe
