import Benchmarks.CurveVault.MutatingLock
import Benchmarks.CurveVault.MutationSites
import Benchmarks.CurveVault.RuntimeBlocks_010
import Benchmarks.CurveVault.RuntimeBlocks_013
import Benchmarks.CurveVault.RuntimeBlocks_015
import Benchmarks.CurveVault.RuntimeBlocks_018
import Benchmarks.CurveVault.RuntimeBlocks_031
import Benchmarks.CurveVault.Entry

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

namespace VaultFlow
def lockEntry : VaultFlow → Nat
  | .deposit => 2159 | .mint => 3162 | .withdraw => 4178 | .redeem => 5080
def bodyEntry : VaultFlow → Nat
  | .deposit => 2169 | .mint => 3172 | .withdraw => 4188 | .redeem => 5090
end VaultFlow

def vaultMutationEntryBody (name : Ident) (args : List Expr) : List Stmt :=
  [.require vaultLockExpr, vaultLockAssignStmt ⟨1⟩, .internalCall name args "__r",
    vaultLockAssignStmt ⟨0⟩, .return [.var "__r"]]

theorem vaultMutationEntry (flow : VaultFlow) {σ σ₀ A I} {g : UInt256} {t : TransitionDecl}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    {decoded locals : Store} {stmts : List Stmt} {name : Ident} {args : List Expr}
    (hcode : I.code = vaultBytecode) (hd : dispatchMsg contract I.calldata = some t)
    (hdec : config.externalABI.decodeCalldata? (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some decoded)
    (hbody : t.body = stmts ++ vaultMutationEntryBody name args)
    (hretTy : t.returnType = [.elem (.int (.uint ⟨256, by decide⟩))])
    (hprefix : ExecBlock fork config {contract := contract, locals := decoded}
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) stmts
      (.ok {contract := contract, locals := locals} (initState σ σ₀ (Sat256.ofUInt256 g) A I)))
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork vaultBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat flow.lockEntry) R mem aw rdata σ k C)
    (hrun : ∀ {aw0 : UInt256} {k0 C0 : Nat}, I.perm = true →
      RD fork vaultBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (UInt256.ofNat flow.bodyEntry) R mem aw0 rdata σ k0 C0 →
      (∃ (evm1 : State) (σ1 : AccountMap) (value : UInt256),
        ExecStmt fork config {contract := contract, locals := locals}
          (vaultSetLock (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1⟩) (.internalCall name args "__r")
          (.ok {contract := contract, locals := locals.insert "__r" (.int (Int.ofNat value.toNat))} evm1) ∧
        SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ1 evm1 ∧
        RDret fork vaultBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (tstoreAccountMap I.codeOwner σ1 ⟨0⟩ ⟨0⟩) value.toByteArray) ∨
      (ExecStmt fork config {contract := contract, locals := locals}
        (vaultSetLock (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1⟩) (.internalCall name args "__r") .reverted ∧
        RDrev fork vaultBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I))) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hload : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ = codeOwnerTransientWord I σ ⟨0⟩ :=
    codeOwnerTransientWord_initState _
  by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
  · have hrev : RDrev fork vaultBytecode (Sat256.ofUInt256 g) evm := by
      cases flow
      · obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_2159_taken_packed (by omega)
          (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _; rw [hlocked]; decide +kernel)
          (by native_decide) h
        exact vaultBlocks.vault_block_8284 (by omega) rdFail
      · obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_3162_taken_packed (by omega)
          (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _; rw [hlocked]; decide +kernel)
          (by native_decide) h
        exact vaultBlocks.vault_block_8284 (by omega) rdFail
      · obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_4178_taken_packed (by omega)
          (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _; rw [hlocked]; decide +kernel)
          (by native_decide) h
        exact vaultBlocks.vault_block_8284 (by omega) rdFail
      · obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_5080_taken_packed (by omega)
          (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _; rw [hlocked]; decide +kernel)
          (by native_decide) h
        exact vaultBlocks.vault_block_8284 (by omega) rdFail
    have hsource : ExecTransitionBody fork config contract evm decoded t.body .reverted := by
      apply ExecFuncBody.execBlockRevert
      rw [hbody]
      exact execBlock_append hprefix (ExecBlock.consRevert (ExecStmt.requireFalse
        (vaultLockEval_fail evm locals (by rw [hload]; exact hlocked))))
    exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  have hbodyReach : ∃ aw0 k0 C0, RD fork vaultBytecode I (Sat256.ofUInt256 g) evm
      (UInt256.ofNat flow.bodyEntry) R mem aw0 rdata σ k0 C0 := by
    cases flow
    · exact vaultBlocks.vault_block_2159_fallthrough_packed (by omega) (u256_eq_of_ne (Ne.symm hlocked)) h
    · exact vaultBlocks.vault_block_3162_fallthrough_packed (by omega) (u256_eq_of_ne (Ne.symm hlocked)) h
    · exact vaultBlocks.vault_block_4178_fallthrough_packed (by omega) (u256_eq_of_ne (Ne.symm hlocked)) h
    · exact vaultBlocks.vault_block_5080_fallthrough_packed (by omega) (u256_eq_of_ne (Ne.symm hlocked)) h
  obtain ⟨aw0, k0, C0, rdBody⟩ := hbodyReach
  have hlock : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨1⟩ := by
    rw [hload]; exact hlocked
  have hlockStmt := ExecStmt.requireTrue (fork := fork) (vaultLockEval_pass evm locals hlock)
  by_cases hperm : I.perm = true
  swap
  · have hp : I.perm = false := by simpa using hperm
    have rdPushOne := rdBody.push1 (UInt256.ofNat 1) (by cases flow <;> native_decide) (by omega)
    have rdStore := rdPushOne.push0 (by cases flow <;> native_decide) (by simp only [List.length_cons]; omega)
    have hstatic := tstoreStaticReach rdStore hp (by cases flow <;> native_decide) (by omega)
    have hsource : ExecTransitionBody fork config contract evm decoded t.body .staticViolation := by
      apply ExecFuncBody.execBlockStatic
      rw [hbody]
      apply execBlock_append hprefix
      exact ExecBlock.consNormal hlockStmt (ExecBlock.consStatic (ExecStmt.assignTransientStatic
        (value := .int 1) (by simp [evalExpr?, pure]; rfl) (vaultLockAssign evm locals ⟨1⟩) hp))
    exact hstatic.reEquivStaticHalt hcode hd hdec hsource
  rcases hrun hperm rdBody with ⟨evm1, σ1, shares, hcall, hs1, hret⟩ | ⟨hcall, hrev⟩
  swap
  · have hsource : ExecTransitionBody fork config contract evm decoded t.body .reverted := by
      apply ExecFuncBody.execBlockRevert
      rw [hbody]
      apply execBlock_append hprefix
      exact ExecBlock.consNormal hlockStmt (ExecBlock.consNormal (vaultLockSet (fork := fork) (hperm := by assumption) evm locals ⟨1⟩)
        (ExecBlock.consRevert hcall))
    exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  have hsource : ExecTransitionBody fork config contract evm decoded t.body
      (.returned {contract := contract, locals := locals.insert "__r" (.int (Int.ofNat shares.toNat))}
        (vaultSetLock evm1 ⟨0⟩) (some [.int (Int.ofNat shares.toNat)])) := by
    apply ExecFuncBody.execBlockRet
    rw [hbody]
    apply execBlock_append hprefix
    apply ExecBlock.consNormal hlockStmt
    apply ExecBlock.consNormal (vaultLockSet (fork := fork) (hperm := by assumption) evm locals ⟨1⟩)
    apply ExecBlock.consNormal hcall
    apply ExecBlock.consNormal (vaultLockSet (fork := fork) (hperm := (congrArg ExecutionEnv.perm hs1.env).trans hperm) _ _ ⟨0⟩)
    exact ExecBlock.consReturn (ExecStmt.return (by
      simp only [evalExprs?, evalExpr?, store_get_self, collapseReturns, EvalResult.ofOption, EvalResult.bind, pure, bind]))
  have hsFinal : SourceState evm I (tstoreAccountMap I.codeOwner σ1 ⟨0⟩ ⟨0⟩) (vaultSetLock evm1 ⟨0⟩) := by
    unfold vaultSetLock
    rw [hs1.env]
    exact sourceStateTransientWrite hs1 ⟨0⟩ ⟨0⟩
  exact hret.reEquivExecutionGen hcode hd hdec hsource hsFinal.accounts
    (by rw [hretTy]; exact returnEquiv_of_encode (uint256ReturnEncoding _))

end Benchmarks.CurveVault
