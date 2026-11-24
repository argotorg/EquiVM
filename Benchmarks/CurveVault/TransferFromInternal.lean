import Benchmarks.CurveVault.TransferFromPrepare

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultTransferFromRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sender recipient : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 256 ≤ mem.size)
    (hmf : memLoad (UInt256.ofNat 192) mem = sender)
    (hmt : memLoad (UInt256.ofNat 224) mem = recipient)
    (hcanon0 : sender.toNat < EVM.addressModulus) (hcanon1 : recipient.toNat < EVM.addressModulus)
    (hbase : locals.get? "allowance" = none)
    (hf : locals.get? "_from" = some (.address (AccountAddress.ofNat sender.toNat)))
    (ht : locals.get? "_to" = some (.address (AccountAddress.ofNat recipient.toNat)))
    (hv : locals.get? "_value" = some (.int (Int.ofNat (calldataWord I.calldata 68).toNat)))
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 5726) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store),
      ExecFuncBody fork config {contract := contract, locals := locals} (vaultSetLock evm ⟨1⟩) vaultTransferFromFunction.body
        (.returned {contract := contract, locals := locals'} evm' (some [.bool true])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) (⟨1⟩ : UInt256).toByteArray) ∨
    (ExecFuncBody fork config {contract := contract, locals := locals} (vaultSetLock evm ⟨1⟩)
      vaultTransferFromFunction.body .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let evm0 := vaultSetLock evm ⟨1⟩
  let σ0 := tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩
  let old := codeOwnerStorageWord I σ0 (vaultAllowanceSlot (AccountAddress.ofNat sender.toNat) I.source)
  let locals0 := locals.insert "allowance_" (.int (Int.ofNat old.toNat))
  have hs0 : SourceState s0 I σ0 evm0 := by
    unfold evm0 vaultSetLock
    rw [hs.env]
    exact sourceStateTransientWrite hs ⟨0⟩ ⟨1⟩
  have hread := vaultAllowanceEvalAt evm0 locals (.var "_from") (.env .caller)
    (AccountAddress.ofNat sender.toNat) I.source hbase
    (by rw [evalExpr?]; simp only [hf, EvalResult.ofOption])
    (by simp only [evalExpr?, envValue, hs0.env, pure])
  rw [hs0.storageRead] at hread
  have hlet : ExecStmt fork config {contract := contract, locals := locals} evm0 vaultTransferFromFunction.body[0]!
      (.ok {contract := contract, locals := locals0} evm0) := ExecStmt.letDecl hread
  have ha0 : locals0.get? "allowance_" = some (.int (Int.ofNat old.toNat)) := store_get_self _ _ _
  have hf0 : locals0.get? "_from" = some (.address (AccountAddress.ofNat sender.toNat)) := by
    rw [store_get_ne _ _ (by decide +kernel)]; exact hf
  have ht0 : locals0.get? "_to" = some (.address (AccountAddress.ofNat recipient.toNat)) := by
    rw [store_get_ne _ _ (by decide +kernel)]; exact ht
  have hv0 : locals0.get? "_value" = some (.int (Int.ofNat (calldataWord I.calldata 68).toNat)) := by
    rw [store_get_ne _ _ (by decide +kernel)]; exact hv
  have hevalOld := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm0) ha0
  have hevalMax : evalExpr? config {contract := contract, locals := locals0} evm0 (.intLit (UInt256.size - 1)) =
      .ok (.int (Int.ofNat (UInt256.ofNat (UInt256.size - 1)).toNat)) := by simp [evalExpr?, pure]; rfl
  obtain ⟨mem0, aw0, k0, C0, hsize0, hframe0, hma0, rdNext⟩ := vaultTransferFromPrepare hsize hmf hcanon0
    (show codeOwnerStorageWord I σ0 (vaultAllowanceSlot (AccountAddress.ofNat sender.toNat) I.source) = old from rfl)
    hperm (by omega) h
  have hmf0 : memLoad (UInt256.ofNat 192) mem0 = sender := by
    rw [hframe0.load 192 (by omega) (by omega) (by omega) (by decide +kernel), hmf]
  have hprefix :
      (∃ (evm1 : State) (σ1 : AccountMap) (locals1 : Store) (mem1 : ByteArray) (aw1 : UInt256) (k1 C1 : Nat),
        ExecBlock fork config {contract := contract, locals := locals} evm0 (vaultTransferFromFunction.body.take 2)
          (.ok {contract := contract, locals := locals1} evm1) ∧
        SourceState s0 I σ1 evm1 ∧ WordMemoryRange mem mem1 192 256 ∧
        locals1.get? "_from" = some (.address (AccountAddress.ofNat sender.toNat)) ∧
        locals1.get? "_to" = some (.address (AccountAddress.ofNat recipient.toNat)) ∧
        locals1.get? "_value" = some (.int (Int.ofNat (calldataWord I.calldata 68).toNat)) ∧
        RD fork vaultBytecode I g s0 (UInt256.ofNat 5845) R mem1 aw1 rdata σ1 k1 C1) ∨
      (ExecFuncBody fork config {contract := contract, locals := locals} evm0 vaultTransferFromFunction.body .reverted ∧
        RDrev fork vaultBytecode g s0) := by
    by_cases hmax : old = UInt256.ofNat (UInt256.size - 1)
    · rw [if_pos hmax] at rdNext
      refine Or.inl ⟨evm0, σ0, locals0, mem0, aw0, k0, C0, ?_, hs0, hframe0, hf0, ht0, hv0, rdNext⟩
      exact ExecBlock.consNormal hlet (ExecBlock.consNormal (ExecStmt.iteFalse
        (evalExpr_ne_int_false hevalOld hevalMax (by rw [hmax])) ExecBlock.nil) ExecBlock.nil)
    · rw [if_neg hmax] at rdNext
      have hcond := evalExpr_ne_int_true hevalOld hevalMax (fun hn => hmax (u256_inj (Int.ofNat.inj hn)))
      rcases vaultTransferFromApprove hs0 hsize0 hmf0 hma0 hcanon0 hf0 ha0 hv0 hperm hstack rdNext with
        ⟨evm1, σ1, mem1, aw1, k1, C1, hcall, hs1, hframe1, rd5845⟩ | ⟨hcall, hrev⟩
      swap
      · exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consNormal hlet
          (ExecBlock.consRevert (ExecStmt.iteTrue hcond (ExecBlock.consRevert hcall)))), hrev⟩
      refine Or.inl ⟨evm1, σ1, locals0.insert "__c0" .unit, mem1, aw1, k1, C1,
        ExecBlock.consNormal hlet (ExecBlock.consNormal
          (ExecStmt.iteTrue hcond (ExecBlock.consNormal hcall ExecBlock.nil)) ExecBlock.nil), hs1,
        hframe0.trans (hframe1.mono (le_refl _) (by decide +kernel)), ?_, ?_, ?_, rd5845⟩
      · rw [store_get_ne _ _ (by decide +kernel)]; exact hf0
      · rw [store_get_ne _ _ (by decide +kernel)]; exact ht0
      · rw [store_get_ne _ _ (by decide +kernel)]; exact hv0
  rcases hprefix with ⟨evm1, σ1, locals1, mem1, aw1, k1, C1, hprefix, hs1, hframe1, hf1, ht1, hv1, rd5845⟩ | hrev
  swap
  · exact Or.inr hrev
  have hmf1 : memLoad (UInt256.ofNat 192) mem1 = sender := by
    rw [hframe1.load 192 (by omega) (by omega) (by omega) (by decide +kernel), hmf]
  have hmt1 : memLoad (UInt256.ofNat 224) mem1 = recipient := by
    rw [hframe1.load 224 (by omega) (by omega) hsize (by decide +kernel), hmt]
  rcases vaultTransferFromTail hs1 (le_trans hsize hframe1.size) hmf1 hmt1 hcanon0 hcanon1 hf1 ht1 hv1 hperm hstack rd5845 with
    ⟨evm', σ', htail, hs', hret⟩ | ⟨htail, hrev⟩
  · refine Or.inl ⟨evm', σ', locals1.insert "__c1" .unit, ExecFuncBody.execBlockRet ?_, hs', hret⟩
    have hbody : vaultTransferFromFunction.body = vaultTransferFromFunction.body.take 2 ++ vaultTransferFromFunction.body.drop 2 := rfl
    rw [hbody]
    exact execBlock_append hprefix htail
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    have hbody : vaultTransferFromFunction.body = vaultTransferFromFunction.body.take 2 ++ vaultTransferFromFunction.body.drop 2 := rfl
    rw [hbody]
    exact execBlock_append hprefix htail

end Benchmarks.CurveVault
