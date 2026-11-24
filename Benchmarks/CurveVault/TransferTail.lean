import Benchmarks.CurveVault.TransferGuard
import Benchmarks.CurveVault.Memory
import Benchmarks.CurveVault.Arithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultTransferMemory (mem : ByteArray) (sender recipient value : UInt256) : ByteArray :=
  value.toByteArray.write 0
    (wordAt0Mem ⟨13⟩ (wordAt32Mem recipient (wordAt0Mem ⟨13⟩ (wordAt32Mem sender mem)))) 160 32

theorem vaultTransferMemory_frame (mem : ByteArray) (sender recipient value : UInt256) :
    WordMemoryRange mem (vaultTransferMemory mem sender recipient value) 192 UInt256.size := by
  exact (wordMemoryRange_vyperHash mem ⟨13⟩ sender 192 UInt256.size (by omega)).trans
    ((wordMemoryRange_vyperHash _ ⟨13⟩ recipient 192 UInt256.size (by omega)).trans
      (wordMemoryRange_write _ value 160 192 UInt256.size
        (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 160 (by omega))) (Or.inr (by omega))))

theorem vaultTransferTail {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sender recipient value returnPc : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 160 ≤ mem.size)
    (hmf : memLoad (UInt256.ofNat 64) mem = sender)
    (hmt : memLoad (UInt256.ofNat 96) mem = recipient)
    (hmv : memLoad (UInt256.ofNat 128) mem = value)
    (hcanon0 : sender.toNat < EVM.addressModulus) (hcanon1 : recipient.toNat < EVM.addressModulus)
    (hbase : locals.get? "balanceOf" = none)
    (hf : locals.get? "_from" = some (.address (AccountAddress.ofNat sender.toNat)))
    (ht : locals.get? "_to" = some (.address (AccountAddress.ofNat recipient.toNat)))
    (hv : locals.get? "_value" = some (.int (Int.ofNat value.toNat)))
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 8161) (returnPc :: R) mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (aw' : UInt256) (k' C' : Nat),
      ExecBlock fork config {contract := contract, locals := locals} evm (vaultTransferFunction.body.drop 1)
        (.ok {contract := contract, locals := locals} evm') ∧
      SourceState s0 I σ' evm' ∧
      RD fork vaultBytecode I g s0 returnPc R (vaultTransferMemory mem sender recipient value) aw' rdata σ' k' C') ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm (vaultTransferFunction.body.drop 1)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let slotFrom := vyperMappingSlot ⟨13⟩ (.address (AccountAddress.ofNat sender.toNat))
  let slotTo := vyperMappingSlot ⟨13⟩ (.address (AccountAddress.ofNat recipient.toNat))
  let old := codeOwnerStorageWord I σ slotFrom
  let debit := UInt256.sub old value
  let mem0 := wordAt0Mem ⟨13⟩ (wordAt32Mem sender mem)
  let mem1 := wordAt0Mem ⟨13⟩ (wordAt32Mem recipient mem0)
  have hsize0 : mem0.size = mem.size := vyperHashMem_size _ _ _ (by omega)
  have ht0 : memLoad (UInt256.ofNat 96) mem0 = recipient := by
    rw [memLoad_vyperHashMem _ _ _ _ (by omega) (by omega) (by decide +kernel), hmt]
  have hv0 : memLoad (UInt256.ofNat 128) mem0 = value := by
    rw [memLoad_vyperHashMem _ _ _ _ (by omega) hsize (by decide +kernel), hmv]
  have hv1 : memLoad (UInt256.ofNat 128) mem1 = value := by
    rw [memLoad_vyperHashMem _ _ _ _ (by omega) (by rw [hsize0]; exact hsize) (by decide +kernel), hv0]
  have hhash0 := vyperHashMem_address ⟨13⟩ sender mem (by omega) hcanon0
  have hhash1 := vyperHashMem_address ⟨13⟩ recipient mem0 (by rw [hsize0]; omega) hcanon1
  have hread : evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "balanceOf", steps := [.mindex (.var "_from")]}) =
      .ok (.int (Int.ofNat old.toNat)) := by
    simpa only [hs.storageRead] using vaultBalanceEval evm locals "_from" _ hbase hf
  have hvEval (state : State) := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := state) hv
  have hcondition : UInt256.gt
      (UInt256.sub (codeOwnerStorageWord I σ
        (keccakWord ⟨0⟩ (UInt256.ofNat 64) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem))))
        (memLoad (UInt256.ofNat 128) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem))))
      (codeOwnerStorageWord I σ
        (keccakWord ⟨0⟩ (UInt256.ofNat 64) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem)))) =
        UInt256.gt debit old := by rw [hmf, hhash0, hv0]
  by_cases hsub : value.toNat ≤ old.toNat
  swap
  · have hlt : old.toNat < value.toNat := by omega
    obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_8161_taken_packed
      (by simp only [List.length_cons]; omega)
      (ne_of_eq_of_ne hcondition (by rw [u256_sub_underflow_gt _ _ hlt]; decide +kernel)) (by native_decide) h
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_8161_taken_stack, List.length_cons]; omega) rdFail
    exact Or.inr ⟨ExecBlock.consRevert (ExecStmt.assignExprRevert
      (evalExpr_checkedSub256_revert hread (hvEval evm) hlt)), hrev⟩
  obtain ⟨aw0, k0, C0, rd8190⟩ := vaultBlocks.vault_block_8161_fallthrough_packed
    (by simp only [List.length_cons]; omega)
    (hcondition.trans (ugt_zero (by rw [usub_toNat hsub]; omega))) h
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 8190)
    (UInt256.sub (codeOwnerStorageWord I σ
      (keccakWord ⟨0⟩ (UInt256.ofNat 64) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem))))
      (memLoad (UInt256.ofNat 128) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem))) ::
      memLoad (UInt256.ofNat 128) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem)) ::
      codeOwnerStorageWord I σ (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem))) ::
      keccakWord ⟨0⟩ (UInt256.ofNat 64) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem)) ::
      returnPc :: R)
    (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem)) aw0 rdata σ k0 C0 at rd8190
  rw [hmf, hhash0, hv0] at rd8190
  let σ1 := sstoreAccountMap I.codeOwner σ slotFrom debit
  let evm1 := Stele.EVM.storageStore evm I.codeOwner slotFrom debit
  have hs1 : SourceState s0 I σ1 evm1 := hs.storageWrite _ _
  have hdebit : ExecStmt fork config {contract := contract, locals := locals} evm
      vaultTransferFunction.body[1]!
      (.ok {contract := contract, locals := locals} evm1) := by
    apply ExecStmt.assign (hperm := Or.inr (by simpa only [hs.env] using hperm)) (evalExpr_checkedSub256_ok hread (hvEval evm) rfl hsub)
    simpa only [hs.env] using vaultBalanceAssign evm locals "_from" _ debit hbase hf
  let oldTo := codeOwnerStorageWord I σ1 slotTo
  have hreadTo : evalExpr? config {contract := contract, locals := locals} evm1
      (.storage {base := "balanceOf", steps := [.mindex (.var "_to")]}) =
      .ok (.int (Int.ofNat oldTo.toNat)) := by
    simpa only [hs1.storageRead] using vaultBalanceEval evm1 locals "_to" _ hbase ht
  have hcondition1 : UInt256.lt
      (codeOwnerStorageWord I σ1
        (keccakWord ⟨0⟩ (UInt256.ofNat 64) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 96) mem0) mem0))) +
        memLoad (UInt256.ofNat 128) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 96) mem0) mem0)))
      (codeOwnerStorageWord I σ1
        (keccakWord ⟨0⟩ (UInt256.ofNat 64) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 96) mem0) mem0)))) =
      UInt256.lt (oldTo + value) oldTo := by rw [ht0, hhash1, hv1]
  by_cases hadd : oldTo.toNat + value.toNat < UInt256.size
  swap
  · have hover : UInt256.size ≤ oldTo.toNat + value.toNat := by omega
    obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_8190_taken_packed
      (by simp only [List.length_cons]; omega) hperm
      (ne_of_eq_of_ne hcondition1 (by rw [u256_add_overflow_lt _ _ hover]; decide +kernel)) (by native_decide) rd8190
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_8190_taken_stack, List.length_cons]; omega) rdFail
    exact Or.inr ⟨ExecBlock.consNormal hdebit (ExecBlock.consRevert
      (ExecStmt.assignExprRevert (evalExpr_add256_revert hreadTo (hvEval evm1) hover))), hrev⟩
  obtain ⟨aw1, k1, C1, rd8226⟩ := vaultBlocks.vault_block_8190_fallthrough_packed
    (by simp only [List.length_cons]; omega) hperm
    (hcondition1.trans (ult_zero (by rw [uadd_toNat, Nat.mod_eq_of_lt hadd]; omega))) rd8190
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 8226)
    ((codeOwnerStorageWord I σ1
      (keccakWord ⟨0⟩ (UInt256.ofNat 64) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 96) mem0) mem0))) +
      memLoad (UInt256.ofNat 128) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 96) mem0) mem0))) ::
      memLoad (UInt256.ofNat 128) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 96) mem0) mem0)) ::
      codeOwnerStorageWord I σ1 (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 96) mem0) mem0))) ::
      keccakWord ⟨0⟩ (UInt256.ofNat 64) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 96) mem0) mem0)) ::
      returnPc :: R)
    (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 96) mem0) mem0)) aw1 rdata σ1 k1 C1 at rd8226
  rw [ht0, hhash1, hv1] at rd8226
  obtain ⟨aw2, k2, C2, rdReturn⟩ := vaultBlocks.vault_block_8226_packed (by omega) hperm hvalid rd8226
  change RD fork vaultBytecode I g s0 returnPc R ((memLoad (UInt256.ofNat 128) mem1).toByteArray.write 0 mem1 160 32)
    aw2 rdata (sstoreAccountMap I.codeOwner σ1 slotTo (oldTo + value)) k2 C2 at rdReturn
  rw [hv1] at rdReturn
  let evm2 := Stele.EVM.storageStore evm1 I.codeOwner slotTo (oldTo + value)
  have hs2 : SourceState s0 I (sstoreAccountMap I.codeOwner σ1 slotTo (oldTo + value)) evm2 := hs1.storageWrite _ _
  refine Or.inl ⟨evm2, _, aw2, k2, C2, ?_, hs2, rdReturn⟩
  apply ExecBlock.consNormal hdebit
  have hcredit : ExecStmt fork config {contract := contract, locals := locals} evm1
      vaultTransferFunction.body[2]! (.ok {contract := contract, locals := locals} evm2) := by
    apply ExecStmt.assign (hperm := Or.inr (by simpa only [hs1.env] using hperm)) (evalExpr_add256_ok hreadTo (hvEval evm1) rfl hadd)
    simpa only [hs1.env] using vaultBalanceAssign evm1 locals "_to" _ (oldTo + value) hbase ht
  apply ExecBlock.consNormal hcredit
  refine ExecBlock.consNormal (ExecStmt.emit (fork := fork) (hperm := by simpa only [hs2.env] using hperm) (vals := [.address (AccountAddress.ofNat sender.toNat),
    .address (AccountAddress.ofNat recipient.toNat), .int (Int.ofNat value.toNat)]) ?_) ExecBlock.nil
  change evalExprs? config {contract := contract, locals := locals} evm2 [.var "_from", .var "_to", .var "_value"] = _
  simp only [evalExprs?, evalExpr?, hf, ht, hv, EvalResult.ofOption, EvalResult.bind, bind, pure]

end Benchmarks.CurveVault
