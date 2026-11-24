import Benchmarks.CurveVault.SupplyMemory
import Benchmarks.CurveVault.RuntimeBlocks_030
import Benchmarks.CurveVault.RuntimeBlocks_031
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultBurnFunction : FunctionDecl := contract.functions[34]!

def vaultBurnLocals (sender : AccountAddress) (value : UInt256) : Store :=
  ((∅ : Store).insert "_value" (.int (Int.ofNat value.toNat))).insert "_from" (.address sender)

theorem vaultBurnRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sender value returnPc : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 128 ≤ mem.size)
    (hmt : memLoad (UInt256.ofNat 64) mem = sender)
    (hmv : memLoad (UInt256.ofNat 96) mem = value)
    (hcanon : sender.toNat < EVM.addressModulus)
    (hbase : locals.get? "balanceOf" = none) (hsupply : locals.get? "totalSupply" = none)
    (ht : locals.get? "_from" = some (.address (AccountAddress.ofNat sender.toNat)))
    (hv : locals.get? "_value" = some (.int (Int.ofNat value.toNat)))
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 8024) (returnPc :: R) mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (aw' : UInt256) (k' C' : Nat),
      ExecFuncBody fork config {contract := contract, locals := locals} evm vaultBurnFunction.body
        (.returned {contract := contract, locals := locals} evm' none) ∧
      SourceState s0 I σ' evm' ∧
      RD fork vaultBytecode I g s0 returnPc R (vaultSupplyMemory mem sender value) aw' rdata σ' k' C') ∨
    (ExecFuncBody fork config {contract := contract, locals := locals} evm vaultBurnFunction.body
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let slot := vyperMappingSlot ⟨13⟩ (.address (AccountAddress.ofNat sender.toNat))
  let old := codeOwnerStorageWord I σ slot
  let mem0 := wordAt0Mem ⟨13⟩ (wordAt32Mem sender mem)
  have hv0 : memLoad (UInt256.ofNat 96) mem0 = value := by
    rw [memLoad_vyperHashMem _ _ _ _ (by omega) hsize (by decide +kernel), hmv]
  have hhash := vyperHashMem_address ⟨13⟩ sender mem (by omega) hcanon
  have hread : evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "balanceOf", steps := [.mindex (.var "_from")]}) =
      .ok (.int (Int.ofNat old.toNat)) := by
    simpa only [hs.storageRead] using vaultBalanceEval evm locals "_from" _ hbase ht
  have hvEval (state : State) := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := state) hv
  have hcondition : UInt256.gt
      (codeOwnerStorageWord I σ
        (keccakWord ⟨0⟩ (UInt256.ofNat 64) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem))) -
        memLoad (UInt256.ofNat 96) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem)))
      (codeOwnerStorageWord I σ
        (keccakWord ⟨0⟩ (UInt256.ofNat 64) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem)))) =
        UInt256.gt (UInt256.sub old value) old := by rw [hmt, hhash, hv0]; rfl
  by_cases hsub : value.toNat ≤ old.toNat
  swap
  · have hover : old.toNat < value.toNat := by omega
    obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_8024_taken_packed
      (by simp only [List.length_cons]; omega)
      (ne_of_eq_of_ne hcondition (by rw [u256_sub_underflow_gt _ _ hover]; decide +kernel)) (by native_decide) h
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_8024_taken_stack, List.length_cons]; omega) rdFail
    exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert
      (ExecStmt.assignExprRevert (evalExpr_checkedSub256_revert hread (hvEval evm) hover))), hrev⟩
  obtain ⟨aw0, k0, C0, rd8054⟩ := vaultBlocks.vault_block_8024_fallthrough_packed
    (by simp only [List.length_cons]; omega)
    (hcondition.trans (ugt_zero (by rw [usub_toNat hsub]; omega))) h
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 8054)
    ((codeOwnerStorageWord I σ
      (keccakWord ⟨0⟩ (UInt256.ofNat 64) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem))) -
      memLoad (UInt256.ofNat 96) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem))) ::
      memLoad (UInt256.ofNat 96) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem)) ::
      codeOwnerStorageWord I σ (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem))) ::
      keccakWord ⟨0⟩ (UInt256.ofNat 64) (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem)) ::
      returnPc :: R)
    (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem)) aw0 rdata σ k0 C0 at rd8054
  rw [hmt, hhash, hv0] at rd8054
  let σ1 := sstoreAccountMap I.codeOwner σ slot (UInt256.sub old value)
  let evm1 := Stele.EVM.storageStore evm I.codeOwner slot (UInt256.sub old value)
  have hs1 : SourceState s0 I σ1 evm1 := hs.storageWrite _ _
  have hdebit : ExecStmt fork config {contract := contract, locals := locals} evm
      vaultBurnFunction.body[0]! (.ok {contract := contract, locals := locals} evm1) := by
    apply ExecStmt.assign (hperm := Or.inr (by simpa only [hs.env] using hperm)) (evalExpr_checkedSub256_ok hread (hvEval evm) rfl hsub)
    simpa only [hs.env] using vaultBalanceAssign evm locals "_from" _ (UInt256.sub old value) hbase ht
  let supply := codeOwnerStorageWord I σ1 (UInt256.ofNat 14)
  have hreadSupply : evalExpr? config {contract := contract, locals := locals} evm1
      (.storage {base := "totalSupply", steps := []}) = .ok (.int (Int.ofNat supply.toNat)) := by
    simpa only [wordToElem, normalizeInt_uint256_word, hs1.storageRead] using vaultEvalScalar evm1 locals "totalSupply"
      (.int (.uint ⟨256, by decide⟩)) (UInt256.ofNat 14) hsupply rfl rfl
  have hcondition1 : UInt256.gt (codeOwnerStorageWord I σ1 (UInt256.ofNat 14) - memLoad (UInt256.ofNat 96) mem0)
      (codeOwnerStorageWord I σ1 (UInt256.ofNat 14)) = UInt256.gt (UInt256.sub supply value) supply := by rw [hv0]; rfl
  by_cases hsubSupply : value.toNat ≤ supply.toNat
  swap
  · have hover : supply.toNat < value.toNat := by omega
    obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_8054_taken_packed
      (by simp only [List.length_cons]; omega) hperm
      (ne_of_eq_of_ne hcondition1 (by rw [u256_sub_underflow_gt _ _ hover]; decide +kernel)) (by native_decide) rd8054
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_8054_taken_stack, List.length_cons]; omega) rdFail
    exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consNormal hdebit (ExecBlock.consRevert
      (ExecStmt.assignExprRevert (evalExpr_checkedSub256_revert hreadSupply (hvEval evm1) hover)))), hrev⟩
  obtain ⟨aw1, k1, C1, rd8077⟩ := vaultBlocks.vault_block_8054_fallthrough_packed
    (by simp only [List.length_cons]; omega) hperm
    (hcondition1.trans (ugt_zero (by rw [usub_toNat hsubSupply]; omega))) rd8054
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 8077)
    ((supply - memLoad (UInt256.ofNat 96) mem0) :: memLoad (UInt256.ofNat 96) mem0 :: supply :: returnPc :: R)
    mem0 aw1 rdata σ1 k1 C1 at rd8077
  rw [hv0] at rd8077
  obtain ⟨aw2, k2, C2, rdReturn⟩ := vaultBlocks.vault_block_8077_packed (by omega) hperm hvalid rd8077
  change RD fork vaultBytecode I g s0 returnPc R ((memLoad (UInt256.ofNat 96) mem0).toByteArray.write 0 mem0 128 32)
    aw2 rdata (sstoreAccountMap I.codeOwner σ1 (UInt256.ofNat 14) (UInt256.sub supply value)) k2 C2 at rdReturn
  rw [hv0] at rdReturn
  let evm2 := Stele.EVM.storageStore evm1 I.codeOwner (UInt256.ofNat 14) (UInt256.sub supply value)
  have hs2 : SourceState s0 I (sstoreAccountMap I.codeOwner σ1 (UInt256.ofNat 14) (UInt256.sub supply value)) evm2 := hs1.storageWrite _ _
  refine Or.inl ⟨evm2, _, aw2, k2, C2, ?_, hs2, rdReturn⟩
  apply ExecFuncBody.execBlockOK
  apply ExecBlock.consNormal hdebit
  have hwrite : ExecStmt fork config {contract := contract, locals := locals} evm1
      vaultBurnFunction.body[1]! (.ok {contract := contract, locals := locals} evm2) := by
    apply ExecStmt.assign (hperm := Or.inr (by simpa only [hs1.env] using hperm)) (evalExpr_checkedSub256_ok hreadSupply (hvEval evm1) rfl hsubSupply)
    simpa only [hs1.env] using vaultAssignScalarUint256 evm1 locals "totalSupply" (UInt256.ofNat 14)
      (UInt256.sub supply value) hsupply rfl rfl (by decide +kernel)
  apply ExecBlock.consNormal hwrite
  refine ExecBlock.consNormal (ExecStmt.emit (fork := fork) (hperm := by simpa only [hs2.env] using hperm) (vals := [.address (AccountAddress.ofNat sender.toNat),
    .address 0, .int (Int.ofNat value.toNat)]) ?_) ExecBlock.nil
  change evalExprs? config {contract := contract, locals := locals} evm2
    [.var "_from", .cast (.intLit 0) (.elem .address), .var "_value"] = _
  simp only [evalExprs?, evalExpr?, ht, hv, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rfl

end Benchmarks.CurveVault
