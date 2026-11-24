import Benchmarks.CurveVault.TotalAssetsCalls
import Reasoning.SteleArithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultTotalAssetsFunction : FunctionDecl := contract.functions[26]!

def vaultTotalAssetsScratch (mem : ByteArray) (available debt fees : UInt256) : ByteArray :=
  fees.toByteArray.write 0 (vaultBlocks.vault_block_6877_memory (mem :=
    debt.toByteArray.write 0 (vaultBlocks.vault_block_6815_memory (mem :=
      available.toByteArray.write 0 (vaultBlocks.vault_block_6772_memory (mem := mem)) 64 32)) 128 32)) 192 32

theorem vaultTotalAssetsBody_eq : vaultTotalAssetsFunction.body =
    vaultControllerCall "controller_available_balance" "__c0" "available_balance" ++
    vaultControllerCall "controller_total_debt" "__c1" "total_debt" ++
    [.letDecl "subtotal" (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (sourceAdd256 (.var "__c0") (.var "__c1"))] ++
    vaultControllerCall "controller_admin_fees" "__c2" "admin_fees" ++
    [.return [sourceCheckedSub256 (.var "subtotal") (.var "__c2")]] := by rfl


theorem vaultTotalAssetsRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {dest returnPc : UInt256} {R : List UInt256}
    (hs : SourceState s0 I σ evm) (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 6772) (dest :: returnPc :: R) mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (available debt fees : UInt256)
        (aw' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecFuncBody fork config {contract := contract, locals := ∅} evm vaultTotalAssetsFunction.body
        (.returned {contract := contract, locals := locals'} evm'
          (some [.int (Int.ofNat (UInt256.sub (available + debt) fees).toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RD fork vaultBytecode I g s0 returnPc R
        ((UInt256.sub (available + debt) fees).toByteArray.write 0
          (vaultTotalAssetsScratch mem available debt fees) dest.toNat 32) aw' out σ' k' C') ∨
    (ExecFuncBody fork config {contract := contract, locals := ∅} evm vaultTotalAssetsFunction.body .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  rcases vaultTotalAssetsAvailableCall (locals := ∅) hs (by simp)
    (by simp only [List.length_cons]; omega) h with h0 | ⟨hsource, hrev⟩
  swap
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [vaultTotalAssetsBody_eq]
    simp only [List.append_assoc]
    exact execBlock_reverted_append hsource
  rcases h0 with ⟨evm0, σ0, out0, aw0, k0, C0, _, _, hsource0, hs0, rd0⟩
  let a := retWord out0
  let mem0 := a.toByteArray.write 0 (vaultBlocks.vault_block_6772_memory (mem := mem)) 64 32
  let locals0 := vaultControllerCallLocals ∅ evm "controller_available_balance" "__c0" (.int (Int.ofNat a.toNat))
  have hword0 : memLoad (UInt256.ofNat 64) mem0 = a :=
    memLoad_write_back _ _ 64 (by decide +kernel)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by norm_num)))
  rcases vaultTotalAssetsDebtCall (locals := locals0) hs0
    (by simp [locals0, vaultControllerCallLocals])
    (by simp only [List.length_cons]; omega) rd0 with h1 | ⟨hsource, hrev⟩
  swap
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [vaultTotalAssetsBody_eq]
    simp only [List.append_assoc]
    exact execBlock_append hsource0 (execBlock_reverted_append hsource)
  rcases h1 with ⟨evm1, σ1, out1, aw1, k1, C1, _, _, hsource1, hs1, rd1⟩
  let b := retWord out1
  let mem1 := b.toByteArray.write 0 (vaultBlocks.vault_block_6815_memory (mem := mem0)) 128 32
  let locals1 := vaultControllerCallLocals locals0 evm0 "controller_total_debt" "__c1" (.int (Int.ofNat b.toNat))
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 6862)
    (codeOwnerStorageWord I σ0 ⟨3⟩ :: memLoad (UInt256.ofNat 64) mem0 :: dest :: returnPc :: R)
    mem1 aw1 out1 σ1 k1 C1 at rd1
  rw [hword0] at rd1
  have hword1 : memLoad (UInt256.ofNat 128) mem1 = b :=
    memLoad_write_back _ _ 128 (by decide +kernel)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 128 (by norm_num)))
  have hevalA : evalExpr? config {contract := contract, locals := locals1} evm1 (.var "__c0") =
      .ok (.int (Int.ofNat a.toNat)) :=
    evalExpr_varUInt256 (by simp only [locals1, locals0, vaultControllerCallLocals,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
  have hevalB : evalExpr? config {contract := contract, locals := locals1} evm1 (.var "__c1") =
      .ok (.int (Int.ofNat b.toNat)) :=
    evalExpr_varUInt256 (by simp [locals1, vaultControllerCallLocals])
  by_cases hadd : a.toNat + b.toNat < UInt256.size
  swap
  · have hover : UInt256.size ≤ a.toNat + b.toNat := by omega
    have rdFail := vaultBlocks.vault_block_6862_taken
      (by simp only [List.length_cons]; omega)
      (by rw [hword1, u256_add_overflow_lt _ _ hover]; decide +kernel)
      (by native_decide) rd1
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_6862_taken_stack, List.length_cons]; omega) rdFail
    refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [vaultTotalAssetsBody_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply execBlock_append hsource0
    apply execBlock_append hsource1
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert (evalExpr_add256_revert hevalA hevalB hover))
  have rd2 := vaultBlocks.vault_block_6862_fallthrough
    (by simp only [List.length_cons]; omega)
    (by rw [hword1]; exact ult_zero (by rw [uadd_toNat, Nat.mod_eq_of_lt hadd]; omega)) rd1
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 6877)
    ((a + memLoad (UInt256.ofNat 128) mem1) :: memLoad (UInt256.ofNat 128) mem1 :: a :: dest :: returnPc :: R)
    mem1 _ out1 σ1 _ _ at rd2
  rw [hword1] at rd2
  let locals2 := locals1.insert "subtotal" (.int (Int.ofNat (a + b).toNat))
  have hlet : ExecStmt fork config {contract := contract, locals := locals1} evm1
      (.letDecl "subtotal" (some (.elem (.int (.uint ⟨256, by decide⟩))))
        (sourceAdd256 (.var "__c0") (.var "__c1")))
      (.ok {contract := contract, locals := locals2} evm1) :=
    ExecStmt.letDecl (evalExpr_add256_ok hevalA hevalB rfl hadd)
  rcases vaultTotalAssetsFeesCall (locals := locals2) hs1
    (by simp [locals2, locals1, locals0, vaultControllerCallLocals])
    (by simp only [List.length_cons]; omega) rd2 with h2 | ⟨hsource, hrev⟩
  swap
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [vaultTotalAssetsBody_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact execBlock_append hsource0 (execBlock_append hsource1
      (ExecBlock.consNormal hlet (execBlock_reverted_append hsource)))
  rcases h2 with ⟨evm2, σ2, out2, aw2, k2, C2, _, _, hsource2, hs2, rd3⟩
  let c := retWord out2
  let mem2 := c.toByteArray.write 0 (vaultBlocks.vault_block_6877_memory (mem := mem1)) 192 32
  let locals3 := vaultControllerCallLocals locals2 evm1 "controller_admin_fees" "__c2" (.int (Int.ofNat c.toNat))
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 6923)
    (codeOwnerStorageWord I σ1 ⟨3⟩ :: (a + b) :: dest :: returnPc :: R)
    mem2 aw2 out2 σ2 k2 C2 at rd3
  have hword2 : memLoad (UInt256.ofNat 192) mem2 = c :=
    memLoad_write_back _ _ 192 (by decide +kernel)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 192 (by norm_num)))
  have hevalSum : evalExpr? config {contract := contract, locals := locals3} evm2 (.var "subtotal") =
      .ok (.int (Int.ofNat (a + b).toNat)) :=
    evalExpr_varUInt256 (by simp only [locals3, locals2, vaultControllerCallLocals,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
  have hevalFees : evalExpr? config {contract := contract, locals := locals3} evm2 (.var "__c2") =
      .ok (.int (Int.ofNat c.toNat)) :=
    evalExpr_varUInt256 (by simp [locals3, vaultControllerCallLocals])
  by_cases hsub : c.toNat ≤ (a + b).toNat
  · have rd4 := vaultBlocks.vault_block_6923_fallthrough
      (by simp only [List.length_cons]; omega)
      (by rw [hword2]; exact ugt_zero (by rw [usub_toNat hsub]; omega)) rd3
    have rdRet := vaultBlocks.vault_block_6938
      (by omega) hvalid rd4
    change RD fork vaultBytecode I g s0 returnPc R
      ((UInt256.sub (a + b) (memLoad (UInt256.ofNat 192) mem2)).toByteArray.write 0 mem2 dest.toNat 32)
      _ out2 σ2 _ _ at rdRet
    rw [hword2] at rdRet
    refine Or.inl ⟨evm2, σ2, locals3, a, b, c, _, out2, _, _, ?_, hs2, rdRet⟩
    apply ExecFuncBody.execBlockRet
    rw [vaultTotalAssetsBody_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply execBlock_append hsource0
    apply execBlock_append hsource1
    apply ExecBlock.consNormal hlet
    apply execBlock_append hsource2
    exact ExecBlock.consReturn (ExecStmt.return
      (evalExprs?_singleton (evalExpr_checkedSub256_ok hevalSum hevalFees rfl hsub)))
  · have hlt : (a + b).toNat < c.toNat := by omega
    have rdFail := vaultBlocks.vault_block_6923_taken
      (by simp only [List.length_cons]; omega)
      (by rw [hword2, ugt_one (by rw [usub_toNat_underflow hlt]; have hc := c.val.isLt; change c.toNat < UInt256.size at hc; omega)]; decide +kernel)
      (by native_decide) rd3
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_6923_taken_stack, List.length_cons]; omega) rdFail
    refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [vaultTotalAssetsBody_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply execBlock_append hsource0
    apply execBlock_append hsource1
    apply ExecBlock.consNormal hlet
    apply execBlock_append hsource2
    apply ExecBlock.consRevert
    apply ExecStmt.returnRevert
    rw [evalExprs?, evalExpr_checkedSub256_revert hevalSum hevalFees hlt]
    rfl
theorem vaultTotalAssetsScratch_frame (mem : ByteArray) (a b c : UInt256) (hmem : 224 ≤ mem.size) :
    (vaultTotalAssetsScratch mem a b c).size = mem.size ∧
    ∀ off, 224 ≤ off → off + 32 ≤ mem.size → off < UInt256.size →
      memLoad (UInt256.ofNat off) (vaultTotalAssetsScratch mem a b c) = memLoad (UInt256.ofNat off) mem := by
  let frame (m : ByteArray) := m.size = mem.size ∧
    ∀ off, 224 ≤ off → off + 32 ≤ mem.size → off < UInt256.size →
      memLoad (UInt256.ofNat off) m = memLoad (UInt256.ofNat off) mem
  have hstep (m : ByteArray) (w : UInt256) (d : Nat) (hd : d + 32 ≤ 224) (hm : frame m) :
      frame (w.toByteArray.write 0 m d 32) := by
    refine ⟨(write32_size_of_end_le _ _ _ (by rw [hm.1]; omega)).trans hm.1, ?_⟩
    intro off hafter hin hoff
    rw [memLoad_above_write _ _ d off (by rw [toByteArray_size])
      (by rw [hm.1]; omega) (by omega) (by rw [hm.1]; exact hin) hoff]
    exact hm.2 off hafter hin hoff
  have h0 : frame mem := ⟨rfl, fun _ _ _ _ => rfl⟩
  have h1 := hstep _ (UInt256.ofNat 153294042) 64 (by omega) h0
  have h2 := hstep _ a 64 (by omega) h1
  have h3 := hstep _ (UInt256.ofNat 836517032) 128 (by omega) h2
  have h4 := hstep _ b 128 (by omega) h3
  have h5 := hstep _ (UInt256.ofNat 454557923) 192 (by omega) h4
  exact hstep _ c 192 (by omega) h5

end Benchmarks.CurveVault
