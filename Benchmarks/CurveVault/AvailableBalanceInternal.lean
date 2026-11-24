import Benchmarks.CurveVault.AvailableBalanceCalls
import Benchmarks.CurveVault.SubOrZero
import Benchmarks.CurveVault.Memory

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultAvailableBalanceFunction : FunctionDecl := contract.functions[32]!

theorem vaultAvailableBalanceBody_eq : vaultAvailableBalanceFunction.body =
    vaultControllerCall "controller_available_balance" "__c0" "available_balance" ++
    vaultControllerCall "controller_admin_fees" "__c1" "admin_fees" ++
    [.internalCall "crv_math_sub_or_zero" [.var "__c0", .var "__c1"] "__c2", .return [.var "__c2"]] := rfl

theorem vaultAvailableBalanceRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {dest returnPc : UInt256} {R : List UInt256}
    (hs : SourceState s0 I σ evm) (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7819) (dest :: returnPc :: R) mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (scratch : ByteArray) (value aw' : UInt256)
        (out : ByteArray) (k' C' : Nat),
      ExecFuncBody fork config {contract := contract, locals := ∅} evm vaultAvailableBalanceFunction.body
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat value.toNat)])) ∧
      SourceState s0 I σ' evm' ∧ WordMemoryRange mem scratch 288 UInt256.size ∧
      RD fork vaultBytecode I g s0 returnPc R
        (value.toByteArray.write 0 scratch dest.toNat 32) aw' out σ' k' C') ∨
    (ExecFuncBody fork config {contract := contract, locals := ∅} evm vaultAvailableBalanceFunction.body .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  rcases vaultAvailableBalanceCall (locals := ∅) hs (by simp)
    (by simp only [List.length_cons]; omega) h with h0 | ⟨hsource, hrev⟩
  swap
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [vaultAvailableBalanceBody_eq, List.append_assoc]
    exact execBlock_reverted_append hsource
  rcases h0 with ⟨evm0, σ0, out0, aw0, k0, C0, _, _, hsource0, hs0, rd0⟩
  let a := retWord out0
  let mem0 := a.toByteArray.write 0 (vaultBlocks.vault_block_7819_memory (mem := mem)) 128 32
  let locals0 := vaultControllerCallLocals ∅ evm "controller_available_balance" "__c0" (.int (Int.ofNat a.toNat))
  have hword0 : memLoad (UInt256.ofNat 128) mem0 = a := memLoad_write_back _ _ 128 (by decide +kernel)
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 128 (by norm_num)))
  rcases vaultAvailableFeesCall (locals := locals0) hs0 (by simp [locals0, vaultControllerCallLocals])
    (by simp only [List.length_cons]; omega) rd0 with h1 | ⟨hsource, hrev⟩
  swap
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [vaultAvailableBalanceBody_eq, List.append_assoc]
    exact execBlock_append hsource0 (execBlock_reverted_append hsource)
  rcases h1 with ⟨evm1, σ1, out1, aw1, k1, C1, _, _, hsource1, hs1, rd1⟩
  let b := retWord out1
  let arg0Mem := a.toByteArray.write 0 mem0 64 32
  let selectorMem := (UInt256.ofNat 454557923).toByteArray.write 0 arg0Mem 192 32
  let mem1 := b.toByteArray.write 0 selectorMem 192 32
  let locals1 := vaultControllerCallLocals locals0 evm0 "controller_admin_fees" "__c1" (.int (Int.ofNat b.toNat))
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 7912)
    (codeOwnerStorageWord I σ0 ⟨3⟩ :: dest :: returnPc :: R)
    (b.toByteArray.write 0 ((UInt256.ofNat 454557923).toByteArray.write 0
      ((memLoad (UInt256.ofNat 128) mem0).toByteArray.write 0 mem0 64 32) 192 32) 192 32)
    aw1 out1 σ1 k1 C1 at rd1
  rw [hword0] at rd1
  have hgap (d : Nat) (hd : d < 1024) (m : ByteArray) : d - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize d (by omega))
  have hsizeArg : 96 ≤ arg0Mem.size := toByteArray_write_size_ge_off_add32 _ _ 64 (hgap _ (by omega) _)
  have hsizeSel : 224 ≤ selectorMem.size := toByteArray_write_size_ge_off_add32 _ _ 192 (hgap _ (by omega) _)
  have hsize1 : 224 ≤ mem1.size := toByteArray_write_size_ge_off_add32 _ _ 192 (hgap _ (by omega) _)
  have hwordA : memLoad (UInt256.ofNat 64) mem1 = a := by
    rw [memLoad_below_write _ _ 192 64 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel),
      memLoad_below_write _ _ 192 64 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel)]
    exact memLoad_write_back _ _ 64 (by decide +kernel) (hgap _ (by omega) _)
  have hwordB : memLoad (UInt256.ofNat 192) mem1 = b := memLoad_write_back _ _ 192 (by decide +kernel) (hgap _ (by omega) _)
  have rd7791 := vaultBlocks.vault_block_7912 (by simp only [List.length_cons]; omega) (by native_decide) rd1
  let argMem := b.toByteArray.write 0 mem1 96 32
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 7791)
    (UInt256.ofNat 256 :: UInt256.ofNat 7930 :: dest :: returnPc :: R)
    ((memLoad (UInt256.ofNat 192) mem1).toByteArray.write 0 mem1 96 32) _ out1 σ1 _ _ at rd7791
  rw [hwordB] at rd7791
  have ha : memLoad (UInt256.ofNat 64) argMem = a := by
    rw [memLoad_below_write _ _ 96 64 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel), hwordA]
  have hb : memLoad (UInt256.ofNat 96) argMem = b := memLoad_write_back _ _ 96 (by decide +kernel) (hgap _ (by omega) _)
  obtain ⟨aw2, k2, C2, rd7930⟩ := vaultSubOrZeroReach ha hb (by simp only [List.length_cons]; omega) (by native_decide) rd7791
  let value := UInt256.sub (wordMax a b) b
  let scratch := value.toByteArray.write 0 argMem 256 32
  have hval : memLoad (UInt256.ofNat 256) scratch = value := memLoad_write_back _ _ 256 (by decide +kernel) (hgap _ (by omega) _)
  have rdRet := vaultBlocks.vault_block_7930 (by omega) hvalid rd7930
  change RD fork vaultBytecode I g s0 returnPc R
    ((memLoad (UInt256.ofNat 256) scratch).toByteArray.write 0 scratch dest.toNat 32) _ out1 σ1 _ _ at rdRet
  rw [hval] at rdRet
  have hevalA : evalExpr? config {contract := contract, locals := locals1} evm1 (.var "__c0") = .ok (.int (Int.ofNat a.toNat)) :=
    evalExpr_varUInt256 (by simp only [locals1, locals0, vaultControllerCallLocals,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
  have hevalB : evalExpr? config {contract := contract, locals := locals1} evm1 (.var "__c1") = .ok (.int (Int.ofNat b.toNat)) :=
    evalExpr_varUInt256 (by simp [locals1, vaultControllerCallLocals])
  let calleeLocals := ((∅ : Store).insert "b" (.int (Int.ofNat b.toNat))).insert "a" (.int (Int.ofNat a.toNat))
  have hcallee := vaultSubOrZeroSource (fork := fork) (evm := evm1) (locals := calleeLocals) (a := a) (b := b)
    (by simp [calleeLocals]) (by simp only [calleeLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
  have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := locals1})
    (callee := vaultSubOrZeroFunction) (name := "crv_math_sub_or_zero")
    (args := [.var "__c0", .var "__c1"]) (argVals := [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat)])
    (retVar := "__c2") (by simp [evalExprs?, hevalA, hevalB, bind, pure, EvalResult.bind]) rfl rfl hcallee
  refine Or.inl ⟨evm1, σ1, locals1.insert "__c2" (.int (Int.ofNat value.toNat)), scratch, value, _, out1, _, _, ?_, hs1, ?_, rdRet⟩
  · apply ExecFuncBody.execBlockRet
    rw [vaultAvailableBalanceBody_eq, List.append_assoc]
    apply execBlock_append hsource0
    apply execBlock_append hsource1
    exact ExecBlock.consNormal hcall (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by
      simp [resumeAfterInternalCall, collapseReturns, evalExpr?, EvalResult.ofOption, value]))))
  · have step (m : ByteArray) (w : UInt256) (d : Nat) (hd : d + 32 ≤ 288) :
        WordMemoryRange m (w.toByteArray.write 0 m d 32) 288 UInt256.size :=
      wordMemoryRange_write m w d 288 UInt256.size (hgap _ (by omega) _) (Or.inr hd)
    exact ((((((step mem (UInt256.ofNat 153294042) 128 (by omega)).trans
      (step _ a 128 (by omega))).trans (step _ a 64 (by omega))).trans
      (step _ (UInt256.ofNat 454557923) 192 (by omega))).trans (step _ b 192 (by omega))).trans
      (step _ b 96 (by omega))).trans (step _ value 256 (by omega))
end Benchmarks.CurveVault
