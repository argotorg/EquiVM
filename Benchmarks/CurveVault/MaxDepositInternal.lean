import Benchmarks.CurveVault.Limits
import Benchmarks.CurveVault.ConversionPrefix
import Benchmarks.CurveVault.RuntimeBlocks_009
import Benchmarks.CurveVault.RuntimeBlocks_010

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultMaxDepositFunction : FunctionDecl := contract.functions[8]!

theorem vaultMaxDepositFinish {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {limit assets : UInt256} {R : List UInt256}
    (hsize : 384 ≤ mem.size)
    (hl : memLoad (UInt256.ofNat 288) mem = limit)
    (ha : memLoad (UInt256.ofNat 352) mem = assets)
    (hstack : R.length + 6 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 1997) R mem aw rdata σ k C) :
    RDret fork vaultBytecode g s0 σ (UInt256.sub (wordMax limit assets) assets).toByteArray := by
  let written := assets.toByteArray.write 0 mem 320 32
  have hgap : 320 - mem.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 320 (by norm_num))
  have hl' : memLoad (UInt256.ofNat 288) written = limit := by
    rw [memLoad_below_write _ _ 320 288 (by omega) (by omega) hgap (by decide +kernel), hl]
  have ha' : memLoad (UInt256.ofNat 320) written = assets := memLoad_write_back _ _ 320 (by decide +kernel) hgap
  have rd2041 := vaultBlocks.vault_block_1997_fallthrough hstack (by
    rw [ha]
    change UInt256.gt (UInt256.sub (UInt256.xor
      (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 288) written) (memLoad (UInt256.ofNat 320) written))
        (UInt256.xor (memLoad (UInt256.ofNat 320) written) (memLoad (UInt256.ofNat 288) written)))
      (memLoad (UInt256.ofNat 320) written)) (memLoad (UInt256.ofNat 320) written))
      (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 288) written) (memLoad (UInt256.ofNat 320) written))
        (UInt256.xor (memLoad (UInt256.ofNat 320) written) (memLoad (UInt256.ofNat 288) written)))
        (memLoad (UInt256.ofNat 320) written)) = _
    rw [hl', ha', branchlessMax]
    exact sub_wordMax_noUnderflow limit assets) h
  have rd2054 := vaultBlocks.vault_block_2041 (by omega) rd2041
  have hret := vaultBlocks.vault_block_2054 (by omega) rd2054
  change RDret fork vaultBytecode g s0 σ
    (((UInt256.sub (UInt256.xor (UInt256.mul (UInt256.gt
      (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem 320 32))
      (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem 320 32)))
      (UInt256.xor (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem 320 32))
        (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem 320 32))))
      (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem 320 32)))
      (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem 320 32))).toByteArray.write 0
        ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem 320 32) 352 32).readWithPadding 352 32) at hret
  rw [toByteArray_write_read_back_of_gap _ _ _
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 352 (by norm_num))), ha] at hret
  change RDret fork vaultBytecode g s0 σ
    (UInt256.sub (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 288) written)
      (memLoad (UInt256.ofNat 320) written)) (UInt256.xor (memLoad (UInt256.ofNat 320) written)
        (memLoad (UInt256.ofNat 288) written))) (memLoad (UInt256.ofNat 320) written))
      (memLoad (UInt256.ofNat 320) written)).toByteArray at hret
  rw [hl', ha', branchlessMax] at hret
  exact hret

theorem vaultMaxDepositRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hloc : locals.get? "maxSupply" = none)
    (hstack : R.length + 10 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 1961) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (value : UInt256),
      ExecFuncBody fork config {contract := contract, locals := locals} evm vaultMaxDepositFunction.body
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat value.toNat)])) ∧
      SourceState s0 I σ' evm' ∧ RDret fork vaultBytecode g s0 σ' value.toByteArray) ∨
    (ExecFuncBody fork config {contract := contract, locals := locals} evm vaultMaxDepositFunction.body .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  let limit := codeOwnerStorageWord I σ ⟨5⟩
  let locals1 := locals.insert "max_supply" (.int (Int.ofNat limit.toNat))
  let mem1 := limit.toByteArray.write 0 mem 288 32
  have hgap : 288 - mem.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by norm_num))
  have hsize1 : 320 ≤ mem1.size := toByteArray_write_size_ge_off_add32 _ _ 288 hgap
  have hread : memLoad (UInt256.ofNat 288) mem1 = limit := memLoad_write_back _ _ 288 (by decide +kernel) hgap
  have heval : evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "maxSupply", steps := []}) = .ok (.int (Int.ofNat limit.toNat)) := by
    have hh := vaultEvalScalar evm locals "maxSupply" (.int (.uint ⟨256, by decide⟩)) ⟨5⟩ hloc rfl rfl
    simpa only [wordToElem, normalizeInt_uint256_word, hs.storageRead] using hh
  have hlEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (value := limit) (show locals1.get? "max_supply" = _ by simp [locals1])
  by_cases hmax : limit = vaultMaxWord
  · obtain ⟨_, _, rd1977⟩ := vaultBlocks.vault_block_1961_fallthrough (by omega)
      (by change UInt256.lnot (memLoad (UInt256.ofNat 288) mem1) = _
          rw [hread]; exact (u256_lnot_eq_zero_iff limit).mpr hmax) h
    have rd2054 := vaultBlocks.vault_block_1977 (by omega) (by native_decide) rd1977
    have hret := vaultBlocks.vault_block_2054 (by omega) rd2054
    change RDret fork vaultBytecode g s0 σ ((limit.toByteArray.write 0 mem 288 32).readWithPadding 288 32) at hret
    rw [toByteArray_write_read_back_of_gap _ _ _ hgap] at hret
    refine Or.inl ⟨evm, σ, locals1, limit, ?_, hs, hret⟩
    apply ExecFuncBody.execBlockRet
    apply ExecBlock.consNormal (ExecStmt.letDecl heval)
    apply ExecBlock.consReturn (ExecStmt.iteTrue ?_ ?_)
    · apply evalExpr_eq_int_true (b := 2 ^ 256 - 1) hlEval (by simp [evalExpr?, pure])
      rw [hmax]; decide +kernel
    · exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hlEval))
  · have hfalse : evalExpr? config {contract := contract, locals := locals1} evm
        (.binary .eq (.var "max_supply") (.intLit (2 ^ 256 - 1))) = .ok (.bool false) := by
      apply evalExpr_eq_int_false (b := 2 ^ 256 - 1) hlEval (by simp [evalExpr?, pure])
      intro hn
      apply hmax
      apply u256_inj
      change limit.toNat = (UInt256.ofNat (UInt256.size - 1)).toNat
      rw [ulit_toNat' _ (by decide +kernel)]
      change (limit.toNat : Int) = Int.ofNat (UInt256.size - 1) at hn
      exact Int.ofNat.inj hn
    obtain ⟨_, _, rd1986⟩ := vaultBlocks.vault_block_1961_taken (by omega)
      (by change UInt256.lnot (memLoad (UInt256.ofNat 288) mem1) ≠ _
          rw [hread]; exact fun hz => hmax ((u256_lnot_eq_zero_iff limit).mp hz)) (by native_decide) h
    have rd6772 := vaultBlocks.vault_block_1986 (by omega) (by native_decide) rd1986
    rcases vaultTotalAssetsRoutine hs hstack (by native_decide) rd6772 with
      ⟨evm', σ', calleeLocals, a, b, c, aw', out, k', C', hcallee, hs', rd1997⟩ | ⟨hcallee, hrev⟩
    · let assets := UInt256.sub (a + b) c
      let scratch := vaultTotalAssetsScratch mem1 a b c
      let returned := assets.toByteArray.write 0 scratch 352 32
      have hframe := vaultTotalAssetsScratch_frame mem1 a b c (by omega)
      have hscratch : scratch.size = mem1.size := hframe.1
      have hlimit : memLoad (UInt256.ofNat 288) returned = limit := by
        rw [memLoad_below_write _ _ 352 288 (by omega) (by omega)
          (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 352 (by norm_num))) (by decide +kernel),
          hframe.2 288 (by omega) (by omega) (by decide +kernel), hread]
      have has : memLoad (UInt256.ofNat 352) returned = assets := memLoad_write_back _ _ 352 (by decide +kernel)
        (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 352 (by norm_num)))
      have hret := vaultMaxDepositFinish (toByteArray_write_size_ge_off_add32 _ _ 352
        (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 352 (by norm_num)))) hlimit has (by omega) rd1997
      let locals2 := locals1.insert "assets" (.int (Int.ofNat assets.toNat))
      have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := locals1})
        (callee := vaultTotalAssetsFunction) (name := "_total_assets") (args := []) (argVals := []) (retVar := "assets")
        (by simp [evalExprs?, pure]) rfl rfl hcallee
      have hsub := evalExpr_checkedMaxSub256 (cfg := config) (stele := {contract := contract, locals := locals2}) (evm := evm')
        (lhs := .var "max_supply") (rhs := .var "assets")
        (evalExpr_varUInt256 (value := limit) (by rw [store_get_ne _ _ (by decide +kernel), store_get_self]))
        (evalExpr_varUInt256 (value := assets) (by simp [locals2]))
      refine Or.inl ⟨evm', σ', locals2, UInt256.sub (wordMax limit assets) assets, ?_, hs', hret⟩
      apply ExecFuncBody.execBlockRet
      apply ExecBlock.consNormal (ExecStmt.letDecl heval)
      apply ExecBlock.consReturn (ExecStmt.iteFalse hfalse ?_)
      exact ExecBlock.consNormal hcall (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hsub)))
    · refine Or.inr ⟨?_, hrev⟩
      apply ExecFuncBody.execBlockRevert
      apply ExecBlock.consNormal (ExecStmt.letDecl heval)
      apply ExecBlock.consRevert (ExecStmt.iteFalse hfalse ?_)
      exact ExecBlock.consRevert (internalCallFunctionRevert (callee := vaultTotalAssetsFunction)
        (argVals := []) (by simp [evalExprs?, pure]) rfl rfl hcallee)
end Benchmarks.CurveVault
