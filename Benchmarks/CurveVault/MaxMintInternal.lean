import Benchmarks.CurveVault.MaxMintCapacity
import Benchmarks.CurveVault.ConvertSharesForward

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultMaxMintFunction : FunctionDecl := contract.functions[11]!

theorem vaultMaxMintRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hloc : locals.get? "maxSupply" = none)
    (hstack : R.length + 15 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 2911) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (value : UInt256),
      ExecFuncBody fork config {contract := contract, locals := locals} evm vaultMaxMintFunction.body
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat value.toNat)])) ∧
      SourceState s0 I σ' evm' ∧ RDret fork vaultBytecode g s0 σ' value.toByteArray) ∨
    (ExecFuncBody fork config {contract := contract, locals := locals} evm vaultMaxMintFunction.body .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  let limit := codeOwnerStorageWord I σ ⟨5⟩
  let locals1 := locals.insert "max_supply" (.int (Int.ofNat limit.toNat))
  let mem1 := limit.toByteArray.write 0 mem 608 32
  have hgap : 608 - mem.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 608 (by norm_num))
  have hsize1 : 640 ≤ mem1.size := toByteArray_write_size_ge_off_add32 _ _ 608 hgap
  have hread : memLoad (UInt256.ofNat 608) mem1 = limit := memLoad_write_back _ _ 608 (by decide +kernel) hgap
  have heval : evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "maxSupply", steps := []}) = .ok (.int (Int.ofNat limit.toNat)) := by
    have hh := vaultEvalScalar evm locals "maxSupply" (.int (.uint ⟨256, by decide⟩)) ⟨5⟩ hloc rfl rfl
    simpa only [wordToElem, normalizeInt_uint256_word, hs.storageRead] using hh
  have hlEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (value := limit) (show locals1.get? "max_supply" = _ by simp [locals1])
  by_cases hmax : limit = vaultMaxWord
  · obtain ⟨_, _, rd2927⟩ := vaultBlocks.vault_block_2911_fallthrough (by omega)
      (by change UInt256.lnot (memLoad (UInt256.ofNat 608) mem1) = _
          rw [hread]; exact (u256_lnot_eq_zero_iff limit).mpr hmax) h
    have rd3058 := vaultBlocks.vault_block_2927 (by omega) (by native_decide) rd2927
    have hret := vaultBlocks.vault_block_3058 (by omega) rd3058
    change RDret fork vaultBytecode g s0 σ ((limit.toByteArray.write 0 mem 608 32).readWithPadding 608 32) at hret
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
    obtain ⟨_, _, rd2936⟩ := vaultBlocks.vault_block_2911_taken (by omega)
      (by change UInt256.lnot (memLoad (UInt256.ofNat 608) mem1) ≠ _
          rw [hread]; exact fun hz => hmax ((u256_lnot_eq_zero_iff limit).mp hz)) (by native_decide) h
    have rd6772 := vaultBlocks.vault_block_2936 (by omega) (by native_decide) rd2936
    rcases vaultTotalAssetsRoutine hs (by omega) (by native_decide) rd6772 with
      ⟨evm', σ', calleeLocals, a, b, c, aw', out, k', C', hcallee, hs', rd2947⟩ | ⟨hcallee, hrev⟩
    · let assets := UInt256.sub (a + b) c
      let scratch := vaultTotalAssetsScratch mem1 a b c
      let returned := assets.toByteArray.write 0 scratch 672 32
      have hframe := vaultTotalAssetsScratch_frame mem1 a b c (by omega)
      have hscratch : scratch.size = mem1.size := hframe.1
      have hlimit : memLoad (UInt256.ofNat 608) returned = limit := by
        rw [memLoad_below_write _ _ 672 608 (by omega) (by omega)
          (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 672 (by norm_num))) (by decide +kernel),
          hframe.2 608 (by omega) (by omega) (by decide +kernel), hread]
      have has : memLoad (UInt256.ofNat 672) returned = assets := memLoad_write_back _ _ 672 (by decide +kernel)
        (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 672 (by norm_num)))
      obtain ⟨aw1, k1, C1, rd2993⟩ := vaultMaxMintCapacity (toByteArray_write_size_ge_off_add32 _ _ 672
        (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 672 (by norm_num)))) hlimit has (by omega) rd2947
      have rd7108 := vaultBlocks.vault_block_2993 (by simp only [List.length_cons]; omega) (by native_decide) rd2993
      let room := UInt256.sub (wordMax limit assets) assets
      have hm := vaultConversionArgsMemory_reads (assets.toByteArray.write 0 returned 640 32) room ⟨1⟩ vaultMaxWord
      let locals2 := locals1.insert "assets" (.int (Int.ofNat assets.toNat))
      have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := locals1})
        (callee := vaultTotalAssetsFunction) (name := "_total_assets") (args := []) (argVals := []) (retVar := "assets")
        (by simp [evalExprs?, pure]) rfl rfl hcallee
      have hsub := evalExpr_checkedMaxSub256 (cfg := config) (stele := {contract := contract, locals := locals2}) (evm := evm')
        (lhs := .var "max_supply") (rhs := .var "assets")
        (evalExpr_varUInt256 (value := limit) (by rw [store_get_ne _ _ (by decide +kernel), store_get_self]))
        (evalExpr_varUInt256 (value := assets) (by simp [locals2]))
      let args : List Expr := [.inRange (.uint ⟨256, by decide⟩)
        (.binary .sub (.ite (.binary .gt (.var "max_supply") (.var "assets")) (.var "max_supply") (.var "assets")) (.var "assets")),
        .boolLit true, .intLit (2 ^ 256 - 1)]
      have hargs : evalExprs? config {contract := contract, locals := locals2} evm' args =
          .ok [.int (Int.ofNat room.toNat), .bool true, .int (Int.ofNat vaultMaxWord.toNat)] := by
        simp only [args, evalExprs?, hsub, evalExpr?, bind, pure, EvalResult.bind]
        rfl
      rcases vaultConvertSharesRoutine (isFloor := true) hs' hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
        (by simp only [List.length_cons]; omega) (by native_decide) rd7108 with
        ⟨evm'', σ'', calleeLocals2, scratch2, value, aw2, out2, k2, C2, hconvert, hs'', _, rd3054⟩ | ⟨hconvert, hrev⟩
      · have rd3058 := vaultBlocks.vault_block_3054 (by simp only [List.length_cons]; omega) rd3054
        have hret := vaultBlocks.vault_block_3058 (by omega) rd3058
        change RDret fork vaultBytecode g s0 σ'' ((value.toByteArray.write 0 scratch2 672 32).readWithPadding 672 32) at hret
        rw [toByteArray_write_read_back_of_gap _ _ _
          (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 672 (by norm_num)))] at hret
        have hcall2 := internalCallFunctionReturn (caller := {contract := contract, locals := locals2})
          (callee := vaultConvertSharesFunction) (name := "_convert_to_shares") (args := args) (retVar := "__c1")
          hargs rfl rfl hconvert
        refine Or.inl ⟨evm'', σ'', locals2.insert "__c1" (.int (Int.ofNat value.toNat)), value, ?_, hs'', hret⟩
        apply ExecFuncBody.execBlockRet
        apply ExecBlock.consNormal (ExecStmt.letDecl heval)
        apply ExecBlock.consReturn (ExecStmt.iteFalse hfalse ?_)
        exact ExecBlock.consNormal hcall (ExecBlock.consNormal hcall2
          (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by
            simp [resumeAfterInternalCall, collapseReturns, evalExpr?, EvalResult.ofOption])))))
      · refine Or.inr ⟨?_, hrev⟩
        apply ExecFuncBody.execBlockRevert
        apply ExecBlock.consNormal (ExecStmt.letDecl heval)
        apply ExecBlock.consRevert (ExecStmt.iteFalse hfalse ?_)
        exact ExecBlock.consNormal hcall (ExecBlock.consRevert
          (internalCallFunctionRevert (callee := vaultConvertSharesFunction) (args := args) hargs rfl rfl hconvert))
    · refine Or.inr ⟨?_, hrev⟩
      apply ExecFuncBody.execBlockRevert
      apply ExecBlock.consNormal (ExecStmt.letDecl heval)
      apply ExecBlock.consRevert (ExecStmt.iteFalse hfalse ?_)
      exact ExecBlock.consRevert (internalCallFunctionRevert (callee := vaultTotalAssetsFunction)
        (argVals := []) (by simp [evalExprs?, pure]) rfl rfl hcallee)
end Benchmarks.CurveVault
