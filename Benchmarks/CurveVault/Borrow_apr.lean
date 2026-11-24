import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.Storage
import Benchmarks.CurveVault.AmmStorage
import Benchmarks.CurveVault.Lock
import Benchmarks.CurveVault.Calls
import Benchmarks.CurveVault.RuntimeBlocks_004
import Benchmarks.CurveVault.RuntimeBlocks_005

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultYearSecondsExpr := sourceMul256 (.intLit 365) (.intLit 86400)

theorem vaultYearSecondsEval (evm : EVM.State) (locals : Store) :
    evalExpr? config {contract := contract, locals := locals} evm vaultYearSecondsExpr =
      .ok (.int (Int.ofNat (UInt256.ofNat 31536000).toNat)) := by
  apply evalExpr_mul256_ok (a := UInt256.ofNat 365) (b := UInt256.ofNat 86400)
    (by simp [evalExpr?, pure]; decide +kernel) (by simp [evalExpr?, pure]; decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem vaultBorrowAprProduct (evm : EVM.State) (locals : Store) (rate : UInt256)
    (hget : locals.get? "__c0" = some (.int (Int.ofNat rate.toNat)))
    (hfit : rate.toNat * (UInt256.ofNat 31536000).toNat < UInt256.size) :
    evalExpr? config {contract := contract, locals := locals} evm
      (sourceMul256 (.var "__c0") vaultYearSecondsExpr) =
      .ok (.int (Int.ofNat (UInt256.mul rate (UInt256.ofNat 31536000)).toNat)) :=
  evalExpr_mul256_ok (evalExpr_varUInt256 hget) (vaultYearSecondsEval evm locals) rfl hfit

theorem vaultBorrowAprProductReverts (evm : EVM.State) (locals : Store) (rate : UInt256)
    (hget : locals.get? "__c0" = some (.int (Int.ofNat rate.toNat)))
    (hover : UInt256.size ≤ rate.toNat * (UInt256.ofNat 31536000).toNat) :
    evalExpr? config {contract := contract, locals := locals} evm
      (sourceMul256 (.var "__c0") vaultYearSecondsExpr) = .revert :=
  evalExpr_mul256_revert (evalExpr_varUInt256 hget) (vaultYearSecondsEval evm locals) hover

abbrev vaultBorrowAprFunction : FunctionDecl := contract.functions[1]!

theorem vaultBorrowAprReceiver (evm : EVM.State) (locals : Store) (hbase : locals.get? "_amm" = none) :
    evalExpr? config {contract := contract, locals := locals} evm (.storage {base := "_amm", steps := []}) =
      .ok (.address (AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩))) :=
  vaultAmmEval evm locals hbase

theorem vaultBorrowAprCallOk {evm evm' : EVM.State} {locals : Store}
    {out : ByteArray} (hbase : locals.get? "_amm" = none)
    (hcall : typedCallViaEVM fork config evm
      (AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩))
      "rate" 0 [] (true, evm', out) false) (h32 : 32 ≤ out.size) :
    ExecStmt fork config {contract := contract, locals := locals} evm
      (.externalCall (.storage {base := "_amm", steps := []}) "rate" (.intLit 0) [] "__c0" (perm := false))
      (.ok {contract := contract, locals := locals.insert "__c0" (.int (Int.ofNat (retWord out).toNat))} evm') := by
  apply ExecStmt.externalCallSuccess (hperm := Or.inl rfl) (sendVal := 0) (argVals := [])
    (value := [.int (Int.ofNat (retWord out).toNat)]) (vaultBorrowAprReceiver evm locals hbase)
    (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
    (by simpa only [address_of_val] using hcall)
  change (ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨256, by decide⟩))) out).map (fun v => [v]) = _
  rw [decodeReturn_vyper_uint256_ok out h32]; rfl

theorem vaultBorrowAprFunctionReturns {evm evm' : EVM.State} {locals : Store}
    {out : ByteArray} (hbase : locals.get? "_amm" = none)
    (hcall : typedCallViaEVM fork config evm
      (AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩))
      "rate" 0 [] (true, evm', out) false) (h32 : 32 ≤ out.size)
    (hfit : (retWord out).toNat * (UInt256.ofNat 31536000).toNat < UInt256.size) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm vaultBorrowAprFunction.body
      (.returned {contract := contract, locals := locals.insert "__c0" (.int (Int.ofNat (retWord out).toNat))} evm'
        (some [.int (Int.ofNat (UInt256.mul (retWord out) (UInt256.ofNat 31536000)).toNat)])) := by
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (vaultBorrowAprCallOk hbase hcall h32) <|
      ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton
        (vaultBorrowAprProduct evm' _ _ (by simp) hfit)))

theorem vaultBorrowAprFunctionOverflow {evm evm' : EVM.State} {locals : Store}
    {out : ByteArray} (hbase : locals.get? "_amm" = none)
    (hcall : typedCallViaEVM fork config evm
      (AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩))
      "rate" 0 [] (true, evm', out) false) (h32 : 32 ≤ out.size)
    (hover : UInt256.size ≤ (retWord out).toNat * (UInt256.ofNat 31536000).toNat) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm vaultBorrowAprFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert <| ExecBlock.consNormal (vaultBorrowAprCallOk hbase hcall h32) <|
    ExecBlock.consRevert <| ExecStmt.returnRevert ?_
  have heval := vaultBorrowAprProductReverts evm'
    (locals.insert "__c0" (.int (Int.ofNat (retWord out).toNat))) (retWord out) (by simp) hover
  simp only [evalExprs?, heval, EvalResult.bind, bind]

theorem vaultBorrowAprFunctionCallFailed {evm evm' : EVM.State} {locals : Store}
    {out : ByteArray} (hbase : locals.get? "_amm" = none)
    (hcall : typedCallViaEVM fork config evm
      (AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩))
      "rate" 0 [] (false, evm', out) false) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm vaultBorrowAprFunction.body .reverted :=
  ExecFuncBody.execBlockRevert <| ExecBlock.consRevert <|
    ExecStmt.externalCallFailure (hperm := Or.inl rfl) (sendVal := 0) (argVals := []) (vaultBorrowAprReceiver evm locals hbase)
      (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
      (by simpa only [address_of_val] using hcall)

theorem vaultBorrowAprFunctionDecodeFailed {evm evm' : EVM.State} {locals : Store}
    {out : ByteArray} (hbase : locals.get? "_amm" = none)
    (hcall : typedCallViaEVM fork config evm
      (AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩))
      "rate" 0 [] (true, evm', out) false)
    (hdec : config.externalABI.decode? "rate" out = none) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm vaultBorrowAprFunction.body .reverted :=
  ExecFuncBody.execBlockRevert <| ExecBlock.consRevert <|
    ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) (sendVal := 0) (argVals := []) (vaultBorrowAprReceiver evm locals hbase)
      (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
      (by simpa only [address_of_val] using hcall) hdec

theorem vaultBorrowAprCalldata (mem : ByteArray) :
    config.externalABI.encode? "rate" [] = some
      (((UInt256.ofNat 743338542).toByteArray.write 0 mem 64 32).readWithPadding 92 4) := by
  change ABI.encodeCallWithSelector? (selectorBytes 0x2c 0x4e 0x72 0x2e) [] [] = _
  exact vyperNullaryCallData _ _ mem 64 (by decide +kernel)
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by norm_num)))

theorem vaultBorrowAprBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 34)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 34) rfl hsel
  have hd : dispatchMsg contract I.calldata = some borrow_aprTransition := by
    apply vaultDispatch_borrow_apr
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := borrow_aprTransition) (pc := UInt256.ofNat 1020)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 4 < UInt256.size) (by decide +kernel) (by native_decide)
    (fun h => False.elim (by omega)) (vaultReachBorrow_aprBody hcode hsz hsize hsel)
  intro hvalue _ k C rdBody
  have hdec : config.externalABI.decodeCalldata? (borrow_aprTransition.params.map Param.name)
      (transitionSignature borrow_aprTransition).paramTypes I.calldata = some ∅ := by
    change decodeCalldataWithMode .vyper [] [] I.calldata = some ∅
    exact decodeCalldataWithMode_empty_ok hsz
  have hload : Stele.EVM.transientLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨0⟩ =
      codeOwnerTransientWord I σ ⟨0⟩ := codeOwnerTransientWord_initState _
  by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
  · have rdRevert := vaultBlocks.vault_block_1020_taken (by simp)
      (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _
          rw [hlocked]; decide +kernel) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp) rdRevert
    have hsource := vaultLockedBodyReverts (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      [.internalCall "borrow_apr_body" [] "__r", .return [.var "__r"]] hvalue
      (by rw [hload]; exact hlocked)
    exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  · have hlock : Stele.EVM.transientLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨0⟩ ≠ ⟨1⟩ :=
      by rwa [hload]
    have hwrap (hb : ExecFuncBody fork config {contract := contract, locals := ∅}
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) vaultBorrowAprFunction.body .reverted) :
        ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
          borrow_aprTransition.body .reverted :=
      vaultViewBodyReverts (fn := vaultBorrowAprFunction) (args := []) (argVals := []) hvalue hlock
        (by simp [evalExprs?, pure]) rfl rfl hb
    have rd1030 := vaultBlocks.vault_block_1020_fallthrough (by simp)
      (u256_eq_of_ne (Ne.symm hlocked)) rdBody
    obtain ⟨gasWord, k1, C1, rd1051⟩ := vaultBlocks.vault_block_1030 (by simp) rd1030
    obtain ⟨evm', σ', z, out, k2, C2, hcall, hs, rd1052, hout⟩ :=
      typedStaticCallBridge (cfg := config) (name := "rate") (args := []) rd1051
        SourceState.init (by native_decide) (vaultBorrowAprCalldata _) (by decide +kernel) (by simp)
    have hsload : Stele.EVM.storageLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨2⟩ =
        codeOwnerStorageWord I σ ⟨2⟩ := codeOwnerStorageWord_initState _
    change typedCallViaEVM fork config _ (AccountAddress.ofUInt256 (codeOwnerStorageWord I σ ⟨2⟩))
      "rate" 0 [] (z, evm', out) false at hcall
    rw [← hsload] at hcall
    have hout256 : out.size < UInt256.size := lt_trans hout (by decide +kernel)
    cases z with
    | false =>
      have rd1056 := vaultBlocks.vault_block_1052_fallthrough (by simp) rfl rd1052
      have hrev := vaultBlocks.vault_block_1056 (by simp [vaultBlocks.vault_block_1052_fallthrough_stack]) rd1056
      exact hrev.reEquivExecutionRevert hcode hd hdec
        (hwrap (vaultBorrowAprFunctionCallFailed (by simp) hcall))
    | true =>
      have rd1063 := vaultBlocks.vault_block_1052_taken (by simp) (by decide +kernel) (by native_decide) rd1052
      by_cases h32 : 32 ≤ out.size
      · have rd1072 := vaultBlocks.vault_block_1063_fallthrough
          (by simp [vaultBlocks.vault_block_1052_taken_stack])
          (ult_zero (by rw [ulit_toNat' _ hout256]; exact h32)) rd1063
        let preMem := (UInt256.ofNat 743338542).toByteArray.write 0 (vaultDispatchMemory ⟨3133463202⟩) 64 32
        have hpre : 96 ≤ preMem.size := toByteArray_write_size_ge_off_add32 _ _ 64
          (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by norm_num)))
        have hword : memLoad (UInt256.ofNat 64)
            (out.write 0 preMem 64 (min (UInt256.ofNat 32) (UInt256.ofNat out.size)).toNat) = retWord out :=
          memLoad_callOutput32 out preMem 64 h32 hout256 hpre (by decide +kernel)
            (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by norm_num)))
        by_cases hfit : (retWord out).toNat * (UInt256.ofNat 31536000).toNat < UInt256.size
        · have rd1097 := vaultBlocks.vault_block_1072_fallthrough (by simp)
            (by change UInt256.xor (UInt256.div (UInt256.mul (memLoad _ (out.write 0 preMem 64 _)) _) _)
                  (memLoad _ (out.write 0 preMem 64 _)) = _
                rw [hword, u256_mul_div_right_eq_of_noOverflow _ _ (by decide +kernel) hfit, u256_xor_self]; rfl) rd1072
          have hret := vaultBlocks.vault_block_1097 (by simp) rd1097
          change RDret fork vaultBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ'
            (((UInt256.mul (memLoad (UInt256.ofNat 64) (out.write 0 preMem 64 _)) (UInt256.ofNat 31536000)).toByteArray.write
              0 _ 128 32).readWithPadding 128 32) at hret
          rw [hword, toByteArray_write_read_back_of_gap _ _ _
            (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 128 (by norm_num)))] at hret
          have hcallee := vaultBorrowAprFunctionReturns (locals := ∅) (by simp) hcall h32 hfit
          have hsource := vaultViewBodyReturns (fn := vaultBorrowAprFunction) (locals := ∅) (args := []) (argVals := [])
            hvalue hlock (by simp [evalExprs?, pure]) rfl rfl hcallee
          exact hret.reEquivExecutionGen hcode hd hdec hsource hs.accounts
            (returnEquiv_of_encode (uint256ReturnEncoding _))
        · have hover : UInt256.size ≤ (retWord out).toNat * (UInt256.ofNat 31536000).toNat := by omega
          have rdRevert := vaultBlocks.vault_block_1072_taken (by simp)
            (by change UInt256.xor (UInt256.div (UInt256.mul (memLoad _ (out.write 0 preMem 64 _)) _) _)
                  (memLoad _ (out.write 0 preMem 64 _)) ≠ _
                rw [hword]; exact u256_xor_ne_zero_of_ne (u256_mul_div_right_overflow_ne _ _ hover))
            (by native_decide) rd1072
          have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_1072_taken_stack]) rdRevert
          exact hrev.reEquivExecutionRevert hcode hd hdec
            (hwrap (vaultBorrowAprFunctionOverflow (by simp) hcall h32 hover))
      · have hshort : out.size < 32 := by omega
        have rdRevert := vaultBlocks.vault_block_1063_taken
          (by simp [vaultBlocks.vault_block_1052_taken_stack])
          (by rw [ult_one (by rw [ulit_toNat' _ hout256]; exact hshort)]; decide +kernel)
          (by native_decide) rd1063
        have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_1052_taken_stack]) rdRevert
        have hdecode : config.externalABI.decode? "rate" out = none := by
          change (ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨256, by decide⟩))) out).map (fun v => [v]) = _
          rw [decodeReturn_vyper_uint256_short out hshort]; rfl
        exact hrev.reEquivExecutionRevert hcode hd hdec
          (hwrap (vaultBorrowAprFunctionDecodeFailed (by simp) hcall hdecode))

theorem vaultBorrow_aprBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 34)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultBorrowAprBodyCore hcode hsize hsel

end Benchmarks.CurveVault
