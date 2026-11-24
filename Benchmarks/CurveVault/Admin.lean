import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.FactoryStorage
import Benchmarks.CurveVault.Lock
import Benchmarks.CurveVault.Calls
import Benchmarks.CurveVault.RuntimeBlocks_022
import Benchmarks.CurveVault.RuntimeBlocks_023

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultAdminFunction : FunctionDecl := contract.functions[25]!

theorem vaultAdminFunctionReturns {evm evm' : EVM.State} {locals : Store}
    {out : ByteArray} {value : Value} (hbase : locals.get? "_factory" = none)
    (hcall : typedCallViaEVM fork config evm
      (AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩))
      "admin" 0 [] (true, evm', out) false)
    (hdec : config.externalABI.decode? "admin" out = some [value]) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm vaultAdminFunction.body
      (.returned {contract := contract, locals := locals.insert "__c0" value} evm' (some [value])) := by
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.externalCallSuccess (fork := fork) (hperm := Or.inl rfl) (sendVal := 0) (argVals := []) (vaultFactoryEval evm locals hbase)
      (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
      (by simpa only [address_of_val] using hcall) hdec) <|
      ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by
        simp [collapseReturns, evalExpr?, EvalResult.ofOption])))

theorem vaultAdminFunctionCallFailed {evm evm' : EVM.State} {locals : Store}
    {out : ByteArray} (hbase : locals.get? "_factory" = none)
    (hcall : typedCallViaEVM fork config evm
      (AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩))
      "admin" 0 [] (false, evm', out) false) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm vaultAdminFunction.body .reverted :=
  ExecFuncBody.execBlockRevert <| ExecBlock.consRevert <|
    ExecStmt.externalCallFailure (hperm := Or.inl rfl) (sendVal := 0) (argVals := []) (vaultFactoryEval evm locals hbase)
      (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
      (by simpa only [address_of_val] using hcall)

theorem vaultAdminFunctionDecodeFailed {evm evm' : EVM.State} {locals : Store}
    {out : ByteArray} (hbase : locals.get? "_factory" = none)
    (hcall : typedCallViaEVM fork config evm
      (AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩))
      "admin" 0 [] (true, evm', out) false)
    (hdec : config.externalABI.decode? "admin" out = none) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm vaultAdminFunction.body .reverted :=
  ExecFuncBody.execBlockRevert <| ExecBlock.consRevert <|
    ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) (sendVal := 0) (argVals := []) (vaultFactoryEval evm locals hbase)
      (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
      (by simpa only [address_of_val] using hcall) hdec

theorem vaultAdminBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 44)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 44) rfl hsel
  have hd : dispatchMsg contract I.calldata = some adminTransition := by
    apply vaultDispatch_admin
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := adminTransition) (pc := UInt256.ofNat 6326)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 4 < UInt256.size) (by decide +kernel) (by native_decide)
    (fun h => False.elim (by omega)) (vaultReachAdminBody hcode hsz hsize hsel)
  intro hvalue _ k C rdBody
  have hdec : config.externalABI.decodeCalldata? (adminTransition.params.map Param.name)
      (transitionSignature adminTransition).paramTypes I.calldata = some ∅ := by
    change decodeCalldataWithMode .vyper [] [] I.calldata = some ∅
    exact decodeCalldataWithMode_empty_ok hsz
  have hload : Stele.EVM.transientLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨0⟩ =
      codeOwnerTransientWord I σ ⟨0⟩ := codeOwnerTransientWord_initState _
  by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
  · have rdRevert := vaultBlocks.vault_block_6326_taken (by simp)
      (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _
          rw [hlocked]; decide +kernel) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp) rdRevert
    have hsource := vaultLockedBodyReverts (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      [.internalCall "admin_body" [] "__r", .return [.var "__r"]] hvalue
      (by rw [hload]; exact hlocked)
    exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  · have hlock : Stele.EVM.transientLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨0⟩ ≠ ⟨1⟩ :=
      by rwa [hload]
    have hwrap (hb : ExecFuncBody fork config {contract := contract, locals := ∅}
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) vaultAdminFunction.body .reverted) :
        ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
          adminTransition.body .reverted :=
      vaultViewBodyReverts (fn := vaultAdminFunction) (args := []) (argVals := []) hvalue hlock
        (by simp [evalExprs?, pure]) rfl rfl hb
    have rd6336 := vaultBlocks.vault_block_6326_fallthrough (by simp)
      (u256_eq_of_ne (Ne.symm hlocked)) rdBody
    obtain ⟨gasWord, k1, C1, rd6359⟩ := vaultBlocks.vault_block_6336 (by simp) rd6336
    obtain ⟨evm', σ', z, out, k2, C2, hcall, hs, rd6360, hout⟩ :=
      typedStaticCallBridge (cfg := config) (name := "admin") (args := []) rd6359
        SourceState.init (by native_decide) (vaultAdminCalldata _) (by decide +kernel) (by simp)
    have hsload : Stele.EVM.storageLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨4⟩ =
        codeOwnerStorageWord I σ ⟨4⟩ := codeOwnerStorageWord_initState _
    change typedCallViaEVM fork config _ (AccountAddress.ofUInt256 (codeOwnerStorageWord I σ ⟨4⟩))
      "admin" 0 [] (z, evm', out) false at hcall
    rw [← hsload] at hcall
    have hout256 : out.size < UInt256.size := lt_trans hout (by decide +kernel)
    cases z with
    | false =>
      have rd6364 := vaultBlocks.vault_block_6360_fallthrough (by simp) rfl rd6360
      have hrev := vaultBlocks.vault_block_6364 (by simp [vaultBlocks.vault_block_6360_fallthrough_stack]) rd6364
      exact hrev.reEquivExecutionRevert hcode hd hdec
        (hwrap (vaultAdminFunctionCallFailed (by simp) hcall))
    | true =>
      have rd6371 := vaultBlocks.vault_block_6360_taken (by simp) (by decide +kernel) (by native_decide) rd6360
      by_cases h32 : 32 ≤ out.size
      · have rd6394 := vaultBlocks.vault_block_6371_fallthrough (by simp [vaultBlocks.vault_block_6360_taken_stack])
          (rdsCheck_ok 64 96 out.size rfl (by decide +kernel) h32 hout256) rd6371
        let preMem := (UInt256.ofNat 4166100032).toByteArray.write 0 (vaultDispatchMemory ⟨4166100032⟩) 64 32
        have hpre : 96 ≤ preMem.size := toByteArray_write_size_ge_off_add32 _ _ 64
          (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by norm_num)))
        have hword : memLoad (UInt256.ofNat 64)
            (out.write 0 preMem 64 (min (UInt256.ofNat 32) (UInt256.ofNat out.size)).toNat) = retWord out := by
          exact memLoad_callOutput32 out preMem 64 h32 hout256 hpre (by decide +kernel)
            (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by norm_num)))
        by_cases hcanon : (retWord out).toNat < EVM.addressModulus
        · have rd6405 := vaultBlocks.vault_block_6394_fallthrough (by simp [vaultBlocks.vault_block_6371_fallthrough_stack, vaultBlocks.vault_block_6360_taken_stack])
            (by change UInt256.shiftRight (memLoad _ (out.write 0 preMem 64 _)) _ = _
                rw [hword]; exact u256_shiftRight160_zero_of_lt _ hcanon) rd6394
          have hret := vaultBlocks.vault_block_6405 (by simp) rd6405
          change RDret fork vaultBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ'
            (((memLoad (UInt256.ofNat 64) (out.write 0 preMem 64 _)).toByteArray.write 0 _ 128 32).readWithPadding 128 32) at hret
          rw [hword, toByteArray_write_read_back_of_gap _ _ _
            (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 128 (by norm_num)))] at hret
          have hdecode : config.externalABI.decode? "admin" out =
              some [.address (AccountAddress.ofNat (retWord out).toNat)] := by
            change (ABI.decodeReturnValueWithMode? .vyper (.elem .address) out).map (fun v => [v]) = _
            rw [decodeReturn_vyper_address_ok out h32 hcanon]; rfl
          have hcallee := vaultAdminFunctionReturns (locals := ∅) (by simp) hcall hdecode
          have hsource := vaultViewBodyReturns (fn := vaultAdminFunction) (locals := ∅) (args := []) (argVals := [])
            hvalue hlock (by simp [evalExprs?, pure]) rfl rfl hcallee
          exact hret.reEquivExecutionGen hcode hd hdec hsource hs.accounts
            (returnEquiv_of_encode (vaultAddressReturnEncoding (retWord out) hcanon))
        · have rdRevert := vaultBlocks.vault_block_6394_taken (by simp [vaultBlocks.vault_block_6371_fallthrough_stack, vaultBlocks.vault_block_6360_taken_stack])
            (by change UInt256.shiftRight (memLoad _ (out.write 0 preMem 64 _)) _ ≠ _
                rw [hword]; exact fun h => hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ h))
            (by native_decide) rd6394
          have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_6394_taken_stack, vaultBlocks.vault_block_6371_fallthrough_stack, vaultBlocks.vault_block_6360_taken_stack]) rdRevert
          have hdecode : config.externalABI.decode? "admin" out = none := by
            change (ABI.decodeReturnValueWithMode? .vyper (.elem .address) out).map (fun v => [v]) = _
            rw [decodeReturn_vyper_address_noncanon out h32 hcanon]; rfl
          exact hrev.reEquivExecutionRevert hcode hd hdec
            (hwrap (vaultAdminFunctionDecodeFailed (by simp) hcall hdecode))
      · have hshort : out.size < 32 := by omega
        have rdRevert := vaultBlocks.vault_block_6371_taken (by simp [vaultBlocks.vault_block_6360_taken_stack])
          (rdsCheck_short 64 96 out.size rfl (by decide +kernel) hshort) (by native_decide) rd6371
        have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_6371_taken_stack, vaultBlocks.vault_block_6360_taken_stack]) rdRevert
        have hdecode : config.externalABI.decode? "admin" out = none := by
          change (ABI.decodeReturnValueWithMode? .vyper (.elem .address) out).map (fun v => [v]) = _
          rw [decodeReturn_vyper_address_short out hshort]; rfl
        exact hrev.reEquivExecutionRevert hcode hd hdec
          (hwrap (vaultAdminFunctionDecodeFailed (by simp) hcall hdecode))

theorem vaultAdminBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 44)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultAdminBodyCore hcode hsize hsel

end Benchmarks.CurveVault
