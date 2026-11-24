import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.Lock
import Benchmarks.CurveVault.TotalAssetsInternal
import Benchmarks.CurveVault.RuntimeBlocks_007

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault


abbrev vaultTotalAssetsPublicFunction : FunctionDecl := contract.functions[4]!

theorem vaultTotalAssetsPublicReturns {evm evm' : EVM.State} {callee : Frame} {value : Value}
    (hbody : ExecFuncBody fork config {contract := contract, locals := ∅} evm vaultTotalAssetsFunction.body
      (.returned callee evm' (some [value]))) :
    ExecFuncBody fork config {contract := contract, locals := ∅} evm vaultTotalAssetsPublicFunction.body
      (.returned {contract := contract, locals := (∅ : Store).insert "__c0" value} evm' (some [value])) := by
  have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := ∅})
    (callee := vaultTotalAssetsFunction) (name := "_total_assets")
    (args := []) (argVals := []) (retVar := "__c0")
    (by simp [evalExprs?, pure]) rfl rfl hbody
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal hcall <|
      ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by
        simp [resumeAfterInternalCall, collapseReturns, evalExpr?, EvalResult.ofOption])))

theorem vaultTotalAssetsPublicReverts {evm : EVM.State}
    (hbody : ExecFuncBody fork config {contract := contract, locals := ∅} evm vaultTotalAssetsFunction.body .reverted) :
    ExecFuncBody fork config {contract := contract, locals := ∅} evm vaultTotalAssetsPublicFunction.body .reverted := by
  exact ExecFuncBody.execBlockRevert <| ExecBlock.consRevert <|
    internalCallFunctionRevert (callee := vaultTotalAssetsFunction) (argVals := [])
      (by simp [evalExprs?, pure]) rfl rfl hbody

theorem vaultTotalAssetsBodyCore {σ σ₀ A I} {g : UInt256}
    (hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 3)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 3) rfl hsel
  have hd : dispatchMsg contract I.calldata = some totalAssetsTransition := by
    apply vaultDispatch_totalAssets
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := totalAssetsTransition) (pc := UInt256.ofNat 1479)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 4 < UInt256.size) (by decide +kernel) (by native_decide)
    (fun h => False.elim (by omega)) (vaultReachTotalAssetsBody hcode hsz hsize hsel)
  intro hvalue _ k C rdBody
  have hdec : config.externalABI.decodeCalldata? (totalAssetsTransition.params.map Param.name)
      (transitionSignature totalAssetsTransition).paramTypes I.calldata = some ∅ := by
    change decodeCalldataWithMode .vyper [] [] I.calldata = some ∅
    exact decodeCalldataWithMode_empty_ok hsz
  have hload : Stele.EVM.transientLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨0⟩ =
      codeOwnerTransientWord I σ ⟨0⟩ := codeOwnerTransientWord_initState _
  by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
  · have rdRevert := vaultBlocks.vault_block_1479_taken (by simp)
      (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _
          rw [hlocked]; decide +kernel) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp) rdRevert
    have hsource (locals : Store) := vaultLockedBodyReverts (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I) locals
      [.internalCall "totalAssets_body" [] "__r", .return [.var "__r"]] hvalue
      (by rw [hload]; exact hlocked)
    exact RDrev.reEquivOfDispatch hcode hd hsource hrev
  · have rd1489 := vaultBlocks.vault_block_1479_fallthrough (by simp)
      (u256_eq_of_ne (Ne.symm hlocked)) rdBody
    have rd6772 := vaultBlocks.vault_block_1489 (by simp) (by native_decide) rd1489
    rcases vaultTotalAssetsRoutine SourceState.init
      (by simp) (by native_decide) rd6772 with hsuccess | ⟨hcallee, hrev⟩
    · rcases hsuccess with ⟨evm', σ', locals', a, b, c, aw', out, k', C', hcallee, hs, rd1501⟩
      have hret := vaultBlocks.vault_block_1501 (by simp) rd1501
      change RDret fork vaultBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ'
        (((UInt256.sub (a + b) c).toByteArray.write 0 _ 256 32).readWithPadding 256 32) at hret
      rw [toByteArray_write_read_back_of_gap _ _ _
        (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 256 (by norm_num)))] at hret
      have hsource := vaultViewBodyReturns (fn := vaultTotalAssetsPublicFunction)
        (locals := ∅) (args := []) (argVals := []) hvalue (by rw [hload]; exact hlocked)
        (by simp [evalExprs?, pure]) rfl rfl (vaultTotalAssetsPublicReturns hcallee)
      exact hret.reEquivExecutionGen hcode hd hdec hsource hs.accounts
        (returnEquiv_of_encode (uint256ReturnEncoding _))
    · have hsource := vaultViewBodyReverts (fn := vaultTotalAssetsPublicFunction)
        (locals := ∅) (args := []) (argVals := []) hvalue (by rw [hload]; exact hlocked)
        (by simp [evalExprs?, pure]) rfl rfl (vaultTotalAssetsPublicReverts hcallee)
      exact hrev.reEquivExecutionRevert hcode hd hdec hsource

theorem vaultTotalAssetsBody {σ σ₀ A I} {g : UInt256}
    (hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 3)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultTotalAssetsBodyCore hwf hcode hsize hsel
end Benchmarks.CurveVault
