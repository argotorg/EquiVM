import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.Calldata
import Benchmarks.CurveVault.Lock
import Benchmarks.CurveVault.ConvertAssetsForward
import Benchmarks.CurveVault.RuntimeBlocks_012

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault

abbrev vaultPreviewMintFunction : FunctionDecl := contract.functions[12]!

theorem vaultPreviewMintBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 33)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 33) rfl hsel
  have hd : dispatchMsg contract I.calldata = some previewMintTransition := by
    apply vaultDispatch_previewMint
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := previewMintTransition) (pc := UInt256.ofNat 3060)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 36 < UInt256.size) (by decide +kernel) (by native_decide)
    decodeCalldataWithMode_vyper_uint256_none_short (vaultReachPreviewMintBody hcode hsz hsize hsel)
  intro hvalue hargs k C rdBody
  let shares := calldataWord I.calldata 4
  let locals : Store := (∅ : Store).insert "_shares" (.int (Int.ofNat shares.toNat))
  have hdec : config.externalABI.decodeCalldata? (previewMintTransition.params.map Param.name)
      (transitionSignature previewMintTransition).paramTypes I.calldata = some locals :=
    decodeCalldataWithMode_vyper_uint256_ok hargs
  have harg : locals.get? "_shares" = some (.int (Int.ofNat shares.toNat)) := by simp [locals]
  have hargEval := evalExprs?_singleton
    (evalExpr_varUInt256 (cfg := config) (contract := contract)
      (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) harg)
  have hload : Stele.EVM.transientLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨0⟩ =
      codeOwnerTransientWord I σ ⟨0⟩ := codeOwnerTransientWord_initState _
  by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
  · have rdRevert := vaultBlocks.vault_block_3060_taken (by simp)
      (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _
          rw [hlocked]; decide +kernel) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp) rdRevert
    have hsource (l : Store) := vaultLockedBodyReverts (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I) l
      [.internalCall "previewMint_body" [.var "_shares"] "__r", .return [.var "__r"]] hvalue
      (by rw [hload]; exact hlocked)
    exact RDrev.reEquivOfDispatch hcode hd hsource hrev
  · have rd3070 := vaultBlocks.vault_block_3060_fallthrough (by simp)
      (u256_eq_of_ne (Ne.symm hlocked)) rdBody
    have rd7332 := vaultBlocks.vault_block_3070 (by simp) (by native_decide) rd3070
    have hm := vaultConversionArgsMemory_reads (vaultDispatchMemory ⟨3017275065⟩) shares ⟨0⟩ vaultMaxWord
    rcases vaultConvertAssetsRoutine (isFloor := false) SourceState.init hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
      (by simp) (by native_decide) rd7332 with hsuccess | ⟨hcallee, hrev⟩
    · rcases hsuccess with ⟨evm', σ', locals', scratch, value, aw', out, k', C', hcallee, hs, _, rd3131⟩
      have hret := vaultBlocks.vault_block_3131 (by simp) rd3131
      change RDret fork vaultBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ'
        ((value.toByteArray.write 0 scratch 576 32).readWithPadding 576 32) at hret
      rw [toByteArray_write_read_back_of_gap _ _ _
        (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 576 (by norm_num)))] at hret
      have hsource := vaultViewBodyReturns (fn := vaultPreviewMintFunction) hvalue
        (by rw [hload]; exact hlocked) hargEval rfl rfl (vaultAssetsForwardReturns harg hcallee)
      exact hret.reEquivExecutionGen hcode hd hdec hsource hs.accounts
        (returnEquiv_of_encode (uint256ReturnEncoding _))
    · have hsource := vaultViewBodyReverts (fn := vaultPreviewMintFunction) hvalue
        (by rw [hload]; exact hlocked) hargEval rfl rfl (vaultAssetsForwardReverts harg hcallee)
      exact hrev.reEquivExecutionRevert hcode hd hdec hsource

theorem vaultPreviewMintBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 33)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultPreviewMintBodyCore hcode hsize hsel

end Benchmarks.CurveVault
