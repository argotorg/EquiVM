import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.Calldata
import Benchmarks.CurveVault.Lock
import Benchmarks.CurveVault.ConvertSharesForward
import Benchmarks.CurveVault.RuntimeBlocks_015

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault

abbrev vaultPreviewWithdrawFunction : FunctionDecl := contract.functions[15]!

theorem vaultPreviewWithdrawBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 7)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 7) rfl hsel
  have hd : dispatchMsg contract I.calldata = some previewWithdrawTransition := by
    apply vaultDispatch_previewWithdraw
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := previewWithdrawTransition) (pc := UInt256.ofNat 4031)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 36 < UInt256.size) (by decide +kernel) (by native_decide)
    decodeCalldataWithMode_vyper_uint256_none_short (vaultReachPreviewWithdrawBody hcode hsz hsize hsel)
  intro hvalue hargs k C rdBody
  let assets := calldataWord I.calldata 4
  let locals : Store := (∅ : Store).insert "_assets" (.int (Int.ofNat assets.toNat))
  have hdec : config.externalABI.decodeCalldata? (previewWithdrawTransition.params.map Param.name)
      (transitionSignature previewWithdrawTransition).paramTypes I.calldata = some locals :=
    decodeCalldataWithMode_vyper_uint256_ok hargs
  have harg : locals.get? "_assets" = some (.int (Int.ofNat assets.toNat)) := by simp [locals]
  have hargEval := evalExprs?_singleton
    (evalExpr_varUInt256 (cfg := config) (contract := contract)
      (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) harg)
  have hload : Stele.EVM.transientLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨0⟩ =
      codeOwnerTransientWord I σ ⟨0⟩ := codeOwnerTransientWord_initState _
  by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
  · have rdRevert := vaultBlocks.vault_block_4031_taken (by simp)
      (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _
          rw [hlocked]; decide +kernel) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp) rdRevert
    have hsource (l : Store) := vaultLockedBodyReverts (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I) l
      [.internalCall "previewWithdraw_body" [.var "_assets"] "__r", .return [.var "__r"]] hvalue
      (by rw [hload]; exact hlocked)
    exact RDrev.reEquivOfDispatch hcode hd hsource hrev
  · have rd4041 := vaultBlocks.vault_block_4031_fallthrough (by simp)
      (u256_eq_of_ne (Ne.symm hlocked)) rdBody
    have rd7108 := vaultBlocks.vault_block_4041 (by simp) (by native_decide) rd4041
    have hm := vaultConversionArgsMemory_reads (vaultDispatchMemory ⟨170435703⟩) assets ⟨0⟩ vaultMaxWord
    rcases vaultConvertSharesRoutine (isFloor := false) SourceState.init hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
      (by simp) (by native_decide) rd7108 with hsuccess | ⟨hcallee, hrev⟩
    · rcases hsuccess with ⟨evm', σ', locals', scratch, value, aw', out, k', C', hcallee, hs, _, rd4102⟩
      have hret := vaultBlocks.vault_block_4102 (by simp) rd4102
      change RDret fork vaultBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ'
        ((value.toByteArray.write 0 scratch 576 32).readWithPadding 576 32) at hret
      rw [toByteArray_write_read_back_of_gap _ _ _
        (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 576 (by norm_num)))] at hret
      have hsource := vaultViewBodyReturns (fn := vaultPreviewWithdrawFunction) hvalue
        (by rw [hload]; exact hlocked) hargEval rfl rfl (vaultSharesForwardReturns harg hcallee)
      exact hret.reEquivExecutionGen hcode hd hdec hsource hs.accounts
        (returnEquiv_of_encode (uint256ReturnEncoding _))
    · have hsource := vaultViewBodyReverts (fn := vaultPreviewWithdrawFunction) hvalue
        (by rw [hload]; exact hlocked) hargEval rfl rfl (vaultSharesForwardReverts harg hcallee)
      exact hrev.reEquivExecutionRevert hcode hd hdec hsource

theorem vaultPreviewWithdrawBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 7)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultPreviewWithdrawBodyCore hcode hsize hsel

end Benchmarks.CurveVault
