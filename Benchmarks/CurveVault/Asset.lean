import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.Storage
import Benchmarks.CurveVault.Lock
import Benchmarks.CurveVault.RuntimeBlocks_007

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultAssetFunction : FunctionDecl := contract.functions[3]!

theorem vaultAssetFunctionReturns (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_borrowed_token" = none) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm vaultAssetFunction.body
      (.returned {contract := contract, locals := locals} evm
        (some [.address (AccountAddress.ofNat
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)])) := by
  have heval := vaultEvalScalar evm locals "_borrowed_token" .address ⟨0⟩ hbase rfl rfl
  exact ExecFuncBody.execBlockRet <| ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton heval))

theorem vaultAssetBodyCore {σ σ₀ A I} {g : UInt256}
    (hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 15)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 15) rfl hsel
  have hd : dispatchMsg contract I.calldata = some assetTransition := by
    apply vaultDispatch_asset
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := assetTransition) (pc := UInt256.ofNat 1459)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 4 < UInt256.size) (by decide +kernel) (by native_decide)
    (fun h => False.elim (by omega)) (vaultReachAssetBody hcode hsz hsize hsel)
  intro hvalue _ k C rdBody
  have hdec : config.externalABI.decodeCalldata? (assetTransition.params.map Param.name)
      (transitionSignature assetTransition).paramTypes I.calldata = some ∅ := by
    change decodeCalldataWithMode .vyper [] [] I.calldata = some ∅
    exact decodeCalldataWithMode_empty_ok hsz
  have hload : Stele.EVM.transientLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨0⟩ =
      codeOwnerTransientWord I σ ⟨0⟩ := codeOwnerTransientWord_initState _
  by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
  · have rdRevert := vaultBlocks.vault_block_1459_taken (by simp)
      (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _
          rw [hlocked]; decide +kernel) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp) rdRevert
    have hsource (locals : Store) := vaultLockedBodyReverts (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I) locals
      [.internalCall "asset_body" [] "__r", .return [.var "__r"]] hvalue
      (by rw [hload]; exact hlocked)
    exact RDrev.reEquivOfDispatch hcode hd hsource hrev
  · have rd1469 := vaultBlocks.vault_block_1459_fallthrough (by simp)
      (u256_eq_of_ne (Ne.symm hlocked)) rdBody
    have hret := vaultBlocks.vault_block_1469 (by simp) rd1469
    change RDret fork vaultBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      σ (((codeOwnerStorageWord I σ ⟨0⟩).toByteArray.write 0 _ 64 32).readWithPadding 64 32) at hret
    rw [vaultWordReturn_read] at hret
    have hcallee := vaultAssetFunctionReturns (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ (by simp)
    change ExecFuncBody fork config _ _ _ (.returned _ _ (some [.address (AccountAddress.ofNat
      (Stele.EVM.storageLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner ⟨0⟩).toNat)])) at hcallee
    rw [codeOwnerStorageWord_initState] at hcallee
    have hsource := vaultViewBodyReturns (fn := vaultAssetFunction) (locals := ∅) (args := []) (argVals := [])
      hvalue (by rw [hload]; exact hlocked)
      (by simp [evalExprs?, pure]) rfl rfl hcallee
    exact hret.reEquivExecution hcode hd hdec hsource
      (returnEquiv_of_encode (vaultAddressReturnEncoding (codeOwnerStorageWord I σ ⟨0⟩)
        (vaultSlotWord_canonical hwf 0 (by decide +kernel))))

theorem vaultAssetBody {σ σ₀ A I} {g : UInt256}
    (hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 15)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultAssetBodyCore hwf hcode hsize hsel

end Benchmarks.CurveVault
