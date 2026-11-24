import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.Calldata
import Benchmarks.CurveVault.SetMaxInternal

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

set_option maxRecDepth 2000000

theorem vaultSet_max_supplyBodyCore {σ σ₀ A I} {g : UInt256}
    (hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 26)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 26) rfl hsel
  have hd : dispatchMsg contract I.calldata = some set_max_supplyTransition := by
    apply vaultDispatch_set_max_supply
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := set_max_supplyTransition) (pc := UInt256.ofNat 851)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 36 < UInt256.size) (by decide +kernel) (by native_decide)
    decodeCalldataWithMode_vyper_uint256_none_short (vaultReachSet_max_supplyBody hcode hsz hsize hsel)
  intro hvalue hargs k C rdBody
  let value := calldataWord I.calldata 4
  let locals : Store := (∅ : Store).insert "_max_supply" (.int (Int.ofNat value.toNat))
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hdec : config.externalABI.decodeCalldata? (set_max_supplyTransition.params.map Param.name)
      (transitionSignature set_max_supplyTransition).paramTypes I.calldata = some locals :=
    decodeCalldataWithMode_vyper_uint256_ok hargs
  have hv : locals.get? "_max_supply" = some (.int (Int.ofNat value.toNat)) := by simp [locals]
  have hargEval := evalExprs?_singleton
    (evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := vaultSetLock evm ⟨1⟩) hv)
  have hload : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ = codeOwnerTransientWord I σ ⟨0⟩ :=
    codeOwnerTransientWord_initState _
  by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
  · have rdRevert := vaultBlocks.vault_block_851_taken (by simp)
      (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _; rw [hlocked]; decide +kernel)
      (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp) rdRevert
    have hsource := vaultLockedBodyReverts (fork := fork) evm locals (set_max_supplyTransition.body.drop 2) hvalue
      (by rw [hload]; exact hlocked)
    exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  have rd861 := vaultBlocks.vault_block_851_fallthrough (by simp)
    (u256_eq_of_ne (Ne.symm hlocked)) rdBody
  by_cases hperm : I.perm = true
  swap
  · have hp : I.perm = false := by simpa using hperm
    have rd863 := rd861.push1 (UInt256.ofNat 1) (by native_decide) (by simp)
    have rd864 := rd863.push0 (by native_decide) (by simp)
    have hstatic := tstoreStaticReach rd864 hp (by native_decide) (by simp)
    have hsource := vaultMutatingBodyStatic (fork := fork) evm locals (set_max_supplyTransition.body.drop 3) hvalue
      (by rw [hload]; exact hlocked) hp
    exact hstatic.reEquivStaticHalt hcode hd hdec hsource
  have hfactory : (codeOwnerStorageWord I σ ⟨4⟩).toNat < EVM.addressModulus :=
    vaultSlotWord_canonical hwf 4 (by omega)
  rcases vaultSetMaxRoutine (locals := locals) SourceState.init (by simp [locals])
    (by simp [locals]) hv hfactory hperm (by simp) rd861 with
    ⟨evm', σ', locals', hcallee, hs', hret⟩ | ⟨hcallee, hrev⟩
  swap
  · have hsource := vaultMutatingBodyReverts (fork := fork) (hperm := by assumption) (fn := vaultSetMaxFunction)
      hvalue (by rw [hload]; exact hlocked) hargEval rfl rfl hcallee
      (rest := [vaultLockAssignStmt ⟨0⟩])
    exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  have hsource := vaultMutatingBodyVoidReturns
    (hpermAfter := (congrArg ExecutionEnv.perm hs'.env).trans hperm)
    (hperm := hperm) (fn := vaultSetMaxFunction)
    hvalue (by rw [hload]; exact hlocked) hargEval rfl rfl hcallee
  have hsFinal : SourceState evm I (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) (vaultSetLock evm' ⟨0⟩) := by
    unfold vaultSetLock
    rw [hs'.env]
    exact sourceStateTransientWrite hs' ⟨0⟩ ⟨0⟩
  exact hret.reEquivExecutionGen hcode hd hdec hsource hsFinal.accounts
    (returnEquiv.fallthrough rfl rfl (by native_decide))

theorem vaultSet_max_supplyBody {σ σ₀ A I} {g : UInt256}
    (hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 26)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultSet_max_supplyBodyCore hwf hcode hsize hsel

end Benchmarks.CurveVault
