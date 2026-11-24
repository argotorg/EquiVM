import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.Lock
import Benchmarks.CurveVault.LendInternal

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

theorem vaultLend_aprBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 32)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 32) rfl hsel
  have hd : dispatchMsg contract I.calldata = some lend_aprTransition := by
    apply vaultDispatch_lend_apr
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := lend_aprTransition) (pc := UInt256.ofNat 1107)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 4 < UInt256.size) (by decide +kernel) (by native_decide)
    (fun h => False.elim (by omega)) (vaultReachLend_aprBody hcode hsz hsize hsel)
  intro hvalue _ k C rdBody
  have hdec : config.externalABI.decodeCalldata? (lend_aprTransition.params.map Param.name)
      (transitionSignature lend_aprTransition).paramTypes I.calldata = some ∅ := by
    change decodeCalldataWithMode .vyper [] [] I.calldata = some ∅
    exact decodeCalldataWithMode_empty_ok hsz
  have hload : Stele.EVM.transientLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨0⟩ =
      codeOwnerTransientWord I σ ⟨0⟩ := codeOwnerTransientWord_initState _
  by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
  · have rdRevert := vaultBlocks.vault_block_1107_taken (by simp)
      (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _
          rw [hlocked]; decide +kernel) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp) rdRevert
    have hsource (locals : Store) := vaultLockedBodyReverts (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I) locals
      [.internalCall "lend_apr_body" [] "__r", .return [.var "__r"]] hvalue
      (by rw [hload]; exact hlocked)
    exact RDrev.reEquivOfDispatch hcode hd hsource hrev
  · have rd1117 := vaultBlocks.vault_block_1107_fallthrough (by simp)
      (u256_eq_of_ne (Ne.symm hlocked)) rdBody
    rcases vaultLendRoutine SourceState.init (by simp) rd1117 with
      ⟨evm', σ', locals', value, hcallee, hs, hret⟩ | ⟨hcallee, hrev⟩
    · have hsource := vaultViewBodyReturns (fn := vaultLendFunction)
        (locals := ∅) (args := []) (argVals := []) hvalue (by rw [hload]; exact hlocked)
        (by simp [evalExprs?, pure]) rfl rfl hcallee
      exact hret.reEquivExecutionGen hcode hd hdec hsource hs.accounts
        (returnEquiv_of_encode (uint256ReturnEncoding _))
    · have hsource := vaultViewBodyReverts (fn := vaultLendFunction)
        (locals := ∅) (args := []) (argVals := []) hvalue (by rw [hload]; exact hlocked)
        (by simp [evalExprs?, pure]) rfl rfl hcallee
      exact hrev.reEquivExecutionRevert hcode hd hdec hsource

theorem vaultLend_aprBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 32)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultLend_aprBodyCore hcode hsize hsel
end Benchmarks.CurveVault
