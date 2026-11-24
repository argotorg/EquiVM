import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.Lock
import Benchmarks.CurveVault.MaxMintInternal

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault

theorem vaultMaxMintBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 36)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 36) rfl hsel
  have hd : dispatchMsg contract I.calldata = some maxMintTransition := by
    apply vaultDispatch_maxMint
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := maxMintTransition) (pc := UInt256.ofNat 2886)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 36 < UInt256.size) (by decide +kernel) (by native_decide)
    (decodeCalldataWithMode_vyper_address_none_short hsz) (vaultReachMaxMintBody hcode hsz hsize hsel)
  intro hvalue hargs k C rdBody
  by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  · have rd2898 := vaultBlocks.vault_block_2886_fallthrough (by simp)
      (u256_shiftRight160_zero_of_lt _ hcanon) rdBody
    let receiver := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
    let locals : Store := (∅ : Store).insert "_receiver" (.address receiver)
    have hdec : config.externalABI.decodeCalldata? (maxMintTransition.params.map Param.name)
        (transitionSignature maxMintTransition).paramTypes I.calldata = some locals :=
      decodeCalldataWithMode_vyper_address_ok hargs hcanon
    have hargEval : evalExprs? config {contract := contract, locals := locals}
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) [.var "_receiver"] = .ok [.address receiver] := by
      simp [locals, evalExprs?, evalExpr?, EvalResult.ofOption, bind, pure, EvalResult.bind]
    have hload : Stele.EVM.transientLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨0⟩ =
        codeOwnerTransientWord I σ ⟨0⟩ := codeOwnerTransientWord_initState _
    by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
    · have rdRevert := vaultBlocks.vault_block_2898_taken (by simp)
        (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _
            rw [hlocked]; decide +kernel) (by native_decide) rd2898
      have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_2898_taken_stack]) rdRevert
      have hsource (l : Store) := vaultLockedBodyReverts (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I) l
        [.internalCall "maxMint_body" [.var "_receiver"] "__r", .return [.var "__r"]] hvalue
        (by rw [hload]; exact hlocked)
      exact RDrev.reEquivOfDispatch hcode hd hsource hrev
    · have rd2911 := vaultBlocks.vault_block_2898_fallthrough (by simp)
        (u256_eq_of_ne (Ne.symm hlocked)) rd2898
      rcases vaultMaxMintRoutine (locals := locals) SourceState.init (by simp [locals])
        (by simp [vaultBlocks.vault_block_2898_fallthrough_stack]) rd2911 with
        ⟨evm', σ', locals', value, hcallee, hs, hret⟩ | ⟨hcallee, hrev⟩
      · have hsource := vaultViewBodyReturns (fn := vaultMaxMintFunction) hvalue
          (by rw [hload]; exact hlocked) hargEval rfl rfl hcallee
        exact hret.reEquivExecutionGen hcode hd hdec hsource hs.accounts
          (returnEquiv_of_encode (uint256ReturnEncoding _))
      · have hsource := vaultViewBodyReverts (fn := vaultMaxMintFunction) hvalue
          (by rw [hload]; exact hlocked) hargEval rfl rfl hcallee
        exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  · have rdRevert := vaultBlocks.vault_block_2886_taken (by simp)
      (fun hz => hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ hz)) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_2886_taken_stack]) rdRevert
    exact hrev.reEquivDecodingFailed hcode hd
      (decodeCalldataWithMode_vyper_address_none_noncanon hargs hcanon) rfl rfl

theorem vaultMaxMintBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 36)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultMaxMintBodyCore hcode hsize hsel

end Benchmarks.CurveVault
