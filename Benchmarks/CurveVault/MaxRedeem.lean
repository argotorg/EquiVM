import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.Lock
import Benchmarks.CurveVault.MaxRedeemInternal

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault

theorem vaultMaxRedeemBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 40)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 40) rfl hsel
  have hd : dispatchMsg contract I.calldata = some maxRedeemTransition := by
    apply vaultDispatch_maxRedeem
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := maxRedeemTransition) (pc := UInt256.ofNat 4783)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 36 < UInt256.size) (by decide +kernel) (by native_decide)
    (decodeCalldataWithMode_vyper_address_none_short hsz) (vaultReachMaxRedeemBody hcode hsz hsize hsel)
  intro hvalue hargs k C rdBody
  by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  · have rd4795 := vaultBlocks.vault_block_4783_fallthrough (by simp)
      (u256_shiftRight160_zero_of_lt _ hcanon) rdBody
    let receiver := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
    let locals : Store := (∅ : Store).insert "_owner" (.address receiver)
    have hdec : config.externalABI.decodeCalldata? (maxRedeemTransition.params.map Param.name)
        (transitionSignature maxRedeemTransition).paramTypes I.calldata = some locals :=
      decodeCalldataWithMode_vyper_address_ok hargs hcanon
    have hargEval : evalExprs? config {contract := contract, locals := locals}
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) [.var "_owner"] = .ok [.address receiver] := by
      simp [locals, evalExprs?, evalExpr?, EvalResult.ofOption, bind, pure, EvalResult.bind]
    have hload : Stele.EVM.transientLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨0⟩ =
        codeOwnerTransientWord I σ ⟨0⟩ := codeOwnerTransientWord_initState _
    by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
    · have rdRevert := vaultBlocks.vault_block_4795_taken (by simp)
        (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _
            rw [hlocked]; decide +kernel) (by native_decide) rd4795
      have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_4795_taken_stack]) rdRevert
      have hsource (l : Store) := vaultLockedBodyReverts (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I) l
        [.internalCall "maxRedeem_body" [.var "_owner"] "__r", .return [.var "__r"]] hvalue
        (by rw [hload]; exact hlocked)
      exact RDrev.reEquivOfDispatch hcode hd hsource hrev
    · have rd4808 := vaultBlocks.vault_block_4795_fallthrough (by simp)
        (u256_eq_of_ne (Ne.symm hlocked)) rd4795
      have hgap : 576 - (vaultDispatchMemory ⟨3641014142⟩).size < USize.size :=
        lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 576 (by norm_num))
      have hmem : 608 ≤ ((calldataWord I.calldata 4).toByteArray.write 0 (vaultDispatchMemory ⟨3641014142⟩) 576 32).size :=
        le_trans (by omega) (toByteArray_write_size_ge_off_add32 _ _ 576 hgap)
      rcases vaultMaxRedeemRoutine (locals := locals) SourceState.init hmem
        (memLoad_write_back _ _ 576 (by decide +kernel) hgap) hcanon (by simp [locals]) (by simp [locals, receiver])
        (by simp [vaultBlocks.vault_block_4795_fallthrough_stack]) rd4808 with
        ⟨evm', σ', locals', value, hcallee, hs, hret⟩ | ⟨hcallee, hrev⟩
      · have hsource := vaultViewBodyReturns (fn := vaultMaxRedeemFunction) hvalue
          (by rw [hload]; exact hlocked) hargEval rfl rfl hcallee
        exact hret.reEquivExecutionGen hcode hd hdec hsource hs.accounts
          (returnEquiv_of_encode (uint256ReturnEncoding _))
      · have hsource := vaultViewBodyReverts (fn := vaultMaxRedeemFunction) hvalue
          (by rw [hload]; exact hlocked) hargEval rfl rfl hcallee
        exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  · have rdRevert := vaultBlocks.vault_block_4783_taken (by simp)
      (fun hz => hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ hz)) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_4783_taken_stack]) rdRevert
    exact hrev.reEquivDecodingFailed hcode hd
      (decodeCalldataWithMode_vyper_address_none_noncanon hargs hcanon) rfl rfl

theorem vaultMaxRedeemBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 40)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultMaxRedeemBodyCore hcode hsize hsel

end Benchmarks.CurveVault
