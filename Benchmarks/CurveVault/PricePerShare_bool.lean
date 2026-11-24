import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.Lock
import Benchmarks.CurveVault.PriceInternal
import Benchmarks.CurveVault.Calldata

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault

theorem vaultPricePerShare_boolBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 11)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 11) rfl hsel
  have hd : dispatchMsg contract I.calldata = some pricePerShare_boolTransition := by
    apply vaultDispatch_pricePerShare_bool
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := pricePerShare_boolTransition) (pc := UInt256.ofNat 1517)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 36 < UInt256.size) (by decide +kernel) (by native_decide)
    decodeCalldataWithMode_vyper_bool_none_short (vaultReachPricePerShare_boolBody hcode hsz hsize hsel)
  intro hvalue hargs k C rdBody
  by_cases hcanon : (calldataWord I.calldata 4).toNat < 2
  · have rd1529 := vaultBlocks.vault_block_1517_fallthrough (by simp)
      (u256_shiftRight1_zero_of_lt _ hcanon) rdBody
    have rd1533 := vaultBlocks.vault_block_1529 (by simp [vaultBlocks.vault_block_1517_fallthrough_stack]) rd1529
    let isFloor := decide ((calldataWord I.calldata 4).toNat = 1)
    have hword : calldataWord I.calldata 4 = if isFloor then ⟨1⟩ else ⟨0⟩ := by
      exact (bool_toUInt256_decide _ hcanon).symm
    let locals : Store := (∅ : Store).insert "_is_floor" (.bool isFloor)
    have hdec : config.externalABI.decodeCalldata? (pricePerShare_boolTransition.params.map Param.name)
        (transitionSignature pricePerShare_boolTransition).paramTypes I.calldata = some locals :=
      decodeCalldataWithMode_vyper_bool_ok hargs hword
    have hargEval : evalExprs? config {contract := contract, locals := locals}
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) [.var "_is_floor"] = .ok [.bool isFloor] := by
      simp [locals, evalExprs?, evalExpr?, EvalResult.ofOption, bind, pure, EvalResult.bind]
    have hload : Stele.EVM.transientLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨0⟩ =
        codeOwnerTransientWord I σ ⟨0⟩ := codeOwnerTransientWord_initState _
    by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
    · have rdRevert := vaultBlocks.vault_block_1533_taken (by simp [vaultBlocks.vault_block_1529_stack])
        (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _
            rw [hlocked]; decide +kernel) (by native_decide) rd1533
      have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_1529_stack]) rdRevert
      have hsource (l : Store) := vaultLockedBodyReverts (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I) l
        [.internalCall "pricePerShare_body" [.var "_is_floor"] "__r", .return [.var "__r"]] hvalue
        (by rw [hload]; exact hlocked)
      exact RDrev.reEquivOfDispatch hcode hd hsource hrev
    · have rd1543 := vaultBlocks.vault_block_1533_fallthrough (by simp [vaultBlocks.vault_block_1529_stack])
        (u256_eq_of_ne (Ne.symm hlocked)) rd1533
      have hgap : 320 - (vaultDispatchMemory ⟨683696643⟩).size < USize.size :=
        lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 320 (by norm_num))
      have hmem : 352 ≤ ((calldataWord I.calldata 4).toByteArray.write 0 (vaultDispatchMemory ⟨683696643⟩) 320 32).size :=
        toByteArray_write_size_ge_off_add32 _ _ 320 hgap
      have hflag : memLoad (UInt256.ofNat 320)
          ((calldataWord I.calldata 4).toByteArray.write 0 (vaultDispatchMemory ⟨683696643⟩) 320 32) =
          if isFloor then ⟨1⟩ else ⟨0⟩ := (memLoad_write_back _ _ 320 (by decide +kernel) hgap).trans hword
      rcases vaultPriceRoutine (locals := locals) SourceState.init hmem (by simp [locals]) (by simp [locals])
        (by simp [locals]) hflag (by simp [vaultBlocks.vault_block_1529_stack]) rd1543 with
        ⟨evm', σ', locals', value, hcallee, hs, hret⟩ | ⟨hcallee, hrev⟩
      · have hsource := vaultViewBodyReturns (fn := vaultPriceFunction) hvalue
          (by rw [hload]; exact hlocked) hargEval rfl rfl hcallee
        exact hret.reEquivExecutionGen hcode hd hdec hsource hs.accounts
          (returnEquiv_of_encode (uint256ReturnEncoding _))
      · have hsource := vaultViewBodyReverts (fn := vaultPriceFunction) hvalue
          (by rw [hload]; exact hlocked) hargEval rfl rfl hcallee
        exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  · have rdRevert := vaultBlocks.vault_block_1517_taken (by simp)
      (fun hz => hcanon (u256_lt_two_of_shiftRight1_zero _ hz)) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_1517_taken_stack]) rdRevert
    exact hrev.reEquivDecodingFailed hcode hd
      (decodeCalldataWithMode_vyper_bool_none_noncanon hargs
        (fun hz => hcanon (by rw [hz]; decide +kernel))
        (fun ho => hcanon (by rw [ho]; decide +kernel))) rfl rfl

theorem vaultPricePerShare_boolBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 11)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultPricePerShare_boolBodyCore hcode hsize hsel

end Benchmarks.CurveVault
