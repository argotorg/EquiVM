import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.TransferFromInternal

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

set_option maxHeartbeats 400000 in
theorem vaultTransferFromBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 9)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 9) rfl hsel
  have hd : dispatchMsg contract I.calldata = some transferFromTransition := by
    apply vaultDispatch_transferFrom
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := transferFromTransition) (pc := UInt256.ofNat 5688)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 100 < UInt256.size) (by decide +kernel) (by native_decide)
    (decodeCalldataWithMode_vyper_address_address_uint256_none_short hsz)
    (vaultReachTransferFromBody hcode hsz hsize hsel)
  intro hvalue hargs k C rdBody
  by_cases hcanon0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · have rdRevert := vaultBlocks.vault_block_5688_taken (by simp)
      (fun h => hcanon0 (u256_lt_addressModulus_of_shiftRight160_zero _ h)) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_5688_taken_stack]) rdRevert
    exact hrev.reEquivDecodingFailed hcode hd
      (decodeCalldataWithMode_vyper_address_address_uint256_none_noncanon0 hargs hcanon0) rfl rfl
  have rd5700 := vaultBlocks.vault_block_5688_fallthrough (by simp)
    (u256_shiftRight160_zero_of_lt _ hcanon0) rdBody
  by_cases hcanon1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
  swap
  · have rdRevert := vaultBlocks.vault_block_5700_taken (by simp)
      (fun h => hcanon1 (u256_lt_addressModulus_of_shiftRight160_zero _ h)) (by native_decide) rd5700
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_5700_taken_stack]) rdRevert
    exact hrev.reEquivDecodingFailed hcode hd
      (decodeCalldataWithMode_vyper_address_address_uint256_none_noncanon1 hargs hcanon0 hcanon1) rfl rfl
  let sender := calldataWord I.calldata 4
  let recipient := calldataWord I.calldata 36
  let value := calldataWord I.calldata 68
  let locals := (((∅ : Store).insert "_from" (.address (AccountAddress.ofNat sender.toNat))).insert
    "_to" (.address (AccountAddress.ofNat recipient.toNat))).insert "_value" (.int (Int.ofNat value.toNat))
  let calleeLocals := vaultTransferLocals (AccountAddress.ofNat sender.toNat) (AccountAddress.ofNat recipient.toNat) value
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hdec : config.externalABI.decodeCalldata? (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = some locals :=
    decodeCalldataWithMode_vyper_address_address_uint256_ok hargs hcanon0 hcanon1
  have hload : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ = codeOwnerTransientWord I σ ⟨0⟩ :=
    codeOwnerTransientWord_initState _
  have rd5714 := vaultBlocks.vault_block_5700_fallthrough (by simp)
    (u256_shiftRight160_zero_of_lt _ hcanon1) rd5700
  by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
  · have rdRevert := vaultBlocks.vault_block_5714_taken (by simp)
      (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _; rw [hlocked]; decide +kernel)
      (by native_decide) rd5714
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_5714_taken_stack]) rdRevert
    have hsource := vaultLockedBodyReverts (fork := fork) evm locals (transferFromTransition.body.drop 2) hvalue
      (by rw [hload]; exact hlocked)
    exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  have rd5726 := vaultBlocks.vault_block_5714_fallthrough (by simp)
    (u256_eq_of_ne (Ne.symm hlocked)) rd5714
  by_cases hperm : I.perm = true
  swap
  · have hp : I.perm = false := by simpa using hperm
    have rd5728 := rd5726.push1 (UInt256.ofNat 1) (by native_decide)
      (by simp [vaultBlocks.vault_block_5714_fallthrough_stack])
    have rd5729 := rd5728.push0 (by native_decide)
      (by simp [vaultBlocks.vault_block_5714_fallthrough_stack])
    have hstatic := tstoreStaticReach rd5729 hp (by native_decide)
      (by simp [vaultBlocks.vault_block_5714_fallthrough_stack])
    have hsource := vaultMutatingBodyStatic (fork := fork) evm locals (transferFromTransition.body.drop 3) hvalue
      (by rw [hload]; exact hlocked) hp
    exact hstatic.reEquivStaticHalt hcode hd hdec hsource
  let first := sender.toByteArray.write 0 (vaultDispatchMemory ⟨599290589⟩) 192 32
  let mem := recipient.toByteArray.write 0 first 224 32
  have hgap (d : Nat) (hd : d ≤ 224) (m : ByteArray) : d - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize d (by omega))
  have hsizeFirst : 224 ≤ first.size := toByteArray_write_size_ge_off_add32 _ _ 192 (hgap _ (by omega) _)
  have hsizeMem : 256 ≤ mem.size := toByteArray_write_size_ge_off_add32 _ _ 224 (hgap _ (by omega) _)
  have hmf : memLoad (UInt256.ofNat 192) mem = sender := by
    rw [memLoad_below_write _ _ 224 192 hsizeFirst (by omega) (hgap _ (by omega) _) (by decide +kernel)]
    exact memLoad_write_back _ _ 192 (by decide +kernel) (hgap _ (by omega) _)
  have hmt : memLoad (UInt256.ofNat 224) mem = recipient := memLoad_write_back _ _ 224 (by decide +kernel) (hgap _ (by omega) _)
  have hbase : calleeLocals.get? "allowance" = none := by
    dsimp only [calleeLocals, vaultTransferLocals]
    rw [store_get_ne _ _ (by decide +kernel), store_get_ne _ _ (by decide +kernel),
      store_get_ne _ _ (by decide +kernel)]
    exact store_get_empty _
  have hf : calleeLocals.get? "_from" = some (.address (AccountAddress.ofNat sender.toNat)) := by
    simp only [calleeLocals, vaultTransferLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have ht : calleeLocals.get? "_to" = some (.address (AccountAddress.ofNat recipient.toNat)) := by
    simp only [calleeLocals, vaultTransferLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hv : calleeLocals.get? "_value" = some (.int (Int.ofNat value.toNat)) := by
    simp only [calleeLocals, vaultTransferLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hcallArgs : evalExprs? config {contract := contract, locals := locals} (vaultSetLock evm ⟨1⟩)
      [.var "_from", .var "_to", .var "_value"] =
      .ok [.address (AccountAddress.ofNat sender.toNat), .address (AccountAddress.ofNat recipient.toNat),
        .int (Int.ofNat value.toNat)] := by
    simp only [evalExprs?, evalExpr?, locals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.bind, pure, bind]
    rfl
  rcases vaultTransferFromRoutine SourceState.init hsizeMem hmf hmt hcanon0 hcanon1 hbase hf ht hv hperm
    (by simp [vaultBlocks.vault_block_5714_fallthrough_stack]) rd5726 with
    ⟨evm', σ', locals', hcallee, hs', hret⟩ | ⟨hcallee, hrev⟩
  swap
  · have hsource := vaultMutatingBodyReverts (fork := fork) (hperm := by assumption) (fn := vaultTransferFromFunction) hvalue
      (by rw [hload]; exact hlocked) hcallArgs rfl rfl hcallee
    exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  have hsource := vaultMutatingBodyReturns (hpermAfter := (congrArg ExecutionEnv.perm hs'.env).trans hperm) (hperm := by assumption) (fn := vaultTransferFromFunction) hvalue
    (by rw [hload]; exact hlocked) hcallArgs rfl rfl hcallee
  have hsFinal : SourceState evm I (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) (vaultSetLock evm' ⟨0⟩) := by
    unfold vaultSetLock
    rw [hs'.env]
    exact sourceStateTransientWrite hs' ⟨0⟩ ⟨0⟩
  exact hret.reEquivExecutionGen hcode hd hdec hsource hsFinal.accounts
    (returnEquiv_of_encode boolTrueReturnEncoding)

theorem vaultTransferFromBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 9)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultTransferFromBodyCore hcode hsize hsel

end Benchmarks.CurveVault
