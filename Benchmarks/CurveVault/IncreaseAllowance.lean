import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.AllowanceAdjustInternal

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultIncreaseAllowanceBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 16)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 16) rfl hsel
  have hd : dispatchMsg contract I.calldata = some increaseAllowanceTransition := by
    apply vaultDispatch_increaseAllowance
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := increaseAllowanceTransition) (pc := UInt256.ofNat 6012)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 68 < UInt256.size) (by decide +kernel) (by native_decide)
    (decodeCalldataWithMode_vyper_addr_uint256_none_short hsz)
    (vaultReachIncreaseAllowanceBody hcode hsz hsize hsel)
  intro hvalue hargs k C rdBody
  by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · have rdRevert := vaultBlocks.vault_block_6012_taken (by simp)
      (fun h => hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ h)) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_6012_taken_stack]) rdRevert
    exact hrev.reEquivDecodingFailed hcode hd
      (decodeCalldataWithMode_vyper_addr_uint256_none_noncanon hargs hcanon) rfl rfl
  let spender := calldataWord I.calldata 4
  let delta := calldataWord I.calldata 36
  let locals := ((∅ : Store).insert "_spender" (.address (AccountAddress.ofNat spender.toNat))).insert
    "_add_value" (.int (Int.ofNat delta.toNat))
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hdec : config.externalABI.decodeCalldata? (increaseAllowanceTransition.params.map Param.name)
      (transitionSignature increaseAllowanceTransition).paramTypes I.calldata = some locals :=
    decodeCalldataWithMode_vyper_addr_uint256_ok hargs hcanon
  have hload : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ = codeOwnerTransientWord I σ ⟨0⟩ :=
    codeOwnerTransientWord_initState _
  have rdLock := vaultBlocks.vault_block_6012_fallthrough (by simp)
    (u256_shiftRight160_zero_of_lt _ hcanon) rdBody
  by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
  · have rdRevert := vaultBlocks.vault_block_6024_taken (by simp)
      (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _; rw [hlocked]; decide +kernel)
      (by native_decide) rdLock
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_6024_taken_stack]) rdRevert
    have hsource := vaultLockedBodyReverts (fork := fork) evm locals (increaseAllowanceTransition.body.drop 2) hvalue
      (by rw [hload]; exact hlocked)
    exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  have rdStart := vaultBlocks.vault_block_6024_fallthrough (by simp)
    (u256_eq_of_ne (Ne.symm hlocked)) rdLock
  by_cases hperm : I.perm = true
  swap
  · have hp : I.perm = false := by simpa using hperm
    have hstatic := vaultAdjustStatic true hp (by simp [vaultBlocks.vault_block_6024_fallthrough_stack]) rdStart
    have hsource := vaultMutatingBodyStatic (fork := fork) evm locals (increaseAllowanceTransition.body.drop 3) hvalue
      (by rw [hload]; exact hlocked) hp
    exact hstatic.reEquivStaticHalt hcode hd hdec hsource
  let mem := spender.toByteArray.write 0 (vaultDispatchMemory ⟨961581905⟩) 192 32
  have hgap : 192 - (vaultDispatchMemory ⟨961581905⟩).size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 192 (by omega))
  have hsizeMem : 224 ≤ mem.size := toByteArray_write_size_ge_off_add32 _ _ 192 hgap
  have hms : memLoad (UInt256.ofNat 192) mem = spender := memLoad_write_back _ _ 192 (by decide +kernel) hgap
  obtain ⟨evm', σ', locals', hcallee, hs', hret⟩ := vaultAdjustRoutine true
    (locals := vaultAdjustLocals true (AccountAddress.ofNat spender.toNat) delta) SourceState.init hsizeMem
    (by simp [vaultAdjustLocals, vaultAdjustDeltaName]) (store_get_self _ _ _)
    (by simp only [vaultAdjustLocals, vaultAdjustDeltaName, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
    hms hcanon hperm (by simp [vaultBlocks.vault_block_6024_fallthrough_stack]) rdStart
  have hsource := vaultMutatingBodyReturns (hpermAfter := (congrArg ExecutionEnv.perm hs'.env).trans hperm) (hperm := by assumption) (fn := vaultAdjustFunction true) (locals := locals)
    (args := [.var "_spender", .var "_add_value"])
    (argVals := [.address (AccountAddress.ofNat spender.toNat), .int (Int.ofNat delta.toNat)])
    hvalue (by rw [hload]; exact hlocked)
    (by simp only [evalExprs?, evalExpr?, locals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.bind, pure, bind]; rfl) rfl rfl hcallee
  have hsFinal : SourceState evm I (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) (vaultSetLock evm' ⟨0⟩) := by
    unfold vaultSetLock
    rw [hs'.env]
    exact sourceStateTransientWrite hs' ⟨0⟩ ⟨0⟩
  exact hret.reEquivExecutionGen hcode hd hdec hsource hsFinal.accounts
    (returnEquiv_of_encode boolTrueReturnEncoding)

theorem vaultIncreaseAllowanceBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 16)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultIncreaseAllowanceBodyCore hcode hsize hsel
end Benchmarks.CurveVault
