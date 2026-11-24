import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.DebitEntry
import Benchmarks.CurveVault.DebitArguments
import Benchmarks.CurveVault.UintTwoAddressABI

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault

theorem vaultWithdraw_uint256_address_addressBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 2)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 2) rfl hsel
  have hd : dispatchMsg contract I.calldata = some withdraw_uint256_address_addressTransition := by
    apply vaultDispatch_withdraw_uint256_address_address
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := withdraw_uint256_address_addressTransition) (pc := UInt256.ofNat 4147)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 100 < UInt256.size) (by decide +kernel) (by native_decide)
    (decodeCalldata_vyper_uint256_address_address_none_short hsz)
    (vaultReachWithdraw_uint256_address_addressBody hcode hsz hsize hsel)
  intro hvalue hargs k C rdBody
  by_cases hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus
  swap
  · obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_4147_taken_packed (by simp)
      (fun hz => hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ hz)) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_4147_taken_stack]) rdFail
    exact hrev.reEquivDecodingFailed hcode hd
      (decodeCalldata_vyper_uint256_address_address_none_noncanon0 hargs hcanon) rfl rfl
  obtain ⟨aw0, k0, C0, rdOwner⟩ := vaultBlocks.vault_block_4147_fallthrough_packed (by simp)
    (u256_shiftRight160_zero_of_lt _ hcanon) rdBody
  by_cases hocanon : (calldataWord I.calldata 68).toNat < EVM.addressModulus
  swap
  · obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_4159_taken_packed
      (by simp [vaultBlocks.vault_block_4147_fallthrough_stack])
      (fun hz => hocanon (u256_lt_addressModulus_of_shiftRight160_zero _ hz)) (by native_decide) rdOwner
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_4159_taken_stack]) rdFail
    exact hrev.reEquivDecodingFailed hcode hd
      (decodeCalldata_vyper_uint256_address_address_none_noncanon1 hargs hcanon hocanon) rfl rfl
  let receiver := calldataWord I.calldata 36
  let owner := calldataWord I.calldata 68
  let locals : Store := (((∅ : Store).insert "_assets" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))).insert
    "_receiver" (.address (AccountAddress.ofNat receiver.toNat))).insert "_owner" (.address (AccountAddress.ofNat owner.toNat))
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hdec : config.externalABI.decodeCalldata? (withdraw_uint256_address_addressTransition.params.map Param.name)
      (transitionSignature withdraw_uint256_address_addressTransition).paramTypes I.calldata = some locals :=
    decodeCalldata_vyper_uint256_address_address_ok hargs hcanon hocanon
  have hprefix : ExecBlock fork config {contract := contract, locals := locals} evm
      (withdraw_uint256_address_addressTransition.body.take 1) (.ok {contract := contract, locals := locals} evm) :=
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue)) ExecBlock.nil
  obtain ⟨aw1, k1, C1, rdStore⟩ := vaultBlocks.vault_block_4159_fallthrough_packed
    (by simp [vaultBlocks.vault_block_4147_fallthrough_stack])
    (u256_shiftRight160_zero_of_lt _ hocanon) rdOwner
  obtain ⟨aw2, k2, C2, rdLock⟩ := vaultBlocks.vault_block_4174_packed
    (by simp [vaultBlocks.vault_block_4159_fallthrough_stack]) rdStore
  obtain ⟨hms, hmr, hmo⟩ := vaultDebitArguments_reads (vaultDispatchMemory ⟨3026235284⟩) receiver owner
  exact vaultDebitEntry true hcode hd hdec rfl rfl hprefix
    (by rw [store_get_ne _ _ (by decide +kernel), store_get_ne _ _ (by decide +kernel)]; exact store_get_self _ _ _)
    (by rw [store_get_ne _ _ (by decide +kernel)]; exact store_get_self _ _ _)
    (store_get_self _ _ _) hmo hocanon hms hmr hcanon
    (by simp [vaultBlocks.vault_block_4174_stack]) rdLock

theorem vaultWithdraw_uint256_address_addressBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 2)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultWithdraw_uint256_address_addressBodyCore hcode hsize hsel

end Benchmarks.CurveVault
