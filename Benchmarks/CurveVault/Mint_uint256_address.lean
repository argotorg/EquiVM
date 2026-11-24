import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.CreditEntry
import Benchmarks.CurveVault.UintAddressABI

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultMint_uint256_addressBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 27)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 27) rfl hsel
  have hd : dispatchMsg contract I.calldata = some mint_uint256_addressTransition := by
    apply vaultDispatch_mint_uint256_address
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := mint_uint256_addressTransition) (pc := UInt256.ofNat 3146)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 68 < UInt256.size) (by decide +kernel) (by native_decide)
    (decodeCalldata_vyper_uint256_address_none_short hsz)
    (vaultReachMint_uint256_addressBody hcode hsz hsize hsel)
  intro hvalue hargs k C rdBody
  by_cases hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus
  swap
  · obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_3146_taken_packed (by simp)
      (fun hz => hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ hz)) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_3146_taken_stack]) rdFail
    exact hrev.reEquivDecodingFailed hcode hd
      (decodeCalldata_vyper_uint256_address_none_noncanon hargs hcanon) rfl rfl
  let receiver := calldataWord I.calldata 36
  let locals : Store := ((∅ : Store).insert "_shares" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))).insert
    "_receiver" (.address (AccountAddress.ofNat receiver.toNat))
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let mem := receiver.toByteArray.write 0 (vaultDispatchMemory ⟨2495578189⟩) 576 32
  have hdec : config.externalABI.decodeCalldata? (mint_uint256_addressTransition.params.map Param.name)
      (transitionSignature mint_uint256_addressTransition).paramTypes I.calldata = some locals :=
    decodeCalldata_vyper_uint256_address_ok hargs hcanon
  have hprefix : ExecBlock fork config {contract := contract, locals := locals} evm
      (mint_uint256_addressTransition.body.take 1) (.ok {contract := contract, locals := locals} evm) :=
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue)) ExecBlock.nil
  obtain ⟨aw0, k0, C0, rdStore⟩ := vaultBlocks.vault_block_3146_fallthrough_packed (by simp)
    (u256_shiftRight160_zero_of_lt _ hcanon) rdBody
  obtain ⟨aw1, k1, C1, rdLock⟩ := vaultBlocks.vault_block_3158_packed
    (by simp [vaultBlocks.vault_block_3146_fallthrough_stack]) rdStore
  have hgap : 576 - (vaultDispatchMemory ⟨2495578189⟩).size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 576 (by omega))
  exact vaultCreditEntry false hcode hd hdec rfl rfl hprefix
    (by rw [store_get_ne _ _ (by decide +kernel)]; exact store_get_self _ _ _)
    (store_get_self _ _ _)
    (toByteArray_write_size_ge_off_add32 _ _ 576 hgap)
    (memLoad_write_back _ _ 576 (by decide +kernel) hgap)
    hcanon (by simp [vaultBlocks.vault_block_3158_stack]) rdLock

theorem vaultMint_uint256_addressBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 27)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultMint_uint256_addressBodyCore hcode hsize hsel

end Benchmarks.CurveVault
