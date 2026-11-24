import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.DebitEntry
import Benchmarks.CurveVault.DebitArguments
import Benchmarks.CurveVault.UintAddressABI

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault

theorem vaultRedeem_uint256_addressBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 23)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 23) rfl hsel
  have hd : dispatchMsg contract I.calldata = some redeem_uint256_addressTransition := by
    apply vaultDispatch_redeem_uint256_address
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := redeem_uint256_addressTransition) (pc := UInt256.ofNat 5024)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 68 < UInt256.size) (by decide +kernel) (by native_decide)
    (decodeCalldata_vyper_uint256_address_none_short hsz)
    (vaultReachRedeem_uint256_addressBody hcode hsz hsize hsel)
  intro hvalue hargs k C rdBody
  by_cases hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus
  swap
  · obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_5024_taken_packed (by simp)
      (fun hz => hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ hz)) (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_5024_taken_stack]) rdFail
    exact hrev.reEquivDecodingFailed hcode hd
      (decodeCalldata_vyper_uint256_address_none_noncanon hargs hcanon) rfl rfl
  let receiver := calldataWord I.calldata 36
  let owner := UInt256.ofNat I.source.val
  let decoded : Store := ((∅ : Store).insert "_shares" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))).insert
    "_receiver" (.address (AccountAddress.ofNat receiver.toNat))
  let locals := decoded.insert "_owner" (.address I.source)
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hdec : config.externalABI.decodeCalldata? (redeem_uint256_addressTransition.params.map Param.name)
      (transitionSignature redeem_uint256_addressTransition).paramTypes I.calldata = some decoded :=
    decodeCalldata_vyper_uint256_address_ok hargs hcanon
  have hprefix : ExecBlock fork config {contract := contract, locals := decoded} evm
      (redeem_uint256_addressTransition.body.take 2) (.ok {contract := contract, locals := locals} evm) :=
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
      (ExecBlock.consNormal (ExecStmt.letDecl (by simp [evalExpr?, envValue, evm, initState, pure])) ExecBlock.nil)
  obtain ⟨aw0, k0, C0, rdStore⟩ := vaultBlocks.vault_block_5024_fallthrough_packed (by simp)
    (u256_shiftRight160_zero_of_lt _ hcanon) rdBody
  obtain ⟨aw1, k1, C1, rdLock⟩ := vaultBlocks.vault_block_5036_packed
    (by simp [vaultBlocks.vault_block_5024_fallthrough_stack]) (by native_decide) rdStore
  obtain ⟨hms, hmr, hmo⟩ := vaultDebitArguments_reads (vaultDispatchMemory ⟨2078180082⟩) receiver owner
  exact vaultDebitEntry false hcode hd hdec rfl rfl hprefix
    (by rw [store_get_ne _ _ (by decide +kernel), store_get_ne _ _ (by decide +kernel)]; exact store_get_self _ _ _)
    (by rw [store_get_ne _ _ (by decide +kernel)]; exact store_get_self _ _ _)
    (by rw [addressWord_roundtrip]; exact store_get_self _ _ _)
    hmo (addressWord_canonical I.source) hms hmr hcanon (by simp [vaultBlocks.vault_block_5036_stack]) rdLock

theorem vaultRedeem_uint256_addressBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 23)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultRedeem_uint256_addressBodyCore hcode hsize hsel

end Benchmarks.CurveVault
