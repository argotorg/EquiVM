import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.CreditEntry
import Benchmarks.CurveVault.AddressWord
import Benchmarks.CurveVault.Calldata

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultMint_uint256BodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 28)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 28) rfl hsel
  have hd : dispatchMsg contract I.calldata = some mint_uint256Transition := by
    apply vaultDispatch_mint_uint256
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := mint_uint256Transition) (pc := UInt256.ofNat 3136)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 36 < UInt256.size) (by decide +kernel) (by native_decide)
    decodeCalldataWithMode_vyper_uint256_none_short
    (vaultReachMint_uint256Body hcode hsz hsize hsel)
  intro hvalue hargs k C rdBody
  let decoded : Store := (∅ : Store).insert "_shares" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))
  let locals := decoded.insert "_receiver" (.address I.source)
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let receiver := UInt256.ofNat I.source.val
  let mem := receiver.toByteArray.write 0 (vaultDispatchMemory ⟨2691771752⟩) 576 32
  have hdec : config.externalABI.decodeCalldata? (mint_uint256Transition.params.map Param.name)
      (transitionSignature mint_uint256Transition).paramTypes I.calldata = some decoded :=
    decodeCalldataWithMode_vyper_uint256_ok hargs
  have hprefix : ExecBlock fork config {contract := contract, locals := decoded} evm
      (mint_uint256Transition.body.take 2) (.ok {contract := contract, locals := locals} evm) :=
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
      (ExecBlock.consNormal (ExecStmt.letDecl (by simp [evalExpr?, envValue, evm, initState, pure])) ExecBlock.nil)
  obtain ⟨aw', k', C', rdLock⟩ := vaultBlocks.vault_block_3136_packed (by simp) (by native_decide) rdBody
  have hgap : 576 - (vaultDispatchMemory ⟨2691771752⟩).size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 576 (by omega))
  exact vaultCreditEntry false hcode hd hdec rfl rfl hprefix
    (by rw [store_get_ne _ _ (by decide +kernel)]; exact store_get_self _ _ _)
    (by rw [addressWord_roundtrip]; exact store_get_self _ _ _)
    (toByteArray_write_size_ge_off_add32 _ _ 576 hgap)
    (memLoad_write_back _ _ 576 (by decide +kernel) hgap)
    (addressWord_canonical I.source) (by simp) rdLock

theorem vaultMint_uint256Body {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 28)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultMint_uint256BodyCore hcode hsize hsel

end Benchmarks.CurveVault
