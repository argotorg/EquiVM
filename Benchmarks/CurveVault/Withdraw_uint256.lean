import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.DebitEntry
import Benchmarks.CurveVault.DebitArguments
import Benchmarks.CurveVault.Calldata

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault

theorem vaultWithdraw_uint256BodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 1)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 1) rfl hsel
  have hd : dispatchMsg contract I.calldata = some withdraw_uint256Transition := by
    apply vaultDispatch_withdraw_uint256
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := withdraw_uint256Transition) (pc := UInt256.ofNat 4107)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 36 < UInt256.size) (by decide +kernel) (by native_decide)
    decodeCalldataWithMode_vyper_uint256_none_short
    (vaultReachWithdraw_uint256Body hcode hsz hsize hsel)
  intro hvalue hargs k C rdBody
  let decoded : Store := (∅ : Store).insert "_assets" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))
  let locals := (decoded.insert "_receiver" (.address I.source)).insert "_owner" (.address I.source)
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let caller := UInt256.ofNat I.source.val
  have hdec : config.externalABI.decodeCalldata? (withdraw_uint256Transition.params.map Param.name)
      (transitionSignature withdraw_uint256Transition).paramTypes I.calldata = some decoded :=
    decodeCalldataWithMode_vyper_uint256_ok hargs
  have hprefix : ExecBlock fork config {contract := contract, locals := decoded} evm
      (withdraw_uint256Transition.body.take 3) (.ok {contract := contract, locals := locals} evm) :=
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
      (ExecBlock.consNormal (ExecStmt.letDecl (by simp [evalExpr?, envValue, evm, initState, pure]))
        (ExecBlock.consNormal (ExecStmt.letDecl (by simp [evalExpr?, envValue, evm, initState, pure])) ExecBlock.nil))
  obtain ⟨aw', k', C', rdLock⟩ := vaultBlocks.vault_block_4107_packed (by simp) (by native_decide) rdBody
  obtain ⟨hms, hmr, hmo⟩ := vaultDebitArguments_reads (vaultDispatchMemory ⟨773487949⟩) caller caller
  exact vaultDebitEntry true hcode hd hdec rfl rfl hprefix
    (by rw [store_get_ne _ _ (by decide +kernel), store_get_ne _ _ (by decide +kernel)]; exact store_get_self _ _ _)
    (by rw [addressWord_roundtrip, store_get_ne _ _ (by decide +kernel)]; exact store_get_self _ _ _)
    (by rw [addressWord_roundtrip]; exact store_get_self _ _ _)
    hmo (addressWord_canonical I.source) hms hmr (addressWord_canonical I.source) (by simp) rdLock

theorem vaultWithdraw_uint256Body {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 1)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultWithdraw_uint256BodyCore hcode hsize hsel

end Benchmarks.CurveVault
