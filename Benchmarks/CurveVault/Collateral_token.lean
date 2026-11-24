import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.Storage
import Benchmarks.CurveVault.RuntimeBlocks_001

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultCollateral_tokenEval (evm : EVM.State) (locals : Store)
    (hlocals : locals.get? "_collateral_token" = none) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "_collateral_token", steps := []}) =
      .ok (.address (AccountAddress.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)) := by
  simpa only [wordToElem] using
    vaultEvalScalar evm locals "_collateral_token" .address
      ⟨1⟩ hlocals rfl rfl

theorem vaultCollateral_tokenBodyCore {σ σ₀ A I} {g : UInt256}
    (hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 10)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 10) rfl hsel
  have hd : dispatchMsg contract I.calldata = some collateral_tokenTransition := by
    apply vaultDispatch_collateral_token
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  have heval := vaultCollateral_tokenEval (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ (by simp)
  change evalExpr? config {contract := contract, locals := ∅}
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) _ =
    .ok (.address (AccountAddress.ofNat (Stele.EVM.storageLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner ⟨1⟩).toNat)) at heval
  rw [codeOwnerStorageWord_initState] at heval
  apply vaultNullaryReturn (t := collateral_tokenTransition)
    (pc := UInt256.ofNat 110)
    hcode hsize hsz hd rfl rfl heval
    (returnEquiv_of_encode (vaultAddressReturnEncoding (codeOwnerStorageWord I σ ⟨1⟩)
      (vaultSlotWord_canonical hwf 1 (by decide +kernel))))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by native_decide)
    (vaultReachCollateral_tokenBody hcode hsz hsize hsel)
  intro k C rdBody
  have hret := vaultBlocks.vault_block_110 (by simp) rdBody
  change RDret fork vaultBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    σ (((codeOwnerStorageWord I σ ⟨1⟩).toByteArray.write 0 _ 64 32).readWithPadding 64 32) at hret
  rwa [vaultWordReturn_read] at hret

theorem vaultCollateral_tokenBody {σ σ₀ A I} {g : UInt256}
    (hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 10)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultCollateral_tokenBodyCore hwf hcode hsize hsel

end Benchmarks.CurveVault
