import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.Storage
import Benchmarks.CurveVault.RuntimeBlocks_001

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultControllerBodyCore {σ σ₀ A I} {g : UInt256}
    (hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 43)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 43) rfl hsel
  have hd : dispatchMsg contract I.calldata = some controllerTransition := by
    apply vaultDispatch_controller
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  have heval := vaultControllerEval (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ (by simp)
  change evalExpr? config {contract := contract, locals := ∅}
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) _ =
    .ok (.address (AccountAddress.ofNat (Stele.EVM.storageLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner ⟨3⟩).toNat)) at heval
  rw [codeOwnerStorageWord_initState] at heval
  apply vaultNullaryReturn (t := controllerTransition)
    (pc := UInt256.ofNat 134)
    hcode hsize hsz hd rfl rfl heval
    (returnEquiv_of_encode (vaultAddressReturnEncoding (codeOwnerStorageWord I σ ⟨3⟩)
      (vaultSlotWord_canonical hwf 3 (by decide +kernel))))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by native_decide)
    (vaultReachControllerBody hcode hsz hsize hsel)
  intro k C rdBody
  have hret := vaultBlocks.vault_block_134 (by simp) rdBody
  change RDret fork vaultBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    σ (((codeOwnerStorageWord I σ ⟨3⟩).toByteArray.write 0 _ 64 32).readWithPadding 64 32) at hret
  rwa [vaultWordReturn_read] at hret

theorem vaultControllerBody {σ σ₀ A I} {g : UInt256}
    (hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 43)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultControllerBodyCore hwf hcode hsize hsel

end Benchmarks.CurveVault
