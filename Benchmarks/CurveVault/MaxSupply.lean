import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.Storage
import Benchmarks.CurveVault.RuntimeBlocks_023

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultMaxSupplyEval (evm : EVM.State) (locals : Store)
    (hlocals : locals.get? "maxSupply" = none) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "maxSupply", steps := []}) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)) := by
  simpa only [wordToElem, normalizeInt_uint256_word] using
    vaultEvalScalar evm locals "maxSupply" (.int (.uint ⟨256, by decide⟩))
      ⟨5⟩ hlocals rfl rfl

theorem vaultMaxSupplyBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 39)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 39) rfl hsel
  have hd : dispatchMsg contract I.calldata = some maxSupplyTransition := by
    apply vaultDispatch_maxSupply
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  have heval := vaultMaxSupplyEval (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ (by simp)
  change evalExpr? config {contract := contract, locals := ∅}
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) _ =
    .ok (.int (Int.ofNat (Stele.EVM.storageLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner ⟨5⟩).toNat)) at heval
  rw [codeOwnerStorageWord_initState] at heval
  apply vaultNullaryReturn (t := maxSupplyTransition)
    (pc := UInt256.ofNat 6414)
    hcode hsize hsz hd rfl rfl heval
    (returnEquiv_of_encode (uint256ReturnEncoding (codeOwnerStorageWord I σ ⟨5⟩)))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by native_decide)
    (vaultReachMaxSupplyBody hcode hsz hsize hsel)
  intro k C rdBody
  have hret := vaultBlocks.vault_block_6414 (by simp) rdBody
  change RDret fork vaultBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    σ (((codeOwnerStorageWord I σ ⟨5⟩).toByteArray.write 0 _ 64 32).readWithPadding 64 32) at hret
  rwa [vaultWordReturn_read] at hret

theorem vaultMaxSupplyBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 39)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultMaxSupplyBodyCore hcode hsize hsel

end Benchmarks.CurveVault
