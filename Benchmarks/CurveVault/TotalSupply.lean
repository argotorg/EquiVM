import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.Storage
import Benchmarks.CurveVault.RuntimeBlocks_024

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultTotalSupplyEval (evm : EVM.State) (locals : Store)
    (hlocals : locals.get? "totalSupply" = none) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "totalSupply", steps := []}) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat)) := by
  simpa only [wordToElem, normalizeInt_uint256_word] using
    vaultEvalScalar evm locals "totalSupply" (.int (.uint ⟨256, by decide⟩))
      ⟨14⟩ hlocals rfl rfl

theorem vaultTotalSupplyBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 8)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 8) rfl hsel
  have hd : dispatchMsg contract I.calldata = some totalSupplyTransition := by
    apply vaultDispatch_totalSupply
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  have heval := vaultTotalSupplyEval (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ (by simp)
  change evalExpr? config {contract := contract, locals := ∅}
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) _ =
    .ok (.int (Int.ofNat (Stele.EVM.storageLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner ⟨14⟩).toNat)) at heval
  rw [codeOwnerStorageWord_initState] at heval
  apply vaultNullaryReturn (t := totalSupplyTransition)
    (pc := UInt256.ofNat 6756)
    hcode hsize hsz hd rfl rfl heval
    (returnEquiv_of_encode (uint256ReturnEncoding (codeOwnerStorageWord I σ ⟨14⟩)))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by native_decide)
    (vaultReachTotalSupplyBody hcode hsz hsize hsel)
  intro k C rdBody
  have hret := vaultBlocks.vault_block_6756 (by simp) rdBody
  change RDret fork vaultBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    σ (((codeOwnerStorageWord I σ ⟨14⟩).toByteArray.write 0 _ 64 32).readWithPadding 64 32) at hret
  rwa [vaultWordReturn_read] at hret

theorem vaultTotalSupplyBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 8)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultTotalSupplyBodyCore hcode hsize hsel

end Benchmarks.CurveVault
