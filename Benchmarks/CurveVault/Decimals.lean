import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.RuntimeBlocks_023

variable {fork : Ethereum.Fork}

/-! Refinement of the constant uint8 getter, including the nonpayable guard. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault

theorem vaultDecimalsBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 14)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 14) rfl hsel
  have hd : dispatchMsg contract I.calldata = some decimalsTransition := by
    apply vaultDispatch_decimals
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultNullaryReturn (t := decimalsTransition) (expr := .intLit 18)
    (value := .int 18) (out := (⟨18⟩ : UInt256).toByteArray)
    (pc := UInt256.ofNat 6426)
    hcode hsize hsz hd rfl rfl (by simp [evalExpr?, pure])
    (returnEquiv_of_encode (uint8ReturnEncoding ⟨18⟩ (by decide +kernel)))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by native_decide)
    (vaultReachDecimalsBody hcode hsz hsize hsel)
  intro k C rdBody
  have hret := vaultBlocks.vault_block_6426 (by simp) rdBody
  change RDret fork vaultBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    σ (((⟨18⟩ : UInt256).toByteArray.write 0 (vaultDispatchMemory ⟨826074471⟩) 64 32).readWithPadding 64 32) at hret
  rwa [toByteArray_write_read_back_of_gap _ _ _
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by norm_num)))] at hret

theorem vaultDecimalsBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 14)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultDecimalsBodyCore hcode hsize hsel

end Benchmarks.CurveVault
