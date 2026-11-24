import Benchmarks.CurveVault.RedeemAfterConversion
import Benchmarks.CurveVault.MutationConversion

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultRedeemAfterAssets {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver owner total : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 704 ≤ mem.size)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (ho : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hbc : locals.get? "_controller" = none) (hb : locals.get? "_borrowed_token" = none)
    (hv : locals.get? "_shares" = some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
    (ht : locals.get? "total_assets" = some (.int (Int.ofNat total.toNat)))
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmo : memLoad (UInt256.ofNat 608) mem = owner)
    (hmt : memLoad (UInt256.ofNat 672) mem = total)
    (hrcanon : receiver.toNat < EVM.addressModulus) (hocanon : owner.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hstack : R.length + 14 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 5232) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (assets : UInt256),
      ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction false).body.drop 2)
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat assets.toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) assets.toByteArray) ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction false).body.drop 2)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  have hargs : evalExprs? config {contract := contract, locals := locals} evm
      [.var "_shares", .boolLit true, .var "total_assets"] =
      .ok [.int (Int.ofNat (calldataWord I.calldata 4).toNat), .bool true, .int (Int.ofNat total.toNat)] := by
    simp only [evalExprs?, evalExpr?, hv, ht, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rcases vaultMutationConversion .redeem (retVar := "assets_to_redeem") hs hsize hmt hargs hstack h with
    ⟨evm1, σ1, mem1, assets, aw1, out, k1, C1, hcall, hs1, hframe, hsize1, hread, rdNext⟩ | ⟨hcall, hrev⟩
  swap
  · exact Or.inr ⟨ExecBlock.consRevert hcall, hrev⟩
  let baseMem := vaultMutationConversionBase .redeem mem total
  have hgap : 640 - mem.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 640 (by omega))
  have hframe0 := vaultMutationConversionBase_frame .redeem mem total
  have hframe1 : WordMemoryRange mem mem1 576 640 :=
    (hframe0.mono (by omega) (le_refl _)).trans (hframe.mono (le_refl _) (by omega))
  have ht0 : memLoad (UInt256.ofNat 640) mem1 = total := by
    rw [hframe.load 640 (by omega) (by omega) (toByteArray_write_size_ge_off_add32 _ _ 640 hgap) (by decide +kernel)]
    exact memLoad_write_back _ _ 640 (by decide +kernel) hgap
  let locals1 := locals.insert "assets_to_redeem" (.int (Int.ofNat assets.toNat))
  rcases vaultRedeemAfterConversion (locals := locals1) hs1 hsize1
    (by rw [store_get_ne _ _ (by decide +kernel), hr])
    (by rw [store_get_ne _ _ (by decide +kernel), ho])
    (by rw [store_get_ne _ _ (by decide +kernel), hbc])
    (by rw [store_get_ne _ _ (by decide +kernel), hb]) (store_get_self _ _ _)
    (by rw [store_get_ne _ _ (by decide +kernel), hv])
    (by rw [store_get_ne _ _ (by decide +kernel), ht])
    ((hframe1.load 576 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmr)
    ((hframe1.load 608 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmo)
    ht0 hread hrcanon hocanon hperm (by omega) rdNext with
    ⟨evm2, σ2, locals2, hrest, hs2, hret⟩ | ⟨hrest, hrev⟩
  · exact Or.inl ⟨evm2, σ2, locals2, assets, ExecBlock.consNormal hcall hrest, hs2, hret⟩
  · exact Or.inr ⟨ExecBlock.consNormal hcall hrest, hrev⟩

end Benchmarks.CurveVault
