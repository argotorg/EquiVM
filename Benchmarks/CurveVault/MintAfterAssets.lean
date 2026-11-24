import Benchmarks.CurveVault.MintAfterConversion
import Benchmarks.CurveVault.MutationConversion

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultMintAfterAssets {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver controller total : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 704 ≤ mem.size)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (hc : locals.get? "controller" = some (.address (AccountAddress.ofUInt256 controller)))
    (hw : locals.get? "controller_word" = some (.int (Int.ofNat controller.toNat)))
    (hb : locals.get? "_borrowed_token" = none) (hmax : locals.get? "maxSupply" = none)
    (hv : locals.get? "_shares" = some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
    (ht : locals.get? "total_assets" = some (.int (Int.ofNat total.toNat)))
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmc : memLoad (UInt256.ofNat 608) mem = controller)
    (hmt : memLoad (UInt256.ofNat 672) mem = total)
    (hcanon : receiver.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hstack : R.length + 14 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 3320) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (assets : UInt256),
      ExecBlock fork config {contract := contract, locals := locals} evm ((vaultCreditFunction false).body.drop 4)
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat assets.toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) assets.toByteArray) ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm ((vaultCreditFunction false).body.drop 4)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let shares := calldataWord I.calldata 4
  let baseMem := total.toByteArray.write 0 mem 640 32
  have hgap (m : ByteArray) (off : Nat) (hoff : off ≤ 704) : off - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize off (by omega))
  have hfBase := vaultMutationConversionBase_frame .mint mem total
  have hbaseSize : 672 ≤ baseMem.size := toByteArray_write_size_ge_off_add32 _ _ 640 (hgap _ _ (by omega))
  have hbaseTotal : memLoad (UInt256.ofNat 640) baseMem = total :=
    memLoad_write_back _ _ 640 (by decide +kernel) (hgap _ _ (by omega))
  have hargs : evalExprs? config {contract := contract, locals := locals} evm
      [.var "_shares", .boolLit false, .var "total_assets"] =
      .ok [.int (Int.ofNat shares.toNat), .bool false, .int (Int.ofNat total.toNat)] := by
    simp only [evalExprs?, evalExpr?, hv, ht, EvalResult.ofOption, EvalResult.bind, bind, pure]
    rfl
  rcases vaultMutationConversion .mint (retVar := "assets") hs hsize hmt hargs hstack h with
    ⟨evm1, σ1, returned, assets, aw1, out, k1, C1, hcall, hs1, hkeep, hsize1, hread, rdLimits⟩ | ⟨hcall, hrev⟩
  swap
  · exact Or.inr ⟨ExecBlock.consRevert hcall, hrev⟩
  let locals1 := locals.insert "assets" (.int (Int.ofNat assets.toNat))
  have hkeep0 : WordMemoryRange mem returned 576 640 :=
    (hfBase.mono (by omega) (le_refl _)).trans (hkeep.mono (le_refl _) (by omega))
  rcases vaultMintAfterConversion (locals := locals1) hs1
    hsize1
    (by rw [store_get_ne _ _ (by decide +kernel), hr])
    (by rw [store_get_ne _ _ (by decide +kernel), hc])
    (by rw [store_get_ne _ _ (by decide +kernel), hw])
    (by rw [store_get_ne _ _ (by decide +kernel), hb])
    (by rw [store_get_ne _ _ (by decide +kernel), hmax]) (store_get_self _ _ _)
    (by rw [store_get_ne _ _ (by decide +kernel), hv])
    (by rw [store_get_ne _ _ (by decide +kernel), ht])
    ((hkeep0.load 576 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmr)
    ((hkeep0.load 608 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmc)
    ((hkeep.load 640 (by omega) (by omega) hbaseSize (by decide +kernel)).trans hbaseTotal)
    hread hcanon hperm (by omega) rdLimits with
    ⟨evm2, σ2, locals2, hrest, hs2, hret⟩ | ⟨hrest, hrev⟩
  · exact Or.inl ⟨evm2, σ2, locals2, assets, ExecBlock.consNormal hcall hrest, hs2, hret⟩
  · exact Or.inr ⟨ExecBlock.consNormal hcall hrest, hrev⟩

end Benchmarks.CurveVault
