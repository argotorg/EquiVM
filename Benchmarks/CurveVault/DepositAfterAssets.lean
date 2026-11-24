import Benchmarks.CurveVault.CreditLimits
import Benchmarks.CurveVault.DepositConversion
import Benchmarks.CurveVault.CreditTail

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultDepositAfterAssetsBody_eq : (vaultCreditFunction true).body.drop 3 =
    vaultCreditLimitsBody true ++ vaultDepositConversionBody ++ (vaultCreditFunction true).body.drop 8 := rfl

theorem vaultDepositAfterAssets {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver controller total : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 704 ≤ mem.size)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (hc : locals.get? "controller" = some (.address (AccountAddress.ofUInt256 controller)))
    (hw : locals.get? "controller_word" = some (.int (Int.ofNat controller.toNat)))
    (hb : locals.get? "_borrowed_token" = none) (hmax : locals.get? "maxSupply" = none)
    (ha : locals.get? "_assets" = some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
    (ht : locals.get? "total_assets" = some (.int (Int.ofNat total.toNat)))
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmc : memLoad (UInt256.ofNat 608) mem = controller)
    (hmt : memLoad (UInt256.ofNat 672) mem = total)
    (hcanon : receiver.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hstack : R.length + 14 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 2190) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (shares : UInt256),
      ExecBlock fork config {contract := contract, locals := locals} evm ((vaultCreditFunction true).body.drop 3)
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat shares.toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) shares.toByteArray) ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm ((vaultCreditFunction true).body.drop 3)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  rw [vaultDepositAfterAssetsBody_eq, List.append_assoc]
  let prepared := vaultCreditLimitsMemory true mem
  have hprepared : prepared = total.toByteArray.write 0 mem 640 32 := by
    change (memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem 640 32 = _
    rw [hmt]
  have hgap : 640 - mem.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 640 (by omega))
  have htotal : memLoad (UInt256.ofNat 640) prepared = total := by
    rw [hprepared]; exact memLoad_write_back _ _ 640 (by decide +kernel) hgap
  have hframe : WordMemoryRange mem prepared 0 640 := by
    rw [hprepared]; exact wordMemoryRange_write _ _ 640 0 640 hgap (Or.inl (by omega))
  rcases vaultCreditLimits true hs ht ha hmax htotal rfl (by omega) h with
    ⟨aw0, k0, C0, hlimits, rdConvert⟩ | ⟨hlimits, hrev⟩
  swap
  · exact Or.inr ⟨execBlock_reverted_append hlimits, hrev⟩
  let locals1 := locals.insert "max_supply" (.int (Int.ofNat (codeOwnerStorageWord I σ ⟨5⟩).toNat))
  rcases vaultDepositConversion (locals := locals1) hs (by have hh := hframe.size; omega)
    (by rw [store_get_ne _ _ (by decide +kernel), ha])
    (by rw [store_get_ne _ _ (by decide +kernel), ht]) htotal hstack rdConvert with
    ⟨evm1, σ1, mem1, out, shares, aw1, k1, C1, hconvert, hs1, hframe1, hsize1, hshares, rdTail⟩ | ⟨hconvert, hrev⟩
  swap
  · exact Or.inr ⟨execBlock_append hlimits (execBlock_reverted_append hconvert), hrev⟩
  let locals2 := locals1.insert "to_mint" (.int (Int.ofNat shares.toNat))
  have hlocals (name : Ident) (hm : ("max_supply" == name) = false) (htm : ("to_mint" == name) = false) :
      locals2.get? name = locals.get? name := store_get_ne2 _ _ _ hm htm
  have hkeep : WordMemoryRange mem mem1 576 640 :=
    (hframe.mono (by omega) (le_refl _)).trans (hframe1.mono (le_refl _) (by omega))
  rcases vaultCreditTail true (locals := locals2) hs1 hsize1
    (by rw [hlocals _ (by decide +kernel) (by decide +kernel), hr])
    (by rw [hlocals _ (by decide +kernel) (by decide +kernel), hc])
    (by rw [hlocals _ (by decide +kernel) (by decide +kernel), hw])
    (by rw [hlocals _ (by decide +kernel) (by decide +kernel), hb])
    (by rw [hlocals _ (by decide +kernel) (by decide +kernel)]; exact ha)
    (store_get_self _ _ _)
    ((hkeep.load 576 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmr)
    ((hkeep.load 608 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmc)
    hshares rfl hcanon hperm (by omega) rdTail with
    ⟨evm2, σ2, locals3, htail, hs2, hret⟩ | ⟨htail, hrev⟩
  · exact Or.inl ⟨evm2, σ2, locals3, shares,
      execBlock_append hlimits (execBlock_append hconvert htail), hs2, hret⟩
  · exact Or.inr ⟨execBlock_append hlimits (execBlock_append hconvert htail), hrev⟩

end Benchmarks.CurveVault
