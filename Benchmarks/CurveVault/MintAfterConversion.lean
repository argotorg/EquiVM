import Benchmarks.CurveVault.CreditLimits
import Benchmarks.CurveVault.CreditTail

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultMintAfterConversionBody_eq : (vaultCreditFunction false).body.drop 5 =
    vaultCreditLimitsBody false ++ (vaultCreditFunction false).body.drop 8 := rfl

theorem vaultMintAfterConversion {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver controller total assets : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 736 ≤ mem.size)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (hc : locals.get? "controller" = some (.address (AccountAddress.ofUInt256 controller)))
    (hw : locals.get? "controller_word" = some (.int (Int.ofNat controller.toNat)))
    (hb : locals.get? "_borrowed_token" = none) (hmax : locals.get? "maxSupply" = none)
    (ha : locals.get? "assets" = some (.int (Int.ofNat assets.toNat)))
    (hv : locals.get? "_shares" = some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
    (ht : locals.get? "total_assets" = some (.int (Int.ofNat total.toNat)))
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmc : memLoad (UInt256.ofNat 608) mem = controller)
    (hmt : memLoad (UInt256.ofNat 640) mem = total)
    (hma : memLoad (UInt256.ofNat 704) mem = assets)
    (hcanon : receiver.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 3359) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store),
      ExecBlock fork config {contract := contract, locals := locals} evm ((vaultCreditFunction false).body.drop 5)
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat assets.toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) assets.toByteArray) ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm ((vaultCreditFunction false).body.drop 5)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  rw [vaultMintAfterConversionBody_eq]
  let prepared := vaultCreditLimitsMemory false mem
  have hprepared : prepared = assets.toByteArray.write 0 mem 672 32 := by
    change (memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem 672 32 = _
    rw [hma]
  have hgap : 672 - mem.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 672 (by omega))
  have hframe : WordMemoryRange mem prepared 0 672 := by
    rw [hprepared]; exact wordMemoryRange_write _ _ 672 0 672 hgap (Or.inl (by omega))
  have htotal : memLoad (UInt256.ofNat 640) prepared = total :=
    (hframe.load 640 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmt
  have hassets : memLoad (UInt256.ofNat 672) prepared = assets := by
    rw [hprepared]; exact memLoad_write_back _ _ 672 (by decide +kernel) hgap
  rcases vaultCreditLimits false hs ht ha hmax htotal hassets (by omega) h with
    ⟨aw0, k0, C0, hlimits, rdTail⟩ | ⟨hlimits, hrev⟩
  swap
  · exact Or.inr ⟨execBlock_reverted_append hlimits, hrev⟩
  let locals1 := locals.insert "max_supply" (.int (Int.ofNat (codeOwnerStorageWord I σ ⟨5⟩).toNat))
  have hlocals (name : Ident) (hn : ("max_supply" == name) = false) :
      locals1.get? name = locals.get? name := store_get_ne _ _ hn
  rcases vaultCreditTail false (locals := locals1) hs (by have hh := hframe.size; omega)
    (by rw [hlocals _ (by decide +kernel)]; exact hr)
    (by rw [hlocals _ (by decide +kernel)]; exact hc)
    (by rw [hlocals _ (by decide +kernel)]; exact hw)
    (by rw [hlocals _ (by decide +kernel)]; exact hb)
    (by rw [hlocals _ (by decide +kernel)]; exact ha)
    (by rw [hlocals _ (by decide +kernel)]; exact hv)
    ((hframe.load 576 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmr)
    ((hframe.load 608 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmc)
    hassets rfl hcanon hperm hstack rdTail with
    ⟨evm1, σ1, locals2, htail, hs1, hret⟩ | ⟨htail, hrev⟩
  · exact Or.inl ⟨evm1, σ1, locals2, execBlock_append hlimits htail, hs1, hret⟩
  · exact Or.inr ⟨execBlock_append hlimits htail, hrev⟩

end Benchmarks.CurveVault
