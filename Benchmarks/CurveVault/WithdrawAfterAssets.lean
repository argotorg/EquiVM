import Benchmarks.CurveVault.WithdrawConversion
import Benchmarks.CurveVault.DebitMinimum

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultWithdrawAfterAssets {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver owner total : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 704 ≤ mem.size)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (ho : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hbc : locals.get? "_controller" = none) (hb : locals.get? "_borrowed_token" = none)
    (hallow : locals.get? "allowance" = none)
    (ha : locals.get? "_assets" = some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
    (ht : locals.get? "total_assets" = some (.int (Int.ofNat total.toNat)))
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmo : memLoad (UInt256.ofNat 608) mem = owner)
    (hmt : memLoad (UInt256.ofNat 672) mem = total)
    (hrcanon : receiver.toNat < EVM.addressModulus) (hocanon : owner.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hstack : R.length + 14 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 4202) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (shares : UInt256),
      ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction true).body.drop 1)
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat shares.toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) shares.toByteArray) ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction true).body.drop 1)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let prepared := vaultDebitMinimumMemory true mem
  have hmem : prepared = total.toByteArray.write 0 mem 640 32 := by
    change (memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem 640 32 = _
    rw [hmt]
  have hgap : 640 - mem.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 640 (by omega))
  have hframe : WordMemoryRange mem prepared 0 640 := by
    rw [hmem]; exact wordMemoryRange_write _ _ 640 0 640 hgap (Or.inl (by omega))
  have hread : memLoad (UInt256.ofNat 640) prepared = total := by
    rw [hmem]; exact memLoad_write_back _ _ 640 (by decide +kernel) hgap
  have hsize0 : 672 ≤ prepared.size := by
    rw [hmem]; exact toByteArray_write_size_ge_off_add32 _ _ 640 hgap
  rcases vaultDebitMinimum true ht ha hread rfl (by omega) h with
    ⟨aw0, k0, C0, hminimum, rdConvert⟩ | ⟨hminimum, hrev⟩
  swap
  · exact Or.inr ⟨ExecBlock.consRevert hminimum, hrev⟩
  rcases vaultWithdrawConversion hs hsize0 hr ho hbc hb hallow ha ht
    ((hframe.load 576 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmr)
    ((hframe.load 608 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmo)
    hread hrcanon hocanon hperm hstack rdConvert with
    ⟨evm1, σ1, locals1, shares, hrest, hs1, hret⟩ | ⟨hrest, hrev⟩
  · exact Or.inl ⟨evm1, σ1, locals1, shares, ExecBlock.consNormal hminimum hrest, hs1, hret⟩
  · exact Or.inr ⟨ExecBlock.consNormal hminimum hrest, hrev⟩

end Benchmarks.CurveVault
