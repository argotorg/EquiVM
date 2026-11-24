import Benchmarks.CurveVault.DebitBurn
import Benchmarks.CurveVault.DebitMinimum

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultRedeemAfterConversion {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver owner total assets : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 736 ≤ mem.size)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (ho : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hbc : locals.get? "_controller" = none) (hb : locals.get? "_borrowed_token" = none)
    (ha : locals.get? "assets_to_redeem" = some (.int (Int.ofNat assets.toNat)))
    (hv : locals.get? "_shares" = some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
    (ht : locals.get? "total_assets" = some (.int (Int.ofNat total.toNat)))
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmo : memLoad (UInt256.ofNat 608) mem = owner)
    (hmt : memLoad (UInt256.ofNat 640) mem = total)
    (hmv : memLoad (UInt256.ofNat 704) mem = assets)
    (hrcanon : receiver.toNat < EVM.addressModulus) (hocanon : owner.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hstack : R.length + 9 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 5272) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store),
      ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction false).body.drop 3)
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat assets.toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) assets.toByteArray) ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction false).body.drop 3)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let prepared := vaultDebitMinimumMemory false mem
  have hmem : prepared = assets.toByteArray.write 0 mem 672 32 := by
    change (memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem 672 32 = _
    rw [hmv]
  have hgap : 672 - mem.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 672 (by omega))
  have hframe : WordMemoryRange mem prepared 0 672 := by
    rw [hmem]; exact wordMemoryRange_write _ _ 672 0 672 hgap (Or.inl (by omega))
  have ht0 : memLoad (UInt256.ofNat 640) prepared = total :=
    (hframe.load 640 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmt
  have hv0 : memLoad (UInt256.ofNat 672) prepared = assets := by
    rw [hmem]; exact memLoad_write_back _ _ 672 (by decide +kernel) hgap
  have hsize0 : 704 ≤ prepared.size := by
    rw [hmem]; exact toByteArray_write_size_ge_off_add32 _ _ 672 hgap
  rcases vaultDebitMinimum false ht ha ht0 hv0 (by omega) h with
    ⟨aw0, k0, C0, hminimum, rdBurn⟩ | ⟨hminimum, hrev⟩
  swap
  · exact Or.inr ⟨ExecBlock.consRevert hminimum, hrev⟩
  rcases vaultDebitBurn false hs hsize0 hr ho hbc hb ha hv
    ((hframe.load 576 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmr)
    ((hframe.load 608 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmo)
    hv0 rfl hrcanon hocanon hperm hstack rdBurn with
    ⟨evm1, σ1, locals1, hrest, hs1, hret⟩ | ⟨hrest, hrev⟩
  · exact Or.inl ⟨evm1, σ1, locals1, ExecBlock.consNormal hminimum hrest, hs1, hret⟩
  · exact Or.inr ⟨ExecBlock.consNormal hminimum hrest, hrev⟩

end Benchmarks.CurveVault
