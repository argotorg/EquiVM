import Benchmarks.CurveVault.DebitTotalAssets
import Benchmarks.CurveVault.RedeemAllowance

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultDebitRoutine (isWithdraw : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver owner : UInt256} {R : List UInt256}
    (hs : SourceState s0 I σ evm) (hsize : 640 ≤ mem.size)
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmo : memLoad (UInt256.ofNat 608) mem = owner)
    (hrcanon : receiver.toNat < EVM.addressModulus) (hocanon : owner.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hstack : R.length + 14 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat (if isWithdraw then 4188 else 5090)) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (value : UInt256),
      ExecFuncBody fork config {contract := contract, locals := (vaultDebitLocals isWithdraw (AccountAddress.ofNat receiver.toNat)
        (AccountAddress.ofNat owner.toNat) (calldataWord I.calldata 4))}
        (vaultSetLock evm ⟨1⟩) (vaultDebitFunction isWithdraw).body
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat value.toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) value.toByteArray) ∨
    (ExecFuncBody fork config {contract := contract, locals := (vaultDebitLocals isWithdraw (AccountAddress.ofNat receiver.toNat)
      (AccountAddress.ofNat owner.toNat) (calldataWord I.calldata 4))}
      (vaultSetLock evm ⟨1⟩) (vaultDebitFunction isWithdraw).body .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let locals := vaultDebitLocals isWithdraw (AccountAddress.ofNat receiver.toNat)
    (AccountAddress.ofNat owner.toNat) (calldataWord I.calldata 4)
  have hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)) := by
    cases isWithdraw <;> simp only [locals, vaultDebitLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl
  have ho : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)) := by
    cases isWithdraw <;> simp only [locals, vaultDebitLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl
  have hbc : locals.get? "_controller" = none := by cases isWithdraw <;> simp [locals, vaultDebitLocals]
  have hb : locals.get? "_borrowed_token" = none := by cases isWithdraw <;> simp [locals, vaultDebitLocals]
  have hallow : locals.get? "allowance" = none := by cases isWithdraw <;> simp [locals, vaultDebitLocals]
  have hi : locals.get? (if isWithdraw then "_assets" else "_shares") =
      some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)) := store_get_self _ _ _
  have hprep :
      (∃ (evm0 : State) (σ0 : AccountMap) (locals0 : Store) (mem0 : ByteArray) (aw0 : UInt256) (k0 C0 : Nat),
        ExecBlock fork config {contract := contract, locals := locals} (vaultSetLock evm ⟨1⟩)
          ((vaultDebitFunction isWithdraw).body.take (if isWithdraw then 0 else 1))
          (.ok {contract := contract, locals := locals0} evm0) ∧
        SourceState s0 I σ0 evm0 ∧ WordMemoryRange mem mem0 192 640 ∧
        (∀ name, ("allowance_" == name) = false → ("__c0" == name) = false →
          locals0.get? name = locals.get? name) ∧
        RD fork vaultBytecode I g s0 (UInt256.ofNat 6772)
          (UInt256.ofNat 672 :: UInt256.ofNat (if isWithdraw then 4202 else 5232) :: R) mem0 aw0 rdata σ0 k0 C0) ∨
      (ExecFuncBody fork config {contract := contract, locals := locals} (vaultSetLock evm ⟨1⟩)
        (vaultDebitFunction isWithdraw).body .reverted ∧ RDrev fork vaultBytecode g s0) := by
    cases isWithdraw
    · rcases vaultRedeemAllowance hs hsize ho hi hallow hmo hocanon hperm (by omega) h with
        ⟨evm0, σ0, locals0, mem0, aw0, k0, C0, hallowance, hs0, hframe, hget, rdNext⟩ | ⟨hallowance, hrev⟩
      · obtain ⟨aw1, k1, C1, rdAssets⟩ := vaultBlocks.vault_block_5221_packed (by omega) (by native_decide) rdNext
        exact Or.inl ⟨evm0, σ0, locals0, mem0, aw1, k1, C1,
          ExecBlock.consNormal hallowance ExecBlock.nil, hs0, hframe, hget, rdAssets⟩
      · exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert hallowance), hrev⟩
    · have hs0 : SourceState s0 I (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩) (vaultSetLock evm ⟨1⟩) := by
        unfold vaultSetLock
        rw [hs.env]
        exact sourceStateTransientWrite hs ⟨0⟩ ⟨1⟩
      obtain ⟨aw0, k0, C0, rdAssets⟩ := vaultBlocks.vault_block_4188_packed (by omega) hperm (by native_decide) h
      exact Or.inl ⟨_, _, locals, mem, aw0, k0, C0, ExecBlock.nil, hs0, WordMemoryRange.refl _ _ _,
        fun _ _ _ => rfl, rdAssets⟩
  rcases hprep with ⟨evm0, σ0, locals0, mem0, aw0, k0, C0, hprefix, hs0, hframe, hget, rdAssets⟩ | hrev
  swap
  · exact Or.inr hrev
  rcases vaultDebitTotalAssets isWithdraw (locals := locals0) hs0 (le_trans hsize hframe.size)
    ((hget "_receiver" (by decide +kernel) (by decide +kernel)).trans hr)
    ((hget "_owner" (by decide +kernel) (by decide +kernel)).trans ho)
    ((hget "_controller" (by decide +kernel) (by decide +kernel)).trans hbc)
    ((hget "_borrowed_token" (by decide +kernel) (by decide +kernel)).trans hb)
    ((hget "allowance" (by decide +kernel) (by decide +kernel)).trans hallow)
    ((hget _ (by cases isWithdraw <;> decide +kernel) (by cases isWithdraw <;> decide +kernel)).trans hi)
    ((hframe.load 576 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmr)
    ((hframe.load 608 (by omega) (by omega) hsize (by decide +kernel)).trans hmo)
    hrcanon hocanon hperm hstack rdAssets with
    ⟨evm1, σ1, locals1, value, hrest, hs1, hret⟩ | ⟨hrest, hrev⟩
  · refine Or.inl ⟨evm1, σ1, locals1, value, ExecFuncBody.execBlockRet ?_, hs1, hret⟩
    simpa only [List.take_append_drop] using execBlock_append hprefix hrest
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    simpa only [List.take_append_drop] using execBlock_append hprefix hrest

end Benchmarks.CurveVault
