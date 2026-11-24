import Benchmarks.CurveVault.DebitAllowance
import Benchmarks.CurveVault.MutatingLock

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultRedeemAllowance {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 640 ≤ mem.size)
    (ho : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hv : locals.get? "_shares" = some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
    (hbase : locals.get? "allowance" = none)
    (hmo : memLoad (UInt256.ofNat 608) mem = owner) (hcanon : owner.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 5090) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecStmt fork config {contract := contract, locals := locals} (vaultSetLock evm ⟨1⟩)
        ((vaultDebitFunction false).body[0]!) (.ok {contract := contract, locals := locals'} evm') ∧
      SourceState s0 I σ' evm' ∧ WordMemoryRange mem mem' 192 640 ∧
      (∀ name, ("allowance_" == name) = false → ("__c0" == name) = false →
        locals'.get? name = locals.get? name) ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat 5221) R mem' aw' rdata σ' k' C') ∨
    (ExecStmt fork config {contract := contract, locals := locals} (vaultSetLock evm ⟨1⟩)
      ((vaultDebitFunction false).body[0]!) .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let evm0 := vaultSetLock evm ⟨1⟩
  let σ0 := tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩
  have hs0 : SourceState s0 I σ0 evm0 := by
    unfold evm0 vaultSetLock
    rw [hs.env]
    exact sourceStateTransientWrite hs ⟨0⟩ ⟨1⟩
  have hcond := evalExpr_ne_address_word hcanon
    (show evalExpr? config {contract := contract, locals := locals} evm0 (.var "_owner") =
      .ok (.address (AccountAddress.ofNat owner.toNat)) by rw [evalExpr?]; simp only [ho, EvalResult.ofOption])
    (show evalExpr? config {contract := contract, locals := locals} evm0 (.env .caller) =
      .ok (.address I.source) by simp only [evalExpr?, envValue, hs0.env, pure])
  by_cases heq : owner = UInt256.ofNat I.source.val
  · obtain ⟨aw0, k0, C0, rdNext⟩ := vaultBlocks.vault_block_5090_taken_packed (by omega) hperm
      (by rw [hmo, heq, u256_eq_refl]; decide +kernel) (by native_decide) h
    exact Or.inl ⟨evm0, σ0, locals, mem, aw0, k0, C0,
      ExecStmt.iteFalse (by simpa only [heq, ne_eq, not_true_eq_false, decide_false] using hcond) ExecBlock.nil,
      hs0, WordMemoryRange.refl _ _ _, fun _ _ _ => rfl, rdNext⟩
  obtain ⟨aw0, k0, C0, rdAllowance⟩ := vaultBlocks.vault_block_5090_fallthrough_packed (by omega) hperm
    (by rw [hmo]; exact u256_eq_of_ne heq) h
  have hcondTrue : evalExpr? config {contract := contract, locals := locals} evm0
      (.binary .ne (.var "_owner") (.env .caller)) = .ok (.bool true) := by
    simpa only [decide_eq_true heq] using hcond
  rcases vaultDebitAllowance false hs0 hsize hmo rfl hcanon hbase ho hv hperm hstack rdAllowance with
    ⟨evm1, σ1, locals1, mem1, aw1, k1, C1, hallowance, hs1, hframe, hget, rdNext⟩ | ⟨hallowance, hrev⟩
  · exact Or.inl ⟨evm1, σ1, locals1, mem1, aw1, k1, C1,
      ExecStmt.iteTrue hcondTrue hallowance, hs1, hframe, hget, rdNext⟩
  · exact Or.inr ⟨ExecStmt.iteTrue hcondTrue hallowance, hrev⟩

end Benchmarks.CurveVault
