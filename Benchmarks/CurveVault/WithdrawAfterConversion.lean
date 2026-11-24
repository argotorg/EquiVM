import Benchmarks.CurveVault.DebitAllowance
import Benchmarks.CurveVault.DebitBurn

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultWithdrawAfterConversion {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver owner shares : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 736 ≤ mem.size)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (ho : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hbc : locals.get? "_controller" = none) (hb : locals.get? "_borrowed_token" = none)
    (hallow : locals.get? "allowance" = none)
    (ha : locals.get? "_assets" = some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
    (hv : locals.get? "shares" = some (.int (Int.ofNat shares.toNat)))
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmo : memLoad (UInt256.ofNat 608) mem = owner)
    (hmv : memLoad (UInt256.ofNat 704) mem = shares)
    (hrcanon : receiver.toNat < EVM.addressModulus) (hocanon : owner.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hstack : R.length + 9 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 4412) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store),
      ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction true).body.drop 3)
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat shares.toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) shares.toByteArray) ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction true).body.drop 3)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let prepared := shares.toByteArray.write 0 mem 672 32
  have hgap : 672 - mem.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 672 (by omega))
  have hframe0 : WordMemoryRange mem prepared 192 672 :=
    wordMemoryRange_write _ _ 672 192 672 hgap (Or.inl (by omega))
  have hsize0 : 704 ≤ prepared.size := toByteArray_write_size_ge_off_add32 _ _ 672 hgap
  have ho0 : memLoad (UInt256.ofNat 608) prepared = owner :=
    (hframe0.load 608 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmo
  have hv0 : memLoad (UInt256.ofNat 672) prepared = shares :=
    memLoad_write_back _ _ 672 (by decide +kernel) hgap
  have hcond := evalExpr_ne_address_word hocanon
    (show evalExpr? config {contract := contract, locals := locals} evm (.var "_owner") =
      .ok (.address (AccountAddress.ofNat owner.toNat)) by rw [evalExpr?]; simp only [ho, EvalResult.ofOption])
    (show evalExpr? config {contract := contract, locals := locals} evm (.env .caller) =
      .ok (.address I.source) by simp only [evalExpr?, envValue, hs.env, pure])
  have hprefix :
      (∃ (evm1 : State) (σ1 : AccountMap) (locals1 : Store) (mem1 : ByteArray) (aw1 : UInt256) (k1 C1 : Nat),
        ExecStmt fork config {contract := contract, locals := locals} evm ((vaultDebitFunction true).body[3]!)
          (.ok {contract := contract, locals := locals1} evm1) ∧
        SourceState s0 I σ1 evm1 ∧ WordMemoryRange prepared mem1 192 704 ∧
        (∀ name, ("allowance_" == name) = false → ("__c2" == name) = false →
          locals1.get? name = locals.get? name) ∧
        RD fork vaultBytecode I g s0 (UInt256.ofNat 4549) R mem1 aw1 rdata σ1 k1 C1) ∨
      (ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction true).body.drop 3)
        .reverted ∧ RDrev fork vaultBytecode g s0) := by
    by_cases heq : owner = UInt256.ofNat I.source.val
    · obtain ⟨aw0, k0, C0, rdBurn⟩ := vaultBlocks.vault_block_4412_taken_packed (by omega)
        (by
          change UInt256.eq (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem 672 32)) _ ≠ _
          rw [hmv, ho0, heq, u256_eq_refl]; decide +kernel) (by native_decide) h
      change RD fork vaultBytecode I g s0 (UInt256.ofNat 4549) R
        ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem 672 32) aw0 rdata σ k0 C0 at rdBurn
      rw [hmv] at rdBurn
      exact Or.inl ⟨evm, σ, locals, prepared, aw0, k0, C0,
        ExecStmt.iteFalse (by simpa only [heq, ne_eq, not_true_eq_false, decide_false] using hcond) ExecBlock.nil,
        hs, WordMemoryRange.refl _ _ _, fun _ _ _ => rfl, rdBurn⟩
    obtain ⟨aw0, k0, C0, rdAllowance⟩ := vaultBlocks.vault_block_4412_fallthrough_packed (by omega)
      (by
        change UInt256.eq (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem 672 32)) _ = _
        rw [hmv, ho0]; exact u256_eq_of_ne heq) h
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 4431) R
      ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem 672 32) aw0 rdata σ k0 C0 at rdAllowance
    rw [hmv] at rdAllowance
    have hcondTrue : evalExpr? config {contract := contract, locals := locals} evm
        (.binary .ne (.var "_owner") (.env .caller)) = .ok (.bool true) := by
      simpa only [decide_eq_true heq] using hcond
    rcases vaultDebitAllowance true hs hsize0 ho0 hv0 hocanon hallow ho hv hperm (by omega) rdAllowance with
      ⟨evm1, σ1, locals1, mem1, aw1, k1, C1, hallowance, hs1, hframe, hget, rdBurn⟩ | ⟨hallowance, hrev⟩
    · exact Or.inl ⟨evm1, σ1, locals1, mem1, aw1, k1, C1,
        ExecStmt.iteTrue hcondTrue hallowance, hs1, hframe, hget, rdBurn⟩
    · exact Or.inr ⟨ExecBlock.consRevert (ExecStmt.iteTrue hcondTrue hallowance), hrev⟩
  rcases hprefix with ⟨evm1, σ1, locals1, mem1, aw1, k1, C1, hbranch, hs1, hframe1, hget, rdBurn⟩ | hrev
  swap
  · exact Or.inr hrev
  have hframe := hframe0.trans (hframe1.mono (le_refl _) (by omega))
  rcases vaultDebitBurn true (locals := locals1) hs1 (le_trans hsize0 hframe1.size)
    ((hget "_receiver" (by decide +kernel) (by decide +kernel)).trans hr)
    ((hget "_owner" (by decide +kernel) (by decide +kernel)).trans ho)
    ((hget "_controller" (by decide +kernel) (by decide +kernel)).trans hbc)
    ((hget "_borrowed_token" (by decide +kernel) (by decide +kernel)).trans hb)
    ((hget "_assets" (by decide +kernel) (by decide +kernel)).trans ha)
    ((hget "shares" (by decide +kernel) (by decide +kernel)).trans hv)
    ((hframe.load 576 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmr)
    ((hframe.load 608 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmo)
    ((hframe1.load 672 (by omega) (by omega) hsize0 (by decide +kernel)).trans hv0)
    rfl hrcanon hocanon hperm hstack rdBurn with
    ⟨evm2, σ2, locals2, hburn, hs2, hret⟩ | ⟨hburn, hrev⟩
  · exact Or.inl ⟨evm2, σ2, locals2, ExecBlock.consNormal hbranch hburn, hs2, hret⟩
  · exact Or.inr ⟨ExecBlock.consNormal hbranch hburn, hrev⟩

end Benchmarks.CurveVault
