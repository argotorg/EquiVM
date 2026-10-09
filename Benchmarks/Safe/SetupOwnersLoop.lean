import Benchmarks.Safe.SetupOwnersIteration

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeSetupOwnersLoop (fuel : Nat) (p : SetupOwnersInput) (evm : EVM.State)
    {locals i current ptr I g s0 k C aw mem rdata} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8057⟩
      (UInt256.ofNat i :: UInt256.ofNat p.owners.length :: current :: p.threshold ::
        UInt256.ofNat ptr :: ret :: R) mem aw rdata evm.accountMap k C)
    (hl : SetupOwnersLocals p locals i current) (hn : i + fuel = p.owners.length)
    (hee : evm.executionEnv = I) (hm : WordArrayBuffer mem ptr p.owners) (hp : 96 ≤ ptr)
    (hb : ptr + 32 + 32 * p.owners.length < UInt256.size)
    (hc : current.toNat < EVM.addressModulus)
    (ho : ∀ j (hj : j < p.owners.length), p.owners[j].toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hov : R.length + 20 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧
      ExecStmt config { contract := contract, locals := locals } evm
        (.while setupOwnersLoopCondition setupOwnersLoopBody) .reverted) ∨
    ∃ locals' evm' current' mem' aw' k' C',
      ExecStmt config { contract := contract, locals := locals } evm
        (.while setupOwnersLoopCondition setupOwnersLoopBody)
        (.ok { contract := contract, locals := locals' } evm') ∧
      SetupOwnersLocals p locals' p.owners.length current' ∧
      current'.toNat < EVM.addressModulus ∧ evm'.executionEnv = I ∧ evm'.σ₀ = evm.σ₀ ∧
      RD safeBytecode I g s0 ⟨8199⟩
        (UInt256.ofNat p.owners.length :: UInt256.ofNat p.owners.length :: current' ::
          p.threshold :: UInt256.ofNat ptr :: ret :: R) mem' aw' rdata evm'.accountMap k' C' ∧
      mem'.size = mem.size ∧
      (∀ off count, 64 ≤ off → off + count ≤ mem.size →
        mem'.readWithPadding off count = mem.readWithPadding off count) := by
  induction fuel generalizing i locals current evm k C mem aw with
  | zero =>
      have hi : i = p.owners.length := by omega
      have hg : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat p.owners.length) = ⟨0⟩ := by
        rw [hi]
        exact ult_zero (by omega)
      have h₁ := safeRuntime_block_8057_taken (by simp; omega)
        (by rw [hg]; decide) (by jump_dest) h
      rw [hi] at h₁ hl
      refine .inr ⟨locals, evm, current, mem, aw, _, _, .whileFalse ?_, hl, hc, hee, rfl,
        h₁, rfl, fun _ _ _ _ ↦ rfl⟩
      simpa only [lt_self_iff_false, decide_false] using safeSetupOwnersCondition evm hl
  | succ fuel ih =>
      have hi : i < p.owners.length := by omega
      have hib : i < UInt256.size := by omega
      have hnb : p.owners.length < UInt256.size := by omega
      have hg : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat p.owners.length) = ⟨1⟩ :=
        ult_one (by rwa [ulit_toNat' i hib, ulit_toNat' _ hnb])
      have hcond : evalExpr? config { contract := contract, locals := locals } evm
          setupOwnersLoopCondition = .ok (.bool true) := by
        simpa only [hi, decide_true] using safeSetupOwnersCondition evm hl
      have h₁ := safeRuntime_block_8057_fallthrough (by simp; omega) (by rw [hg]; rfl) h
      obtain ⟨hrev, hbody⟩ | ⟨mem₂, aw₂, k₂, C₂, hbody, h₂, hsize₂, hr₂⟩ :=
        safeSetupOwnersIteration evm h₁ hl hi hee rfl hm hp hb hc (ho i hi) hperm hov
      · exact .inl ⟨hrev, .whileRevert hcond hbody⟩
      have hm₂ : WordArrayBuffer mem₂ ptr p.owners := hm.preserved (by omega)
        (fun off count hlo hin ↦ hr₂ off count (by omega) (hin.trans hm.size))
      have hee₂ : (writeOwnerLink evm current p.owners[i]).executionEnv = I := by
        simpa only [writeOwnerLink, storageStore_executionEnv] using hee
      obtain ⟨hrev, htail⟩ | ⟨locals', evm', current', mem', aw', k', C', htail, hl', hc',
          hee', hw', h₃, hsize', hr'⟩ :=
        ih (writeOwnerLink evm current p.owners[i]) h₂ (hl.next p.owners[i]) (by omega)
          hee₂ hm₂ (ho i hi)
      · exact .inl ⟨hrev, .whileTrue hcond hbody htail⟩
      refine .inr ⟨locals', evm', current', mem', aw', k', C',
        .whileTrue hcond hbody htail, hl', hc', hee', ?_, h₃, hsize'.trans hsize₂, ?_⟩
      · simpa only [writeOwnerLink, storageStore_σ₀] using hw'
      · intro off count hlo hin
        rw [hr' off count hlo (by omega), hr₂ off count hlo hin]

end Benchmarks.Safe
