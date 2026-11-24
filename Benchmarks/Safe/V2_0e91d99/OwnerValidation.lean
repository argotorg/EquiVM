import Benchmarks.Safe.V2_0e91d99.Blocks.Runtime_029
import Benchmarks.Safe.V2_0e91d99.Blocks.Runtime_030
import Benchmarks.Safe.V2_0e91d99.Blocks.Runtime_037
import Benchmarks.Safe.V2_0e91d99.Blocks.Runtime_038
import Benchmarks.Safe.V2_0e91d99.DelegatedAccount
import Benchmarks.Safe.V2_0e91d99.Membership
import Benchmarks.Safe.V2_0e91d99.Authorization

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V2_0e91d99.RuntimeBlocks

namespace Benchmarks.Safe.V2_0e91d99

set_option maxRecDepth 100000

def validOwner (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) : Prop :=
  key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩ ∧
    (key ≠ UInt256.ofNat I.codeOwner.val ∨ delegatedAccount σ I)

instance (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) :
    Decidable (validOwner σ I key) := inferInstanceAs (Decidable
      (key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩ ∧
    (key ≠ UInt256.ofNat I.codeOwner.val ∨ delegatedAccount σ I)))

theorem safeEvalValidOwner (evm : EVM.State) (frame : Frame) (expr : Expr) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus)
    (heval : evalExpr? config frame evm expr =
      .ok (.address (AccountAddress.ofNat key.toNat))) :
    evalExpr? config frame evm (validOwnerExpr expr) =
      .ok (.bool (decide (validOwner evm.accountMap evm.executionEnv key))) := by
  have hz := evalAddressNonzero hcanon heval
  have hs : evalExpr? config frame evm (neE expr sentinelAddr) =
      .ok (.bool (decide (key ≠ ⟨1⟩))) := by
    have hone := canonicalAddress_eq_address_iff key (AccountAddress.ofNat 1) hcanon
    rw [neE, evalExpr_binary_nonshort (by decide) (by decide), heval]
    simp [sentinelAddr, addrSt, evalExpr?, castValue?, evalBinaryOpNeAddress,
      EvalResult.bind, EvalResult.ofOption, bind, pure]
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq] using hone
  have ht : evalExpr? config frame evm (neE expr this) =
      .ok (.bool (decide (key ≠ UInt256.ofNat evm.executionEnv.codeOwner.val))) := by
    have heq := canonicalAddress_eq_address_iff key evm.executionEnv.codeOwner hcanon
    rw [neE, evalExpr_binary_nonshort (by decide) (by decide), heval]
    simp [this, evalExpr?, envValue, evalBinaryOpNeAddress, EvalResult.bind, bind, pure]
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq] using heq
  rw [validOwnerExpr, andE, evalExpr?, hz]
  by_cases hz' : key = ⟨0⟩
  · simp [hz', validOwner, EvalResult.bind, bind, pure]
  · simp only [ne_eq, hz', not_false_eq_true, decide_true, EvalResult.bind, bind, pure]
    rw [andE, evalExpr?, hs]
    by_cases hs' : key = ⟨1⟩
    · simp [hs', validOwner, EvalResult.bind, bind, pure]
    · simp only [ne_eq, hs', not_false_eq_true, decide_true, EvalResult.bind, bind, pure]
      rw [orE, evalExpr?, ht]
      by_cases ht' : key = UInt256.ofNat evm.executionEnv.codeOwner.val
      · simp only [validOwner, ne_eq, hz', hs', not_false_eq_true, true_and]
        simp [ht', safeEvalDelegatedAccount, EvalResult.bind, bind, pure]
      · simp [ht', validOwner, hz', hs', EvalResult.bind, bind, pure]

-- The shared validator leaves its invalidity flag at the final conditional jump.
theorem safeOwnerValidationFlagTrace {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8700⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) :
    ∃ mem' aw' k' C', mem'.size = mem.size ∧
      (∀ off count, 3 ≤ off → off + count ≤ mem.size →
        mem'.readWithPadding off count = mem.readWithPadding off count) ∧
      RD fork safeBytecode I g s0 ⟨8766⟩
        ((if validOwner σ I key then ⟨0⟩ else ⟨1⟩) :: key :: R)
        mem' aw' rdata σ k' C' := by
  by_cases hz : key = ⟨0⟩
  · have h₁ := safeRuntime_block_8700_taken (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc, hz]; decide) (by jump_dest) h
    simp only [safeRuntime_block_8700_taken_stack, safeAddressMask,
      solcAddrMask_clean hc] at h₁
    have he : UInt256.isZero key = ⟨1⟩ := by rw [hz]; rfl
    rw [he] at h₁
    have h₂ := safeRuntime_block_8731_taken (by simp; omega) (by decide) (by jump_dest) h₁
    refine ⟨mem, aw, k + 12 + 4, C + 41 + 17, rfl, fun _ _ _ _ ↦ rfl, ?_⟩
    simpa only [validOwner, hz, ne_eq, not_true_eq_false, false_and, if_false] using h₂
  · have h₁ := safeRuntime_block_8700_fallthrough (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc]; exact isZero_eq_zero_of_ne hz) h
    have h₂ := safeRuntime_block_8717 (by simp; omega) h₁
    simp only [safeRuntime_block_8717_stack, safeAddressMask, solcAddrMask_clean hc] at h₂
    by_cases hs : key = ⟨1⟩
    · have he : UInt256.eq (UInt256.ofNat 1) key = ⟨1⟩ := by rw [hs]; rfl
      rw [he] at h₂
      have h₃ := safeRuntime_block_8731_taken (by simp; omega) (by decide) (by jump_dest) h₂
      refine ⟨mem, aw, k + 12 + 10 + 4, C + 41 + 29 + 17,
        rfl, fun _ _ _ _ ↦ rfl, ?_⟩
      simpa only [validOwner, hs, ne_eq, not_true_eq_false, false_and, and_false,
        if_false] using h₃
    · have he : UInt256.eq (UInt256.ofNat 1) key = ⟨0⟩ :=
        uInt256_eq_zero_of_ne (fun he ↦ hs (uInt256_eq_one_eq he).symm)
      rw [he] at h₂
      have h₃ := safeRuntime_block_8731_fallthrough (by simp; omega) rfl h₂
      by_cases ht : key = UInt256.ofNat I.codeOwner.val
      · have he : UInt256.eq (UInt256.ofNat I.codeOwner.val) key = ⟨1⟩ := by
          rw [ht, uInt256_eq_self]
        have h₄ := safeRuntime_block_8737_fallthrough (by simp; omega)
          (by rw [safeAddressMask, solcAddrMask_clean hc, he]; rfl) h₃
        have h₅ := safeRuntime_block_8756 (by simp; omega) (by jump_dest) h₄
        obtain ⟨aw₆, k₆, C₆, h₆⟩ := safeDelegatedAccountTrace h₅ (by simp; omega) hm
          (by jump_dest)
        have h₇ := safeRuntime_block_8764 (by simp; omega) h₆
        refine ⟨(externalCode σ (UInt256.ofNat I.codeOwner.val)).write 0 mem 0 3,
          aw₆, k₆ + 2, C₆ + 4, delegationCopy_size _ _ (by omega),
          fun off count hlo hin ↦ delegationCopy_read _ _ _ _ (by omega) hlo hin, ?_⟩
        simp only [validOwner, ne_eq, hz, hs, not_false_eq_true, true_and]
        by_cases hd : delegatedAccount σ I
        · simpa [safeRuntime_block_8764_stack, validOwner, hz, hs, ht, hd] using h₇
        · simpa [safeRuntime_block_8764_stack, validOwner, hz, hs, ht, hd] using h₇
      · have he : UInt256.eq (UInt256.ofNat I.codeOwner.val) key = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he ↦ ht (uInt256_eq_one_eq he).symm)
        have h₄ := safeRuntime_block_8737_taken (by simp; omega)
          (by rw [safeAddressMask, solcAddrMask_clean hc, he]; decide) (by jump_dest) h₃
        refine ⟨mem, aw, k + 12 + 10 + 4 + 14, C + 41 + 29 + 17 + 47,
          rfl, fun _ _ _ _ ↦ rfl, ?_⟩
        simpa [safeRuntime_block_8737_taken_stack, safeAddressMask, solcAddrMask_clean hc,
          he, validOwner, hz, hs, ht] using h₄

theorem safeValidOwnerTrace {I g s0 σ k C aw mem rdata} {key ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8700⟩ (key :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) (hv : validOwner σ I key)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ mem' aw' k' C', mem'.size = mem.size ∧
      (∀ off count, 3 ≤ off → off + count ≤ mem.size →
        mem'.readWithPadding off count = mem.readWithPadding off count) ∧
      RD fork safeBytecode I g s0 ret R mem' aw' rdata σ k' C' := by
  obtain ⟨mem', aw', _, _, hm', hr, h₁⟩ := safeOwnerValidationFlagTrace h
    (by simp; omega) hc hm
  simp only [hv, if_true] at h₁
  have h₂ := safeRuntime_block_8766_taken (by simp; omega) (by decide) (by jump_dest) h₁
  have h₃ := safeRuntime_block_6840 (by simp; omega) hret h₂
  exact ⟨mem', aw', _, _, hm', hr, h₃⟩

theorem safeInvalidOwnerTrace {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8700⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) (hv : ¬validOwner σ I key) : RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, _, _, _, _, h₁⟩ := safeOwnerValidationFlagTrace h hov hc hm
  simp only [hv, if_false] at h₁
  have h₂ := safeRuntime_block_8766_fallthrough (by simp; omega) (by decide) h₁
  simp only [safeRuntime_block_8766_fallthrough_stack] at h₂
  have h₃ := safeRuntime_block_8772 (by simp; omega) (by jump_dest) h₂
  exact safeRuntime_block_6898 (by simp; omega) h₃

end Benchmarks.Safe.V2_0e91d99
