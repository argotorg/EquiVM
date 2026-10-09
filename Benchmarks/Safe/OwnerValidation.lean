import Benchmarks.Safe.DelegatedAccount
import Benchmarks.Safe.Membership
import Benchmarks.Safe.Authorization
import Benchmarks.Safe.Blocks.Runtime_037

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

def validOwner (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) : Prop :=
  key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩ ∧ (key ≠ UInt256.ofNat I.codeOwner.val ∨ delegatedAccount σ I)

instance (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) :
    Decidable (validOwner σ I key) := inferInstanceAs (Decidable
      (key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩ ∧ (key ≠ UInt256.ofNat I.codeOwner.val ∨ delegatedAccount σ I)))

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
    rw [neE, evalExpr_binary_nonshort (by decide) (by decide), heval]
    simp [this, evalExpr?, envValue, evalBinaryOpNeAddress,
      EvalResult.bind, EvalResult.ofOption, bind, pure]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq,
      canonicalAddress_eq_address_iff key _ hcanon]
  have hor : evalExpr? config frame evm (orE (neE expr this) isThisDelegatedAccountExpr) =
      .ok (.bool (decide (key ≠ UInt256.ofNat evm.executionEnv.codeOwner.val ∨
        delegatedAccount evm.accountMap evm.executionEnv))) := by
    rw [orE, evalExpr?, ht]
    by_cases ht' : key = UInt256.ofNat evm.executionEnv.codeOwner.val <;>
      simp [ht', safeEvalDelegatedAccount, EvalResult.bind, bind, pure]
  rw [validOwnerExpr, andE, evalExpr?, hz]
  by_cases hz' : key = ⟨0⟩
  · simp [hz', validOwner, EvalResult.bind, bind, pure]
  · simp only [show key ≠ ⟨0⟩ from hz', decide_true, EvalResult.bind, bind, pure]
    rw [andE, evalExpr?, hs]
    by_cases hs' : key = ⟨1⟩ <;>
      simp [hs', hz', validOwner, hor, EvalResult.bind, bind, pure, UInt256.size]

theorem safeOwnerValidationReach {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8589⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hz : key ≠ ⟨0⟩) (hs : key ≠ ⟨1⟩) :
    ∃ k' C', RD safeBytecode I g s0 ⟨8626⟩ (⟨0⟩ :: key :: R) mem aw rdata σ k' C' := by
  have hc : UInt256.land key
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = key := by rw [safeAddressMask, solcAddrMask_clean hcanon]
  have he : UInt256.eq (UInt256.ofNat 1) key = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he ↦ hs (uInt256_eq_one_eq he).symm)
  have h₁ := safeRuntime_block_8589_fallthrough hov (by rw [hc]; exact isZero_eq_zero_of_ne hz) h
  have h₂ := safeRuntime_block_8606 hov h₁
  simp only [safeRuntime_block_8606_stack, hc, he] at h₂
  exact ⟨_, _, safeRuntime_block_8620_fallthrough (by simp; omega) rfl h₂⟩

theorem safeOwnerValidationReject {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8655⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_8655_fallthrough (by omega) (by decide) h
  have h₂ := safeRuntime_block_8661
    (by simp only [safeRuntime_block_8655_fallthrough_stack]; omega) (by jump_dest) h₁
  exact safeRuntime_block_6898
    (by simp only [safeRuntime_block_8655_fallthrough_stack, List.length_cons]; omega) h₂

theorem safeOwnerValidationReturn {I g s0 σ k C aw mem rdata} {key ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8655⟩ (⟨0⟩ :: key :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret R mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_8655_taken (by simp; omega) (by decide) (by jump_dest) h
  exact ⟨_, _, safeRuntime_block_6840 (by omega) hret h₁⟩

theorem safeValidOwnerHeapTrace {I g s0 σ k C aw mem rdata} {key ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8589⟩ (key :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hmem : 96 ≤ mem.size) (hv : validOwner σ I key)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ mem' aw' k' C', mem'.size = mem.size ∧
      (∀ off count, 64 ≤ off → off + count ≤ mem.size →
        mem'.readWithPadding off count = mem.readWithPadding off count) ∧
      RD safeBytecode I g s0 ret R mem' aw' rdata σ k' C' := by
  obtain ⟨k₁, C₁, h₁⟩ := safeOwnerValidationReach h (by simp; omega) hcanon hv.1 hv.2.1
  have hc : UInt256.land key
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = key := by rw [safeAddressMask, solcAddrMask_clean hcanon]
  by_cases ht : key = UInt256.ofNat I.codeOwner.val
  · have hd : delegatedAccount σ I := hv.2.2.resolve_left (fun hn ↦ hn ht)
    have h₂ := safeRuntime_block_8626_fallthrough (by simp; omega)
      (by rw [hc, ht, uInt256_eq_self]; rfl) h₁
    have h₃ := safeRuntime_block_8645 (by simp; omega) (by jump_dest) h₂
    obtain ⟨aw₄, k₄, C₄, h₄⟩ := safeDelegatedAccountTrace h₃ (by simp; omega)
      (by omega) (by jump_dest)
    simp only [hd, decide_true] at h₄
    have h₅ := safeRuntime_block_8653 (by simp; omega) h₄
    change RD safeBytecode I g s0 ⟨8655⟩ (⟨0⟩ :: key :: ret :: R)
      ((thisCode σ I).write 0 mem 0 3) aw₄ rdata σ _ _ at h₅
    obtain ⟨k', C', h'⟩ := safeOwnerValidationReturn h₅ (by omega) hret
    exact ⟨_, _, k', C', writePrefix3_size _ _ (by omega),
      fun off count hlo hin ↦ writePrefix3ReadAbove _ _ off count (by omega) hin (by omega),
      h'⟩
  · have he : UInt256.eq (UInt256.ofNat I.codeOwner.val) key = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun he ↦ ht (uInt256_eq_one_eq he).symm)
    have h₂ := safeRuntime_block_8626_taken (by simp; omega)
      (by rw [hc, he]; decide) (by jump_dest) h₁
    simp only [safeRuntime_block_8626_taken_stack, hc, he] at h₂
    obtain ⟨k', C', h'⟩ := safeOwnerValidationReturn h₂ (by omega) hret
    exact ⟨mem, aw, k', C', rfl, fun _ _ _ _ ↦ rfl, h'⟩

theorem safeValidOwnerTrace {I g s0 σ k C aw mem rdata} {key ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8589⟩ (key :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hmem : mem.size = 96) (hv : validOwner σ I key)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ mem' aw' k' C', mem'.size = 96 ∧
      mem'.readWithPadding 64 32 = mem.readWithPadding 64 32 ∧
      RD safeBytecode I g s0 ret R mem' aw' rdata σ k' C' := by
  obtain ⟨mem', aw', k', C', hm', hr, h'⟩ := safeValidOwnerHeapTrace h hov hcanon
    (by omega) hv hret
  exact ⟨mem', aw', k', C', hm'.trans hmem, hr 64 32 (by omega) (by omega), h'⟩

theorem safeInvalidOwnerTrace {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8589⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hmem : 32 ≤ mem.size) (hv : ¬validOwner σ I key) :
    RDrev safeBytecode g s0 := by
  have hc : UInt256.land key
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = key := by rw [safeAddressMask, solcAddrMask_clean hcanon]
  by_cases hz : key = ⟨0⟩
  · have h₁ := safeRuntime_block_8589_taken (by omega)
      (by rw [hc, hz]; decide) (by jump_dest) h
    simp only [safeRuntime_block_8589_taken_stack, hc, hz,
      show UInt256.isZero ⟨0⟩ = ⟨1⟩ from rfl] at h₁
    have h₂ := safeRuntime_block_8620_taken (by simp; omega) (by decide) (by jump_dest) h₁
    exact safeOwnerValidationReject h₂ (by simp; omega)
  · have h₁ := safeRuntime_block_8589_fallthrough (by omega)
      (by rw [hc]; exact isZero_eq_zero_of_ne hz) h
    have h₂ := safeRuntime_block_8606 (by omega) h₁
    by_cases hs : key = ⟨1⟩
    · simp only [safeRuntime_block_8606_stack, hc, hs, uInt256_eq_self] at h₂
      have h₃ := safeRuntime_block_8620_taken (by simp; omega) (by decide) (by jump_dest) h₂
      exact safeOwnerValidationReject h₃ (by simp; omega)
    · have ht : key = UInt256.ofNat I.codeOwner.val := by
        by_contra hn
        exact hv ⟨hz, hs, Or.inl hn⟩
      have hd : ¬delegatedAccount σ I := fun hd ↦ hv ⟨hz, hs, Or.inr hd⟩
      have he : UInt256.eq (UInt256.ofNat 1) key = ⟨0⟩ :=
        uInt256_eq_zero_of_ne (fun he ↦ hs (uInt256_eq_one_eq he).symm)
      simp only [safeRuntime_block_8606_stack, hc, he] at h₂
      have h₃ := safeRuntime_block_8620_fallthrough (by simp; omega) rfl h₂
      have h₄ := safeRuntime_block_8626_fallthrough (by omega)
        (by rw [hc, ht, uInt256_eq_self]; rfl) h₃
      have h₅ := safeRuntime_block_8645 (by simp; omega) (by jump_dest) h₄
      obtain ⟨aw₆, k₆, C₆, h₆⟩ := safeDelegatedAccountTrace h₅ (by simp; omega)
        hmem (by jump_dest)
      simp only [hd, decide_false] at h₆
      have h₇ := safeRuntime_block_8653 (by simp; omega) h₆
      exact safeOwnerValidationReject h₇ (by simp; omega)

end Benchmarks.Safe
