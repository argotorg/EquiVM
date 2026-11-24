import Benchmarks.Safe.ViaIR.DelegatedAccount
import Benchmarks.Safe.ViaIR.Membership
import Benchmarks.Safe.ViaIR.Authorization
import Benchmarks.Safe.ViaIR.Blocks.Runtime_049

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

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
    (h : RD fork safeBytecode I g s0 ⟨10862⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hz : key ≠ ⟨0⟩) (hs : key ≠ ⟨1⟩) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨10940⟩ (key :: ⟨0⟩ :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_10862_taken hov
    (by
      rw [safeAddressMask, solcAddrMask_clean_left hcanon, isZero_eq_zero_of_ne hz]
      decide) (by jump_dest) h
  simp only [safeRuntime_block_10862_taken_stack, safeAddressMask,
    solcAddrMask_clean_left hcanon] at h₁
  have h₂ := safeRuntime_block_10979 hov (by jump_dest) h₁
  have he : UInt256.eq key (UInt256.ofNat 1) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he ↦ hs (uInt256_eq_one_eq he))
  simp only [safeRuntime_block_10979_stack, he] at h₂
  exact ⟨_, _, safeRuntime_block_10881_taken hov (by decide) (by jump_dest) h₂⟩

theorem safeOwnerValidationReject {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10888⟩ (key :: ⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_10888_taken (by omega) (by decide) (by jump_dest) h
  exact safeRuntime_block_10895 (by simp [safeRuntime_block_10888_taken_stack]; omega) h₁

theorem safeOwnerValidationReturn {I g s0 σ k C aw mem rdata} {key ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10888⟩ (key :: ⟨0⟩ :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret R mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_10888_fallthrough (by simp; omega) rfl h
  exact ⟨_, _, safeRuntime_block_10894 (by omega) hret h₁⟩

theorem safeValidOwnerHeapTrace {I g s0 σ k C aw mem rdata} {key ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10862⟩ (key :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hmem : 96 ≤ mem.size) (hv : validOwner σ I key)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ mem' aw' k' C', mem'.size = mem.size ∧
      (∀ off count, 64 ≤ off → off + count ≤ mem.size →
        mem'.readWithPadding off count = mem.readWithPadding off count) ∧
      RD fork safeBytecode I g s0 ret R mem' aw' rdata σ k' C' := by
  obtain ⟨k₁, C₁, h₁⟩ := safeOwnerValidationReach h (by simp; omega) hcanon hv.1 hv.2.1
  by_cases ht : key = UInt256.ofNat I.codeOwner.val
  · have hd : delegatedAccount σ I := hv.2.2.resolve_left (fun hn ↦ hn ht)
    have h₂ := safeRuntime_block_10940_taken (by simp; omega)
      (by rw [ht, uInt256_eq_self]; decide) (by jump_dest) h₁
    obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeDelegatedAccountTrace h₂ (by simp; omega) (by omega)
    simp only [hd, decide_true] at h₃
    have h₄ := safeRuntime_block_10950 (by simp; omega) (by jump_dest) h₃
    change RD fork safeBytecode I g s0 ⟨10888⟩ (⟨0⟩ :: ⟨0⟩ :: ret :: R)
      ((thisCode σ I).write 0 mem 0 3) aw₃ rdata σ _ _ at h₄
    obtain ⟨k', C', h'⟩ := safeOwnerValidationReturn h₄ (by omega) hret
    exact ⟨_, _, k', C', writePrefix3_size _ _ (by omega),
      fun off count hlo hin ↦ writePrefix3ReadAbove _ _ off count (by omega) hin (by omega),
      h'⟩
  · have he : UInt256.eq (UInt256.ofNat I.codeOwner.val) key = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun he ↦ ht (uInt256_eq_one_eq he).symm)
    have h₂ := safeRuntime_block_10940_fallthrough (by simp; omega) he h₁
    simp only [safeRuntime_block_10940_fallthrough_stack, he] at h₂
    have h₃ := safeRuntime_block_10950 (by simp; omega) (by jump_dest) h₂
    obtain ⟨k', C', h'⟩ := safeOwnerValidationReturn h₃ (by omega) hret
    exact ⟨mem, aw, k', C', rfl, fun _ _ _ _ ↦ rfl, h'⟩

theorem safeValidOwnerTrace {I g s0 σ k C aw mem rdata} {key ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10862⟩ (key :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hmem : mem.size = 96) (hv : validOwner σ I key)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ mem' aw' k' C', mem'.size = 96 ∧
      mem'.readWithPadding 64 32 = mem.readWithPadding 64 32 ∧
      RD fork safeBytecode I g s0 ret R mem' aw' rdata σ k' C' := by
  obtain ⟨mem', aw', k', C', hm', hr, h'⟩ := safeValidOwnerHeapTrace h hov hcanon
    (by omega) hv hret
  exact ⟨mem', aw', k', C', hm'.trans hmem, hr 64 32 (by omega) (by omega), h'⟩

theorem safeInvalidOwnerTrace {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10862⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hmem : 32 ≤ mem.size) (hv : ¬validOwner σ I key) :
    RDrev fork safeBytecode g s0 := by
  by_cases hz : key = ⟨0⟩
  · have h₁ := safeRuntime_block_10862_fallthrough (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean_left hcanon, hz]; decide) h
    simp only [safeRuntime_block_10862_fallthrough_stack, safeAddressMask,
      solcAddrMask_clean_left hcanon, hz] at h₁
    have h₂ := safeRuntime_block_10881_fallthrough (by omega) (by decide) h₁
    exact safeOwnerValidationReject h₂ (by omega)
  · by_cases hs : key = ⟨1⟩
    · have h₁ := safeRuntime_block_10862_taken (by omega)
        (by rw [safeAddressMask, solcAddrMask_clean_left hcanon, hs]; decide) (by jump_dest) h
      simp only [safeRuntime_block_10862_taken_stack, safeAddressMask,
        solcAddrMask_clean_left hcanon] at h₁
      have h₂ := safeRuntime_block_10979 (by omega) (by jump_dest) h₁
      simp only [safeRuntime_block_10979_stack, hs] at h₂
      have h₃ := safeRuntime_block_10881_fallthrough (by omega) (by decide) h₂
      exact safeOwnerValidationReject h₃ (by omega)
    · have ht : key = UInt256.ofNat I.codeOwner.val := by
        by_contra hn
        exact hv ⟨hz, hs, Or.inl hn⟩
      have hd : ¬delegatedAccount σ I := fun hd ↦ hv ⟨hz, hs, Or.inr hd⟩
      obtain ⟨_, _, h₁⟩ := safeOwnerValidationReach h (by omega) hcanon hz hs
      have h₂ := safeRuntime_block_10940_taken (by omega)
        (by rw [ht, uInt256_eq_self]; decide) (by jump_dest) h₁
      obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeDelegatedAccountTrace h₂ (by omega) hmem
      simp only [hd, decide_false] at h₃
      have h₄ := safeRuntime_block_10950 (by simp; omega) (by jump_dest) h₃
      exact safeOwnerValidationReject h₄ (by omega)

end Benchmarks.Safe.ViaIR
