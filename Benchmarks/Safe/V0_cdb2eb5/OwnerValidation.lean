import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_028
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_029
import Benchmarks.Safe.V0_cdb2eb5.Membership
import Benchmarks.Safe.V0_cdb2eb5.Authorization
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_013
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_014
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_027
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_030
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

set_option maxRecDepth 100000

def validOwner (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) : Prop :=
  key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩

instance (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) :
    Decidable (validOwner σ I key) := inferInstanceAs (Decidable
      (key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩))

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
  rw [validOwnerExpr, andE, evalExpr?, hz]
  by_cases hz' : key = ⟨0⟩
  · simp [hz', validOwner, EvalResult.bind, bind, pure]
  · simp only [show key ≠ ⟨0⟩ from hz', decide_true, EvalResult.bind, bind, pure]
    simp [hs, hz', validOwner]

-- The owner validity check is inlined into this entrypoint.
theorem safeValidOwnerTrace {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1744⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hv : validOwner σ I key) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨1797⟩ (top :: key :: R) mem aw rdata σ k' C' := by
  have hz := isZero_eq_zero_of_ne hv.1
  have hs : UInt256.eq (UInt256.ofNat 1) key = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he ↦ hv.2 (uInt256_eq_one_eq he).symm)
  have h₁ := safeRuntime_block_1744_fallthrough (by omega)
    (by rw [safeAddressMask, solcAddrMask_clean hc]; exact hz) h
  have h₂ := safeRuntime_block_1761 (by simp; omega) h₁
  simp only [safeRuntime_block_1761_stack, safeAddressMask, solcAddrMask_clean hc, hs] at h₂
  have h₃ := safeRuntime_block_1775_taken (by simp; omega) (by decide) (by jump_dest) h₂
  exact ⟨_, _, h₃⟩

theorem safeInvalidOwnerTrace {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1744⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hv : ¬validOwner σ I key) : RDrev fork safeBytecode g s0 := by
  have hbad : ∃ k' C', RD fork safeBytecode I g s0 ⟨1775⟩
      (⟨1⟩ :: top :: key :: R) mem aw rdata σ k' C' := by
    by_cases hz : key = ⟨0⟩
    · have h₁ := safeRuntime_block_1744_taken (by omega)
        (by rw [safeAddressMask, solcAddrMask_clean hc, hz]; decide) (by jump_dest) h
      simpa only [safeRuntime_block_1744_taken_stack, safeAddressMask,
        solcAddrMask_clean hc, hz] using (show ∃ k' C', _ from ⟨_, _, h₁⟩)
    · have hs : key = ⟨1⟩ := by
        by_contra hs
        exact hv ⟨hz, hs⟩
      have h₁ := safeRuntime_block_1744_fallthrough (by omega)
        (by rw [safeAddressMask, solcAddrMask_clean hc]; exact isZero_eq_zero_of_ne hz) h
      have h₂ := safeRuntime_block_1761 (by simp; omega) h₁
      simpa only [safeRuntime_block_1761_stack, safeAddressMask,
        solcAddrMask_clean hc, hs, uInt256_eq_self] using
        (show ∃ k' C', _ from ⟨_, _, h₂⟩)
  obtain ⟨_, _, h₁⟩ := hbad
  have h₂ := safeRuntime_block_1775_fallthrough (by simp; omega) (by decide) h₁
  simp only [safeRuntime_block_1775_fallthrough_stack] at h₂
  have h₃ := safeRuntime_block_1781 (by simp; omega) (by jump_dest) h₂
  exact safeRuntime_block_6990 (by simp; omega) h₃

-- The owner validity check is inlined into this entrypoint.
theorem safeValidRemoveOwnerTrace {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6729⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hv : validOwner σ I key) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨6782⟩ (top :: key :: R) mem aw rdata σ k' C' := by
  have hz := isZero_eq_zero_of_ne hv.1
  have hs : UInt256.eq (UInt256.ofNat 1) key = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he ↦ hv.2 (uInt256_eq_one_eq he).symm)
  have h₁ := safeRuntime_block_6729_fallthrough (by omega)
    (by rw [safeAddressMask, solcAddrMask_clean hc]; exact hz) h
  have h₂ := safeRuntime_block_6746 (by simp; omega) h₁
  simp only [safeRuntime_block_6746_stack, safeAddressMask, solcAddrMask_clean hc, hs] at h₂
  have h₃ := safeRuntime_block_6760_taken (by simp; omega) (by decide) (by jump_dest) h₂
  exact ⟨_, _, h₃⟩

theorem safeInvalidRemoveOwnerTrace {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6729⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hv : ¬validOwner σ I key) : RDrev fork safeBytecode g s0 := by
  have hbad : ∃ k' C', RD fork safeBytecode I g s0 ⟨6760⟩
      (⟨1⟩ :: top :: key :: R) mem aw rdata σ k' C' := by
    by_cases hz : key = ⟨0⟩
    · have h₁ := safeRuntime_block_6729_taken (by omega)
        (by rw [safeAddressMask, solcAddrMask_clean hc, hz]; decide) (by jump_dest) h
      simpa only [safeRuntime_block_6729_taken_stack, safeAddressMask,
        solcAddrMask_clean hc, hz] using (show ∃ k' C', _ from ⟨_, _, h₁⟩)
    · have hs : key = ⟨1⟩ := by
        by_contra hs
        exact hv ⟨hz, hs⟩
      have h₁ := safeRuntime_block_6729_fallthrough (by omega)
        (by rw [safeAddressMask, solcAddrMask_clean hc]; exact isZero_eq_zero_of_ne hz) h
      have h₂ := safeRuntime_block_6746 (by simp; omega) h₁
      simpa only [safeRuntime_block_6746_stack, safeAddressMask,
        solcAddrMask_clean hc, hs, uInt256_eq_self] using
        (show ∃ k' C', _ from ⟨_, _, h₂⟩)
  obtain ⟨_, _, h₁⟩ := hbad
  have h₂ := safeRuntime_block_6760_fallthrough (by simp; omega) (by decide) h₁
  simp only [safeRuntime_block_6760_fallthrough_stack] at h₂
  have h₃ := safeRuntime_block_6766 (by simp; omega) (by jump_dest) h₂
  exact safeRuntime_block_6990 (by simp; omega) h₃

-- The owner validity check is inlined into this entrypoint.
theorem safeValidSwapOldOwnerTrace {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6282⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hv : validOwner σ I key) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨6335⟩ (top :: key :: R) mem aw rdata σ k' C' := by
  have hz := isZero_eq_zero_of_ne hv.1
  have hs : UInt256.eq (UInt256.ofNat 1) key = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he ↦ hv.2 (uInt256_eq_one_eq he).symm)
  have h₁ := safeRuntime_block_6282_fallthrough (by omega)
    (by rw [safeAddressMask, solcAddrMask_clean hc]; exact hz) h
  have h₂ := safeRuntime_block_6299 (by simp; omega) h₁
  simp only [safeRuntime_block_6299_stack, safeAddressMask, solcAddrMask_clean hc, hs] at h₂
  have h₃ := safeRuntime_block_6313_taken (by simp; omega) (by decide) (by jump_dest) h₂
  exact ⟨_, _, h₃⟩

theorem safeInvalidSwapOldOwnerTrace {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6282⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hv : ¬validOwner σ I key) : RDrev fork safeBytecode g s0 := by
  have hbad : ∃ k' C', RD fork safeBytecode I g s0 ⟨6313⟩
      (⟨1⟩ :: top :: key :: R) mem aw rdata σ k' C' := by
    by_cases hz : key = ⟨0⟩
    · have h₁ := safeRuntime_block_6282_taken (by omega)
        (by rw [safeAddressMask, solcAddrMask_clean hc, hz]; decide) (by jump_dest) h
      simpa only [safeRuntime_block_6282_taken_stack, safeAddressMask,
        solcAddrMask_clean hc, hz] using (show ∃ k' C', _ from ⟨_, _, h₁⟩)
    · have hs : key = ⟨1⟩ := by
        by_contra hs
        exact hv ⟨hz, hs⟩
      have h₁ := safeRuntime_block_6282_fallthrough (by omega)
        (by rw [safeAddressMask, solcAddrMask_clean hc]; exact isZero_eq_zero_of_ne hz) h
      have h₂ := safeRuntime_block_6299 (by simp; omega) h₁
      simpa only [safeRuntime_block_6299_stack, safeAddressMask,
        solcAddrMask_clean hc, hs, uInt256_eq_self] using
        (show ∃ k' C', _ from ⟨_, _, h₂⟩)
  obtain ⟨_, _, h₁⟩ := hbad
  have h₂ := safeRuntime_block_6313_fallthrough (by simp; omega) (by decide) h₁
  simp only [safeRuntime_block_6313_fallthrough_stack] at h₂
  have h₃ := safeRuntime_block_6319 (by simp; omega) (by jump_dest) h₂
  exact safeRuntime_block_6990 (by simp; omega) h₃

theorem safeValidSwapNewOwnerTrace {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6162⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hv : validOwner σ I key) (hself : key ≠ UInt256.ofNat I.codeOwner.val) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨6234⟩ (key :: R) mem aw rdata σ k' C' := by
  have hs : UInt256.eq (UInt256.ofNat 1) key = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he ↦ hv.2 (uInt256_eq_one_eq he).symm)
  have ht : UInt256.eq (UInt256.ofNat I.codeOwner.val) key = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he ↦ hself (uInt256_eq_one_eq he).symm)
  have h₁ := safeRuntime_block_6162_fallthrough (by omega)
    (by rw [safeAddressMask, solcAddrMask_clean hc]; exact isZero_eq_zero_of_ne hv.1) h
  have h₂ := safeRuntime_block_6179 (by simp; omega) h₁
  simp only [safeRuntime_block_6179_stack, safeAddressMask, solcAddrMask_clean hc, hs] at h₂
  have h₃ := safeRuntime_block_6193_fallthrough (by simp; omega) rfl h₂
  have h₄ := safeRuntime_block_6199 (by simp; omega) h₃
  simp only [safeRuntime_block_6199_stack, safeAddressMask, solcAddrMask_clean hc, ht] at h₄
  exact ⟨_, _, safeRuntime_block_6212_taken (by simp; omega) (by decide) (by jump_dest) h₄⟩

theorem safeInvalidSwapNewOwnerTrace {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6162⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hv : ¬(validOwner σ I key ∧ key ≠ UInt256.ofNat I.codeOwner.val)) :
    RDrev fork safeBytecode g s0 := by
  have hbad : ∃ k' C', RD fork safeBytecode I g s0 ⟨6212⟩
      (⟨1⟩ :: key :: R) mem aw rdata σ k' C' := by
    by_cases hz : key = ⟨0⟩
    · have h₁ := safeRuntime_block_6162_taken (by omega)
        (by rw [safeAddressMask, solcAddrMask_clean hc, hz]; decide) (by jump_dest) h
      have heq : UInt256.isZero (UInt256.land key
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1))) = ⟨1⟩ := by
        rw [safeAddressMask, solcAddrMask_clean hc, hz]; rfl
      simp only [safeRuntime_block_6162_taken_stack, heq] at h₁
      exact ⟨_, _, safeRuntime_block_6193_taken (by simp; omega) (by decide) (by jump_dest) h₁⟩
    · have h₁ := safeRuntime_block_6162_fallthrough (by omega)
        (by rw [safeAddressMask, solcAddrMask_clean hc]; exact isZero_eq_zero_of_ne hz) h
      have h₂ := safeRuntime_block_6179 (by simp; omega) h₁
      simp only [safeRuntime_block_6179_stack, safeAddressMask, solcAddrMask_clean hc] at h₂
      by_cases hs : key = ⟨1⟩
      · have heq : UInt256.eq (UInt256.ofNat 1) key = ⟨1⟩ := by rw [hs]; rfl
        rw [heq] at h₂
        exact ⟨_, _, safeRuntime_block_6193_taken (by simp; omega) (by decide)
          (by jump_dest) h₂⟩
      · have heq : UInt256.eq (UInt256.ofNat 1) key = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he ↦ hs (uInt256_eq_one_eq he).symm)
        have ht : key = UInt256.ofNat I.codeOwner.val := by
          by_contra ht
          exact hv ⟨⟨hz, hs⟩, ht⟩
        rw [heq] at h₂
        have h₃ := safeRuntime_block_6193_fallthrough (by simp; omega) rfl h₂
        have h₄ := safeRuntime_block_6199 (by simp; omega) h₃
        simp only [safeRuntime_block_6199_stack, safeAddressMask, solcAddrMask_clean hc] at h₄
        have heq : UInt256.eq (UInt256.ofNat I.codeOwner.val) key = ⟨1⟩ := by
          rw [ht, uInt256_eq_self]
        rw [heq] at h₄
        exact ⟨_, _, h₄⟩
  obtain ⟨_, _, h₁⟩ := hbad
  have h₂ := safeRuntime_block_6212_fallthrough (by simp; omega) (by decide) h₁
  simp only [safeRuntime_block_6212_fallthrough_stack] at h₂
  have h₃ := safeRuntime_block_6218 (by simp; omega) (by jump_dest) h₂
  exact safeRuntime_block_6990 (by simp; omega) h₃

end Benchmarks.Safe.V0_cdb2eb5
