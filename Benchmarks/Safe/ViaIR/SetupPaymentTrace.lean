import Benchmarks.Safe.ViaIR.SetupOutcome
import Benchmarks.Safe.ViaIR.SetupPaymentPaths
import Benchmarks.Safe.ViaIR.Blocks.Runtime_017

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 5000

theorem safeSetupPaymentTrace (p : SetupInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr locals} {x y : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3475⟩
      (x :: y :: p.paymentToken :: p.paymentReceiver :: p.payment :: ⟨0⟩ :: R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hl : SetupLocals p locals)
    (htoken : p.paymentToken.toNat < EVM.addressModulus)
    (hreceiver : p.paymentReceiver.toNat < EVM.addressModulus)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hp : 128 ≤ ptr)
    (hptr : ptr = 160 + 32 * p.owners.length + 32 + ABI.paddedSize p.payload.size)
    (hcap : ptr < 2 ^ 64) (hperm : I.perm = true) (hov : R.length + 36 ≤ 1024) :
    SetupTailOutcome fork p { contract := contract, locals := locals } evm [setupPaymentStmt] g s0 := by
  have hdata : 32 * p.owners.length + p.payload.size ≤ 2 ^ 64 - 224 := by
    rw [hptr] at hcap
    unfold ABI.paddedSize at hcap
    omega
  by_cases hpay : p.payment = ⟨0⟩
  · have h₁ := safeRuntime_block_3475_fallthrough (by simp; omega) hpay h
    have h₂ := safeRuntime_block_3483 (by simp; omega) h₁
    have ha : 32 * p.owners.length + p.payload.size ≤ p.allocationLimit := by
      simpa only [SetupInput.allocationLimit, hpay, ne_self_iff_false, false_and,
        ite_false] using hdata
    exact .success ha (execBlock_singleton (safeSetupPaymentSkip p evm hl hpay))
      (by simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        byteArray_readWithPadding_zero, hacc] using h₂)
  have h₁ := safeRuntime_block_3475_taken (by simp; omega) hpay (by jump_dest) h
  have h₂ := safeRuntime_block_3486 (by simp; omega) (by jump_dest) h₁
  have ht : UInt256.ofNat p.paymentInput.gasToken.val = p.paymentToken :=
    ((canonicalAddress_eq_address_iff _ _ htoken).mp rfl).symm
  have hr : UInt256.ofNat p.paymentInput.refundReceiver.val = p.paymentReceiver :=
    ((canonicalAddress_eq_address_iff _ _ hreceiver).mp rfl).symm
  have hcall : RD fork safeBytecode I g s0 ⟨10429⟩
      (p.paymentInput.gasUsed :: UInt256.ofNat p.paymentInput.gasToken.val ::
        UInt256.ofNat p.paymentInput.refundReceiver.val :: ⟨3495⟩ :: ⟨0⟩ :: R)
      mem aw rdata σ (k + 6 + 5) (C + 21 + 18) := by
    rw [ht, hr]
    exact h₂
  obtain ⟨k₃, C₃, h₃⟩ :=
    safeSetupPaymentArithmetic p.paymentInput hcall rfl rfl (by simp; omega)
  have hs := (safeSetupPaymentBounds p.paymentInput I rfl rfl).1
  have hm := (safeSetupPaymentBounds p.paymentInput I rfl rfl).2
  have finish (ha : 32 * p.owners.length + p.payload.size ≤ p.allocationLimit)
      (ho : SetupPaymentOutcome fork p.paymentInput evm I g s0 ⟨3495⟩ (⟨0⟩ :: R)) :
      SetupTailOutcome fork p { contract := contract, locals := locals } evm
        [setupPaymentStmt] g s0 := by
    obtain ⟨hrev, hsource⟩ | ⟨f', evm', mem', out, aw', k', C', hsource, htrace⟩ := ho
    · exact .reverted (.consRevert (safeSetupPaymentCall p evm hl hpay hsource)) hrev
    · have hret := safeRuntime_block_3495 (by omega) htrace
      exact .success ha (execBlock_singleton (safeSetupPaymentCall p evm hl hpay hsource))
        (by simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
          byteArray_readWithPadding_zero] using hret)
  by_cases hz : p.paymentInput.gasToken = EVM.address 0
  · simp only [setupPaymentAfterArithmeticPC, setupPaymentArithmeticSaved, paymentPrice,
      hz, ite_true, List.cons_append, List.nil_append] at h₃ hm
    apply finish
    · change AccountAddress.ofNat p.paymentToken.toNat = EVM.address 0 at hz
      simpa only [SetupInput.allocationLimit, hz, ne_self_iff_false, and_false,
        ite_false] using hdata
    · exact safeSetupPaymentNativeTrace p.paymentInput evm h₃ hee hacc hworld hs hm hz
        hf hcap hperm (by simp; omega) (by jump_dest)
  · simp only [setupPaymentAfterArithmeticPC, setupPaymentArithmeticSaved, paymentPrice,
      hz, ite_false, List.cons_append, List.nil_append] at h₃ hm
    by_cases hfit : ptr + 128 < 2 ^ 64
    · apply finish
      · rw [safeSetupAllocationLimit_token p hpay hz]
        rw [hptr] at hfit
        unfold ABI.paddedSize at hfit
        omega
      · exact safeSetupPaymentTokenTrace p.paymentInput evm h₃ hee hacc hworld hs hm hz
          hf hp hfit (by simp; omega) (by jump_dest)
    · refine .allocationRevert ?_
        (safeSetupTokenTransferAllocationRevert h₃ hf hcap hfit (by simp; omega))
      rw [safeSetupAllocationLimit_token p hpay hz]
      rw [hptr] at hfit
      unfold ABI.paddedSize at hfit
      omega

end Benchmarks.Safe.ViaIR
