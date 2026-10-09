import Benchmarks.Safe.PaymentSource
import Benchmarks.Safe.TransactionEnvRead
import Benchmarks.Safe.Decoders
import Benchmarks.Safe.Blocks.Runtime_033
import Benchmarks.Safe.Blocks.Runtime_034

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def paymentPrice (p : PaymentInput) (I : ExecutionEnv) : UInt256 :=
  if p.gasToken = EVM.address 0 then p.nativePrice I else p.gasPrice

def paymentAfterArithmeticPC (p : PaymentInput) : UInt256 :=
  if p.gasToken = EVM.address 0 then ⟨7805⟩ else ⟨7931⟩

theorem safePaymentReceiverWord (p : PaymentInput) (I : ExecutionEnv) :
    (UInt256.ofNat (p.receiver I).val).toNat < EVM.addressModulus :=
  addressWord_canonical _

set_option maxRecDepth 100000 in
theorem safePaymentReceiverTrace (p : PaymentInput) {I g s0 σ k C aw mem rdata}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7730⟩ (UInt256.ofNat p.refundReceiver.val :: R)
      mem aw rdata σ k C) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨7755⟩
      (UInt256.ofNat (p.receiver I).val :: ⟨0⟩ :: ⟨0⟩ ::
        UInt256.ofNat p.refundReceiver.val :: R) mem aw rdata σ k' C' := by
  have hc : (UInt256.ofNat p.refundReceiver.val).toNat < EVM.addressModulus :=
    addressWord_canonical _
  by_cases hz : p.refundReceiver = EVM.address 0
  · have hw : UInt256.ofNat p.refundReceiver.val = ⟨0⟩ := by rw [hz]; rfl
    have h₁ := safeRuntime_block_7730_taken (by omega)
      (by rw [hw]; decide) (by jump_dest) h
    simp only [safeRuntime_block_7730_taken_stack] at h₁
    have h₂ := safeRuntime_block_7753 (by simp; omega) h₁
    have h₃ := transactionEnvRead .origin h₂ (by native_decide) (by simp; omega)
    exact ⟨_, _, by simpa only [TransactionEnvField.word, PaymentInput.receiver, hz, ite_true]
      using h₃⟩
  · have hw : UInt256.ofNat p.refundReceiver.val ≠ ⟨0⟩ := by
      intro he
      have he' := congrArg AccountAddress.ofUInt256 he
      rw [accountAddress_roundtrip] at he'
      exact hz he'
    have h₁ := safeRuntime_block_7730_fallthrough (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc]; exact isZero_eq_zero_of_ne hw) h
    simp only [safeRuntime_block_7730_fallthrough_stack] at h₁
    have h₂ := safeRuntime_block_7748 (by simp; omega) (by jump_dest) h₁
    exact ⟨_, _, by simpa only [safeRuntime_block_7748_stack, PaymentInput.receiver, hz,
      ite_false] using h₂⟩

set_option maxRecDepth 100000 in
theorem safePaymentNativePriceTrace (p : PaymentInput) {I g s0 σ k C aw mem rdata}
    {receiver ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7772⟩
      (receiver :: ⟨0⟩ :: UInt256.ofNat p.refundReceiver.val :: UInt256.ofNat p.gasToken.val ::
        p.gasPrice :: p.baseGas :: p.gasUsed :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨7789⟩
      (p.nativePrice I :: ⟨7805⟩ :: receiver :: ⟨0⟩ :: UInt256.ofNat p.refundReceiver.val ::
        UInt256.ofNat p.gasToken.val :: p.gasPrice :: p.baseGas :: p.gasUsed :: ret :: R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_7772 (by simp; omega) h
  simp only [safeRuntime_block_7772_stack] at h₁
  have h₂ := transactionEnvRead .gasPrice h₁ (by native_decide) (by simp; omega)
  simp only [TransactionEnvField.word] at h₂
  by_cases hp : p.gasPrice.toNat < (UInt256.ofNat I.gasPrice).toNat
  · have h₃ := safeRuntime_block_7776_taken (by simp; omega)
      (by rw [ult_one hp]; decide) (by jump_dest) h₂
    simp only [safeRuntime_block_7776_taken_stack] at h₃
    have h₄ := safeRuntime_block_7787 (by simp; omega) h₃
    exact ⟨_, _, by simpa only [safeRuntime_block_7787_stack, PaymentInput.nativePrice,
      hp, ite_true] using h₄⟩
  · have h₃ := safeRuntime_block_7776_fallthrough (by simp; omega)
      (by exact ult_zero (by omega)) h₂
    simp only [safeRuntime_block_7776_fallthrough_stack] at h₃
    have h₄ := transactionEnvRead .gasPrice h₃ (by native_decide) (by simp; omega)
    have h₅ := safeRuntime_block_7783 (by simp; omega) (by jump_dest) h₄
    exact ⟨_, _, by simpa only [TransactionEnvField.word, PaymentInput.nativePrice,
      hp, ite_false] using h₅⟩

set_option maxRecDepth 100000 in
theorem safePaymentPrepare (p : PaymentInput) {I g s0 σ k C aw mem rdata}
    {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7730⟩
      (UInt256.ofNat p.refundReceiver.val :: UInt256.ofNat p.gasToken.val :: p.gasPrice ::
        p.baseGas :: p.gasUsed :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨7082⟩
      (p.baseGas :: p.gasUsed :: ⟨7799⟩ :: paymentPrice p I :: paymentAfterArithmeticPC p ::
        UInt256.ofNat (p.receiver I).val :: ⟨0⟩ :: UInt256.ofNat p.refundReceiver.val ::
        UInt256.ofNat p.gasToken.val :: p.gasPrice :: p.baseGas :: p.gasUsed :: ret :: R)
      mem aw rdata σ k' C' := by
  obtain ⟨k₁, C₁, h₁⟩ := safePaymentReceiverTrace p h (by simp; omega)
  have hc : (UInt256.ofNat p.gasToken.val).toNat < EVM.addressModulus :=
    addressWord_canonical _
  by_cases hz : p.gasToken = EVM.address 0
  · have hw : UInt256.ofNat p.gasToken.val = ⟨0⟩ := by rw [hz]; rfl
    have h₂ := safeRuntime_block_7755_fallthrough (by simp; omega)
      (by rw [hw]; decide) h₁
    simp only [safeRuntime_block_7755_fallthrough_stack] at h₂
    obtain ⟨k₃, C₃, h₃⟩ := safePaymentNativePriceTrace p h₂ (by omega)
    have h₄ := safeRuntime_block_7789 (by simp; omega) (by jump_dest) h₃
    exact ⟨_, _, by simpa only [safeRuntime_block_7789_stack, paymentPrice,
      paymentAfterArithmeticPC, hz, ite_true] using h₄⟩
  · have hw : UInt256.ofNat p.gasToken.val ≠ ⟨0⟩ := by
      intro he
      have he' := congrArg AccountAddress.ofUInt256 he
      rw [accountAddress_roundtrip] at he'
      exact hz he'
    have h₂ := safeRuntime_block_7755_taken (by simp; omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc]; exact hw) (by jump_dest) h₁
    simp only [safeRuntime_block_7755_taken_stack] at h₂
    have h₃ := safeRuntime_block_7917 (by simp; omega) (by jump_dest) h₂
    exact ⟨_, _, by simpa only [safeRuntime_block_7917_stack, paymentPrice,
      paymentAfterArithmeticPC, hz, ite_false] using h₃⟩

end Benchmarks.Safe
