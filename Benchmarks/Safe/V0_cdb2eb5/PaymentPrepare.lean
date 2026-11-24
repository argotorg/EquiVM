import Benchmarks.Safe.V0_cdb2eb5.PaymentSource
import Benchmarks.Safe.V0_cdb2eb5.TransactionEnvRead
import Benchmarks.Safe.V0_cdb2eb5.Decoders
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_034
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_035

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

def paymentPrice (p : PaymentInput) (I : ExecutionEnv) : UInt256 :=
  if p.gasToken = EVM.address 0 then p.nativePrice I else p.gasPrice

def paymentAfterArithmeticPC (p : PaymentInput) : UInt256 :=
  if p.gasToken = EVM.address 0 then ⟨7973⟩ else ⟨8099⟩

theorem safePaymentReceiverWord (p : PaymentInput) (I : ExecutionEnv) :
    (UInt256.ofNat (p.receiver I).val).toNat < EVM.addressModulus :=
  addressWord_canonical _

set_option maxRecDepth 100000 in
theorem safePaymentReceiverTrace (p : PaymentInput) {I g s0 σ k C aw mem rdata}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7898⟩ (UInt256.ofNat p.refundReceiver.val :: R)
      mem aw rdata σ k C) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7923⟩
      (UInt256.ofNat (p.receiver I).val :: ⟨0⟩ :: ⟨0⟩ ::
        UInt256.ofNat p.refundReceiver.val :: R) mem aw rdata σ k' C' := by
  have hc : (UInt256.ofNat p.refundReceiver.val).toNat < EVM.addressModulus :=
    addressWord_canonical _
  by_cases hz : p.refundReceiver = EVM.address 0
  · have hw : UInt256.ofNat p.refundReceiver.val = ⟨0⟩ := by rw [hz]; rfl
    have h₁ := safeRuntime_block_7898_taken (by omega)
      (by rw [hw]; decide) (by jump_dest) h
    simp only [safeRuntime_block_7898_taken_stack] at h₁
    have h₂ := safeRuntime_block_7921 (by simp; omega) h₁
    have h₃ := transactionEnvRead .origin h₂ (by native_decide) (by simp; omega)
    exact ⟨_, _, by simpa only [TransactionEnvField.word, PaymentInput.receiver, hz, ite_true]
      using h₃⟩
  · have hw : UInt256.ofNat p.refundReceiver.val ≠ ⟨0⟩ := by
      intro he
      have he' := congrArg AccountAddress.ofUInt256 he
      rw [accountAddress_roundtrip] at he'
      exact hz he'
    have h₁ := safeRuntime_block_7898_fallthrough (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc]; exact isZero_eq_zero_of_ne hw) h
    simp only [safeRuntime_block_7898_fallthrough_stack] at h₁
    have h₂ := safeRuntime_block_7916 (by simp; omega) (by jump_dest) h₁
    exact ⟨_, _, by simpa only [safeRuntime_block_7916_stack, PaymentInput.receiver, hz,
      ite_false] using h₂⟩

set_option maxRecDepth 100000 in
theorem safePaymentNativePriceTrace (p : PaymentInput) {I g s0 σ k C aw mem rdata}
    {receiver ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7940⟩
      (receiver :: ⟨0⟩ :: UInt256.ofNat p.refundReceiver.val :: UInt256.ofNat p.gasToken.val ::
        p.gasPrice :: p.baseGas :: p.gasUsed :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7957⟩
      (p.nativePrice I :: ⟨7973⟩ :: receiver :: ⟨0⟩ :: UInt256.ofNat p.refundReceiver.val ::
        UInt256.ofNat p.gasToken.val :: p.gasPrice :: p.baseGas :: p.gasUsed :: ret :: R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_7940 (by simp; omega) h
  simp only [safeRuntime_block_7940_stack] at h₁
  have h₂ := transactionEnvRead .gasPrice h₁ (by native_decide) (by simp; omega)
  simp only [TransactionEnvField.word] at h₂
  by_cases hp : p.gasPrice.toNat < (UInt256.ofNat I.gasPrice).toNat
  · have h₃ := safeRuntime_block_7944_taken (by simp; omega)
      (by rw [ult_one hp]; decide) (by jump_dest) h₂
    simp only [safeRuntime_block_7944_taken_stack] at h₃
    have h₄ := safeRuntime_block_7955 (by simp; omega) h₃
    exact ⟨_, _, by simpa only [safeRuntime_block_7955_stack, PaymentInput.nativePrice,
      hp, ite_true] using h₄⟩
  · have h₃ := safeRuntime_block_7944_fallthrough (by simp; omega)
      (by exact ult_zero (by omega)) h₂
    simp only [safeRuntime_block_7944_fallthrough_stack] at h₃
    have h₄ := transactionEnvRead .gasPrice h₃ (by native_decide) (by simp; omega)
    have h₅ := safeRuntime_block_7951 (by simp; omega) (by jump_dest) h₄
    exact ⟨_, _, by simpa only [TransactionEnvField.word, PaymentInput.nativePrice,
      hp, ite_false] using h₅⟩

set_option maxRecDepth 100000 in
theorem safePaymentPrepare (p : PaymentInput) {I g s0 σ k C aw mem rdata}
    {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7898⟩
      (UInt256.ofNat p.refundReceiver.val :: UInt256.ofNat p.gasToken.val :: p.gasPrice ::
        p.baseGas :: p.gasUsed :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8786⟩
      (p.baseGas :: p.gasUsed :: ⟨7967⟩ :: paymentPrice p I :: paymentAfterArithmeticPC p ::
        UInt256.ofNat (p.receiver I).val :: ⟨0⟩ :: UInt256.ofNat p.refundReceiver.val ::
        UInt256.ofNat p.gasToken.val :: p.gasPrice :: p.baseGas :: p.gasUsed :: ret :: R)
      mem aw rdata σ k' C' := by
  obtain ⟨k₁, C₁, h₁⟩ := safePaymentReceiverTrace p h (by simp; omega)
  have hc : (UInt256.ofNat p.gasToken.val).toNat < EVM.addressModulus :=
    addressWord_canonical _
  by_cases hz : p.gasToken = EVM.address 0
  · have hw : UInt256.ofNat p.gasToken.val = ⟨0⟩ := by rw [hz]; rfl
    have h₂ := safeRuntime_block_7923_fallthrough (by simp; omega)
      (by rw [hw]; decide) h₁
    simp only [safeRuntime_block_7923_fallthrough_stack] at h₂
    obtain ⟨k₃, C₃, h₃⟩ := safePaymentNativePriceTrace p h₂ (by omega)
    have h₄ := safeRuntime_block_7957 (by simp; omega) (by jump_dest) h₃
    exact ⟨_, _, by simpa only [safeRuntime_block_7957_stack, paymentPrice,
      paymentAfterArithmeticPC, hz, ite_true] using h₄⟩
  · have hw : UInt256.ofNat p.gasToken.val ≠ ⟨0⟩ := by
      intro he
      have he' := congrArg AccountAddress.ofUInt256 he
      rw [accountAddress_roundtrip] at he'
      exact hz he'
    have h₂ := safeRuntime_block_7923_taken (by simp; omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc]; exact hw) (by jump_dest) h₁
    simp only [safeRuntime_block_7923_taken_stack] at h₂
    have h₃ := safeRuntime_block_8085 (by simp; omega) (by jump_dest) h₂
    exact ⟨_, _, by simpa only [safeRuntime_block_8085_stack, paymentPrice,
      paymentAfterArithmeticPC, hz, ite_false] using h₃⟩

end Benchmarks.Safe.V0_cdb2eb5
