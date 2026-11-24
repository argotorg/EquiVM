import Benchmarks.Safe.ViaIR.PaymentSource
import Benchmarks.Safe.ViaIR.TransactionEnvRead
import Benchmarks.Safe.ViaIR.Decoders
import Benchmarks.Safe.ViaIR.Blocks.Runtime_024
import Benchmarks.Safe.ViaIR.Blocks.Runtime_025
import Benchmarks.Safe.ViaIR.Blocks.Runtime_026

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def paymentPrice (p : PaymentInput) (I : ExecutionEnv) : UInt256 :=
  if p.gasToken = EVM.address 0 then p.nativePrice I else p.gasPrice

def paymentAfterArithmeticPC (p : PaymentInput) : UInt256 :=
  if p.gasToken = EVM.address 0 then ⟨5066⟩ else ⟨5152⟩

def paymentAddReturnPC (p : PaymentInput) : UInt256 :=
  if p.gasToken = EVM.address 0 then ⟨5032⟩ else ⟨5130⟩

def paymentAddSaved (p : PaymentInput) (I : ExecutionEnv) (R : List UInt256) :
    List UInt256 :=
  (if p.gasToken = EVM.address 0 then [p.gasUsed, ⟨0⟩]
    else [UInt256.ofNat p.gasToken.val, ⟨0⟩, p.gasUsed]) ++
    UInt256.ofNat (p.receiver I).val :: R

def paymentArithmeticSaved (p : PaymentInput) (I : ExecutionEnv) (R : List UInt256) :
    List UInt256 :=
  (if p.gasToken = EVM.address 0 then [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]
    else [UInt256.ofNat p.gasToken.val, ⟨0⟩, ⟨32⟩]) ++
    UInt256.ofNat (p.receiver I).val :: R

theorem safePaymentReceiverWord (p : PaymentInput) (I : ExecutionEnv) :
    (UInt256.ofNat (p.receiver I).val).toNat < EVM.addressModulus :=
  addressWord_canonical _

set_option maxRecDepth 5000 in
theorem safePaymentReceiverTrace (p : PaymentInput) {I g s0 σ k C aw mem rdata}
    {scratch₀ scratch₁ : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4979⟩
      (UInt256.ofNat p.refundReceiver.val :: ⟨0⟩ :: p.gasUsed ::
        UInt256.ofNat p.gasToken.val :: scratch₀ :: scratch₁ :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨5004⟩
      (UInt256.ofNat p.gasToken.val :: ⟨0⟩ :: p.gasUsed ::
        UInt256.ofNat (p.receiver I).val :: R) mem aw rdata σ k' C' := by
  have hc : (UInt256.ofNat p.refundReceiver.val).toNat < EVM.addressModulus :=
    addressWord_canonical _
  by_cases hz : p.refundReceiver = EVM.address 0
  · have hw : UInt256.ofNat p.refundReceiver.val = ⟨0⟩ := by rw [hz]; rfl
    have h₁ := safeRuntime_block_4979_fallthrough (by simp; omega)
      (by rw [hw]; decide) h
    have h₂ := safeRuntime_block_5001 (by simp; omega) h₁
    simp only [safeRuntime_block_5001_stack] at h₂
    have h₃ := transactionEnvRead .origin h₂ (by native_decide) (by simp; omega)
    have h₄ := safeRuntime_block_5003 (by simp; omega) h₃
    exact ⟨_, _, by simpa only [safeRuntime_block_5003_stack, TransactionEnvField.word,
      PaymentInput.receiver, hz, ite_true] using h₄⟩
  · have hw : UInt256.ofNat p.refundReceiver.val ≠ ⟨0⟩ := by
      intro he
      have he' := congrArg AccountAddress.ofUInt256 he
      rw [accountAddress_roundtrip] at he'
      exact hz he'
    have h₁ := safeRuntime_block_4979_taken (by simp; omega)
      (by change UInt256.land _ solcAddrMask ≠ _; rw [solcAddrMask_clean hc]; exact hw)
      (by jump_dest) h
    have h₂ := safeRuntime_block_5266 (by simp; omega) (by jump_dest) h₁
    exact ⟨_, _, by simpa only [safeRuntime_block_5266_stack, PaymentInput.receiver, hz,
      ite_false] using h₂⟩

set_option maxRecDepth 5000 in
theorem safePaymentNativePriceTrace (p : PaymentInput) {I g s0 σ k C aw mem rdata}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5040⟩ (p.gasTotal :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hc : calldataWord I.calldata 196 = p.gasPrice) (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨9466⟩
      (p.gasTotal :: p.nativePrice I :: ⟨5066⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_5040 (by simp; omega) h
  simp only [safeRuntime_block_5040_stack] at h₁
  have h₂ := transactionEnvRead .gasPrice h₁ (by native_decide) (by simp; omega)
  change uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 196).toNat 32) =
    p.gasPrice at hc
  by_cases hp : p.gasPrice.toNat < (UInt256.ofNat I.gasPrice).toNat
  · have h₃ := safeRuntime_block_5048_fallthrough (by simp; omega)
      (by simp only [hc, TransactionEnvField.word, ult_one hp]; decide) h₂
    have h₄ := safeRuntime_block_5058 (by simp; omega) (by jump_dest) h₃
    exact ⟨_, _, by simpa only [safeRuntime_block_5058_stack, hc,
      PaymentInput.nativePrice, hp, ite_true] using h₄⟩
  · have h₃ := safeRuntime_block_5048_taken (by simp; omega)
      (by simp only [hc, TransactionEnvField.word, ult_zero (by omega :
        (UInt256.ofNat I.gasPrice).toNat ≤ p.gasPrice.toNat)]; decide) (by jump_dest) h₂
    simp only [safeRuntime_block_5048_taken_stack] at h₃
    have h₄ := safeRuntime_block_5111 (by simp; omega) h₃
    have h₅ := transactionEnvRead .gasPrice h₄ (by native_decide) (by simp; omega)
    have h₆ := safeRuntime_block_5113 (by simp; omega) (by jump_dest) h₅
    exact ⟨_, _, by simpa only [safeRuntime_block_5113_stack, TransactionEnvField.word,
      PaymentInput.nativePrice, hp, ite_false] using h₆⟩

set_option maxRecDepth 5000 in
theorem safePaymentPrepare (p : PaymentInput) {I g s0 σ k C aw mem rdata}
    {scratch₀ scratch₁ : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4979⟩
      (UInt256.ofNat p.refundReceiver.val :: ⟨0⟩ :: p.gasUsed ::
        UInt256.ofNat p.gasToken.val :: scratch₀ :: scratch₁ :: R) mem aw rdata σ k C)
    (hc : calldataWord I.calldata 164 = p.baseGas) (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8914⟩
      (p.gasUsed :: p.baseGas :: paymentAddReturnPC p :: paymentAddSaved p I R)
      mem aw rdata σ k' C' := by
  obtain ⟨k₁, C₁, h₁⟩ := safePaymentReceiverTrace p h (by omega)
  have ht : (UInt256.ofNat p.gasToken.val).toNat < EVM.addressModulus :=
    addressWord_canonical _
  change uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 164).toNat 32) =
    p.baseGas at hc
  by_cases hz : p.gasToken = EVM.address 0
  · have hw : UInt256.ofNat p.gasToken.val = ⟨0⟩ := by rw [hz]; rfl
    have h₂ := safeRuntime_block_5004_fallthrough (by simp; omega)
      (by rw [hw]; decide) h₁
    have h₃ := safeRuntime_block_5019 (by simp; omega) (by jump_dest) h₂
    exact ⟨_, _, by simpa only [safeRuntime_block_5019_stack, hc, paymentAddReturnPC,
      paymentAddSaved, hz, ite_true, List.cons_append, List.nil_append] using h₃⟩
  · have hw : UInt256.ofNat p.gasToken.val ≠ ⟨0⟩ := by
      intro he
      have he' := congrArg AccountAddress.ofUInt256 he
      rw [accountAddress_roundtrip] at he'
      exact hz he'
    have h₂ := safeRuntime_block_5004_taken (by simp; omega)
      (by change UInt256.land _ solcAddrMask ≠ _; rw [solcAddrMask_clean ht]; exact hw)
      (by jump_dest) h₁
    have h₃ := safeRuntime_block_5118 (by simp; omega) (by jump_dest) h₂
    exact ⟨_, _, by simpa only [safeRuntime_block_5118_stack, hc, paymentAddReturnPC,
      paymentAddSaved, hz, ite_false, List.cons_append, List.nil_append] using h₃⟩

end Benchmarks.Safe.ViaIR
