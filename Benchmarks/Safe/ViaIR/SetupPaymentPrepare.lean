import Benchmarks.Safe.ViaIR.PaymentOutcome
import Benchmarks.Safe.ViaIR.Blocks.Runtime_047
import Benchmarks.Safe.ViaIR.Blocks.Runtime_048

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

def setupPaymentAfterArithmeticPC (p : PaymentInput) : UInt256 :=
  if p.gasToken = EVM.address 0 then ⟨10499⟩ else ⟨10565⟩

def setupPaymentArithmeticSaved (p : PaymentInput) (I : ExecutionEnv) (ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  (if p.gasToken = EVM.address 0 then [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]
    else [UInt256.ofNat p.gasToken.val, ⟨0⟩, ⟨32⟩]) ++
    ret :: UInt256.ofNat (p.receiver I).val :: R

theorem safeSetupPaymentBounds (p : PaymentInput) (I : ExecutionEnv)
    (hbase : p.baseGas = ⟨0⟩) (hprice : p.gasPrice = ⟨1⟩) :
    p.gasUsed.toNat + p.baseGas.toNat < UInt256.size ∧
      p.gasTotal.toNat * (paymentPrice p I).toNat < UInt256.size := by
  have ht : p.gasTotal = p.gasUsed := by rw [PaymentInput.gasTotal, hbase, u256_add_zero]
  have hpriceBound : (paymentPrice p I).toNat ≤ 1 := by
    unfold paymentPrice
    split
    · unfold PaymentInput.nativePrice
      split
      · rw [hprice]; decide
      · rename_i hle
        rw [hprice] at hle
        change ¬1 < (UInt256.ofNat I.gasPrice).toNat at hle
        omega
    · rw [hprice]; decide
  have hu := p.gasUsed.val.isLt
  constructor
  · simpa only [hbase, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.add_zero] using hu
  · rw [ht]
    exact lt_of_le_of_lt (by simpa using Nat.mul_le_mul_left p.gasUsed.toNat hpriceBound) hu

theorem safeSetupPaymentReceiverTrace (p : PaymentInput) {I g s0 σ k C aw mem rdata}
    {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10429⟩
      (p.gasUsed :: UInt256.ofNat p.gasToken.val :: UInt256.ofNat p.refundReceiver.val ::
        ret :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨10452⟩
      (UInt256.ofNat p.gasToken.val :: ⟨0⟩ :: p.gasUsed :: ret ::
        UInt256.ofNat (p.receiver I).val :: R) mem aw rdata σ k' C' := by
  have hc : (UInt256.ofNat p.refundReceiver.val).toNat < EVM.addressModulus :=
    addressWord_canonical _
  by_cases hz : p.refundReceiver = EVM.address 0
  · have hw : UInt256.ofNat p.refundReceiver.val = ⟨0⟩ := by rw [hz]; rfl
    have h₁ := safeRuntime_block_10429_fallthrough (by simp; omega)
      (by rw [hw]; decide) h
    simp only [safeRuntime_block_10429_fallthrough_stack] at h₁
    have h₂ := safeRuntime_block_10449 (by simp; omega) h₁
    simp only [safeRuntime_block_10449_stack] at h₂
    have h₃ := transactionEnvRead .origin h₂ (by native_decide) (by simp; omega)
    have h₄ := safeRuntime_block_10451 (by simp; omega) h₃
    exact ⟨_, _, by simpa only [safeRuntime_block_10451_stack, TransactionEnvField.word,
      PaymentInput.receiver, hz, ite_true] using h₄⟩
  · have hw : UInt256.ofNat p.refundReceiver.val ≠ ⟨0⟩ := by
      intro he
      have he' := congrArg AccountAddress.ofUInt256 he
      rw [accountAddress_roundtrip] at he'
      exact hz he'
    have h₁ := safeRuntime_block_10429_taken (by simp; omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc]; exact hw) (by jump_dest) h
    simp only [safeRuntime_block_10429_taken_stack] at h₁
    have h₂ := safeRuntime_block_10669 (by simp; omega) (by jump_dest) h₁
    exact ⟨_, _, by simpa only [safeRuntime_block_10669_stack, PaymentInput.receiver,
      hz, ite_false] using h₂⟩

theorem safeSetupPaymentNativePriceTrace (p : PaymentInput) {I g s0 σ k C aw mem rdata}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10473⟩ (⟨0⟩ :: p.gasUsed :: R) mem aw rdata σ k C)
    (hprice : p.gasPrice = ⟨1⟩) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨9466⟩
      (p.gasUsed :: p.nativePrice I :: ⟨10499⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_10473 (by simp; omega) h
  simp only [safeRuntime_block_10473_stack] at h₁
  have h₂ := transactionEnvRead .gasPrice h₁ (by native_decide) (by simp; omega)
  by_cases hp : p.gasPrice.toNat < (UInt256.ofNat I.gasPrice).toNat
  · have hlt : UInt256.lt (UInt256.ofNat 1) (UInt256.ofNat I.gasPrice) = ⟨1⟩ :=
      ult_one (by simpa only [hprice] using hp)
    have h₃ := safeRuntime_block_10483_fallthrough (by simp; omega)
      (by simp only [TransactionEnvField.word, hlt]; decide) h₂
    have h₄ := safeRuntime_block_10492
      (by simp; omega) (by jump_dest) h₃
    have hnp : p.nativePrice I = p.gasPrice := if_pos hp
    exact ⟨_, _, by simpa only [safeRuntime_block_10492_stack,
      safeRuntime_block_10483_fallthrough_stack, hnp, hprice] using h₄⟩
  · have hlt : UInt256.lt (UInt256.ofNat 1) (UInt256.ofNat I.gasPrice) = ⟨0⟩ :=
      ult_zero (by rw [hprice] at hp; exact Nat.le_of_not_lt hp)
    have h₃ := safeRuntime_block_10483_taken (by simp; omega)
      (by simp only [TransactionEnvField.word, hlt]; decide) (by jump_dest) h₂
    simp only [safeRuntime_block_10483_taken_stack] at h₃
    have h₄ := safeRuntime_block_5111 (by simp; omega) h₃
    have h₅ := transactionEnvRead .gasPrice h₄ (by native_decide) (by simp; omega)
    have h₆ := safeRuntime_block_5113 (by simp; omega) (by jump_dest) h₅
    exact ⟨_, _, by simpa only [safeRuntime_block_5113_stack, TransactionEnvField.word,
      PaymentInput.nativePrice, hp, ite_false] using h₆⟩

theorem safeSetupPaymentArithmetic (p : PaymentInput) {I g s0 σ k C aw mem rdata}
    {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10429⟩
      (p.gasUsed :: UInt256.ofNat p.gasToken.val :: UInt256.ofNat p.refundReceiver.val ::
        ret :: R) mem aw rdata σ k C)
    (hbase : p.baseGas = ⟨0⟩) (hprice : p.gasPrice = ⟨1⟩)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 (setupPaymentAfterArithmeticPC p)
      (UInt256.mul p.gasTotal (paymentPrice p I) :: setupPaymentArithmeticSaved p I ret R)
      mem aw rdata σ k' C' := by
  obtain ⟨k₁, C₁, h₁⟩ := safeSetupPaymentReceiverTrace p h (by omega)
  have ht : p.gasTotal = p.gasUsed := by rw [PaymentInput.gasTotal, hbase, u256_add_zero]
  have hprod := (safeSetupPaymentBounds p I hbase hprice).2
  have hmul : ∃ k₂ C₂, RD fork safeBytecode I g s0 ⟨9466⟩
      (p.gasTotal :: paymentPrice p I :: setupPaymentAfterArithmeticPC p ::
        setupPaymentArithmeticSaved p I ret R) mem aw rdata σ k₂ C₂ := by
    by_cases hz : p.gasToken = EVM.address 0
    · have hw : UInt256.ofNat p.gasToken.val = ⟨0⟩ := by rw [hz]; rfl
      have h₂ := safeRuntime_block_10452_fallthrough (by simp; omega)
        (by rw [hw]; decide) h₁
      have h₃ := safeRuntime_block_10467_fallthrough (by simp; omega) rfl h₂
      simp only [safeRuntime_block_10467_fallthrough_stack] at h₃
      obtain ⟨k₄, C₄, h₄⟩ :=
        safeSetupPaymentNativePriceTrace p h₃ hprice (by simp; omega)
      exact ⟨k₄, C₄, by simpa only [paymentPrice, setupPaymentAfterArithmeticPC,
        setupPaymentArithmeticSaved, hz, ite_true, ht, List.cons_append, List.nil_append]
        using h₄⟩
    · have hw : UInt256.ofNat p.gasToken.val ≠ ⟨0⟩ := by
        intro he
        have he' := congrArg AccountAddress.ofUInt256 he
        rw [accountAddress_roundtrip] at he'
        exact hz he'
      have h₂ := safeRuntime_block_10452_taken (by simp; omega)
        (by rw [safeAddressMask, solcAddrMask_clean (addressWord_canonical _)]; exact hw)
        (by jump_dest) h₁
      have h₃ := safeRuntime_block_10549 (by simp; omega) (by jump_dest) h₂
      exact ⟨_, _, by simpa only [safeRuntime_block_10549_stack, paymentPrice,
        setupPaymentAfterArithmeticPC, setupPaymentArithmeticSaved, hz, ite_false, ht,
        hprice, List.cons_append, List.nil_append] using h₃⟩
  obtain ⟨k₂, C₂, h₂⟩ := hmul
  have hret : (D_J safeBytecode 0).contains (setupPaymentAfterArithmeticPC p) = true := by
    unfold setupPaymentAfterArithmeticPC
    split <;> jump_dest
  exact safeMulTrace h₂ hprod (by
    unfold setupPaymentArithmeticSaved
    split <;> simp <;> omega) hret

end Benchmarks.Safe.ViaIR
