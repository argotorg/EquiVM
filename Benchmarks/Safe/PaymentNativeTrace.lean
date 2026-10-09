import Benchmarks.Safe.PaymentOutcome
import Benchmarks.Safe.PaymentNativeReturn
import Benchmarks.Safe.RawValueCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safePaymentNativeTrace (p : PaymentInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7805⟩
      (UInt256.mul p.gasTotal (p.nativePrice I) :: UInt256.ofNat (p.receiver I).val :: ⟨0⟩ ::
        UInt256.ofNat p.refundReceiver.val :: UInt256.ofNat p.gasToken.val :: p.gasPrice ::
        p.baseGas :: p.gasUsed :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hsum : p.gasUsed.toNat + p.baseGas.toNat < UInt256.size)
    (hprod : p.gasTotal.toNat * (p.nativePrice I).toNat < UInt256.size)
    (htoken : p.gasToken = EVM.address 0)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hb : ptr < 2 ^ 220)
    (hov : R.length + 24 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    PaymentOutcome p evm I g s0 mem ptr ret R := by
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_7805_packed (by simp; omega) h
  have hr := safePaymentReceiverWord p I
  have hf₁ : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr := hf
  simp only [safeRuntime_block_7805_stack, safeAddressMask, solcAddrMask_clean_left hr,
    hf₁, u256_sub_self] at h₁
  by_cases hperm : I.perm = true ∨ UInt256.mul p.gasTotal (p.nativePrice I) = ⟨0⟩
  swap
  · have hpfalse : I.perm = false := by cases hpi : I.perm <;> simp_all
    have hnonzero : UInt256.mul p.gasTotal (p.nativePrice I) ≠ ⟨0⟩ :=
      fun he ↦ hperm (.inr he)
    have hstat := RD.callValueStatic h₁ hpfalse hnonzero (by native_decide) (by simp; omega)
    refine .inr (.inl ⟨hstat, ?_⟩)
    exact safePaymentNativeStatic p evm hsum (by simpa only [hee] using hprod) htoken
      (by simpa only [hee] using hpfalse) (by simpa only [hee] using hnonzero)
  obtain ⟨evm', σ', z, out, aw₂, k₂, C₂, hc, hee', hacc', hw', h₂, hout, hbound⟩ :=
    rawValueCallTraceFrom evm h₁ hee hacc hworld (by native_decide) (by simp; omega) hperm
  have hc' : callViaEVM evm (EVM.address (p.receiver evm.executionEnv))
      (Int.ofNat (UInt256.mul p.gasTotal (p.nativePrice evm.executionEnv)).toNat)
      ByteArray.empty (z, evm', out) := by
    simpa only [hee, accountAddress_roundtrip, addressOfAddress,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero] using hc
  have hout138 : out.size < 2 ^ 138 := hbound (by
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero]
    exact Nat.zero_le _)
  have hbz : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = z.toUInt256 := by cases z <;> rfl
  rw [hbz, callOutputMem_zero] at h₂
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safePaymentReturnBuffer h₂ hf
    (by change ptr + out.size + 64 < 2 ^ 256; omega) (by simp; omega)
  have hbody := safePaymentNativeSource hsum (by simpa only [hee] using hprod) htoken hc'
  have hfinish := safePaymentNativeFinish z h₃ (by omega) hret
  cases z
  · exact .inl ⟨hfinish, hbody⟩
  · obtain ⟨k₄, C₄, h₄⟩ := hfinish
    have hpres := paymentReturnMemory_preserved mem out ptr (by omega)
    have hzero : memLoad ⟨96⟩ (paymentReturnMemory mem ptr out) = ⟨0⟩ := by
      rw [memLoadReadWord, show (⟨96⟩ : UInt256).toNat = 96 from rfl,
        hpres.read 96 32 (by decide) (by omega) hm,
        ← show (⟨96⟩ : UInt256).toNat = 96 from rfl, ← memLoadReadWord, hz]
    have hbounds := paymentReturnEnd_bounds ptr out hout138
    have hsize := (paymentReturnMemory_size mem out ptr (by omega)).2
    refine .inr (.inr ⟨p.nativeFinal evm.executionEnv true out, evm', σ',
      paymentReturnMemory mem ptr out, paymentReturnEnd ptr out, out, aw₃, k₄, C₄,
      ?_, hee', hacc', hw', ?_, paymentReturnMemory_free hf (by omega), hzero,
      hbounds.1, hbounds.2, by omega, hpres⟩)
    · simpa only [paymentPrice, htoken, ite_true, hee] using hbody
    · simpa only [paymentPrice, htoken, ite_true] using h₄

end Benchmarks.Safe
