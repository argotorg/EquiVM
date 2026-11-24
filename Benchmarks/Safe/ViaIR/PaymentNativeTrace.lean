import Benchmarks.Safe.ViaIR.PaymentOutcome
import Benchmarks.Safe.ViaIR.PaymentNativeReturn
import Benchmarks.Safe.ViaIR.RawValueCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000 in
theorem safePaymentNativeTrace (p : PaymentInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr} {guard success hash : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5066⟩
      (UInt256.mul p.gasTotal (p.nativePrice I) :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        UInt256.ofNat (p.receiver I).val :: guard :: success :: hash :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hsum : p.gasUsed.toNat + p.baseGas.toNat < UInt256.size)
    (hprod : p.gasTotal.toNat * (p.nativePrice I).toNat < UInt256.size)
    (htoken : p.gasToken = EVM.address 0)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hb : ptr < 2 ^ 220)
    (hov : R.length + 28 ≤ 1024) :
    PaymentOutcome fork p evm I g s0 mem ptr ⟨5097⟩ (hash :: guard :: success :: hash :: R) := by
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_5066_packed (by simp; omega) h
  have hr := safePaymentReceiverWord p I
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := rfl
  simp only [safeRuntime_block_5066_stack, hmask, solcAddrMask_clean_left hr] at h₁
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
  have hc' : callViaEVM fork evm (EVM.address (p.receiver evm.executionEnv))
      (Int.ofNat (UInt256.mul p.gasTotal (p.nativePrice evm.executionEnv)).toNat)
      ByteArray.empty (z, evm', out) := by
    simpa only [hee, accountAddress_roundtrip, addressOfAddress,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero] using hc
  have hout138 : out.size < 2 ^ 138 := hbound (by
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero]
    exact Nat.zero_le _)
  have hbz : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = z.toUInt256 := by cases z <;> rfl
  rw [hbz, callOutputMem_zero] at h₂
  have h₂' := safeRuntime_block_5081 (by simp; omega) (by jump_dest) h₂
  simp only [safeRuntime_block_5081_stack] at h₂'
  obtain hrev | ⟨aw₃, k₃, C₃, h₃, hcap⟩ := safePaymentReturnBuffer h₂' hf
    (by change ptr + out.size + 64 < 2 ^ 256; omega) (by simp; omega) (by jump_dest)
  · exact .inl hrev
  have hbody := safePaymentNativeSource (fork := fork) (hperm := by simpa only [hee, or_comm] using hperm) hsum (by simpa only [hee] using hprod) htoken hc'
  have hfinish := safePaymentNativeFinish z h₃ (by omega)
  cases z
  · exact .inl hfinish
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
      hbounds.1, hbounds.2, by omega, hpres, hcap⟩)
    · simpa only [paymentPrice, htoken, ite_true, hee] using hbody
    · simpa only [paymentPrice, htoken, ite_true] using h₄

end Benchmarks.Safe.ViaIR
