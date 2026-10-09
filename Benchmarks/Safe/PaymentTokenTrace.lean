import Benchmarks.Safe.PaymentOutcome
import Benchmarks.Safe.PaymentNativeReturn
import Benchmarks.Safe.TokenTransferTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safePaymentTokenTrace (p : PaymentInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7931⟩
      (UInt256.mul p.gasTotal p.gasPrice :: UInt256.ofNat (p.receiver I).val :: ⟨0⟩ ::
        UInt256.ofNat p.refundReceiver.val :: UInt256.ofNat p.gasToken.val :: p.gasPrice ::
        p.baseGas :: p.gasUsed :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hsum : p.gasUsed.toNat + p.baseGas.toNat < UInt256.size)
    (hprod : p.gasTotal.toNat * p.gasPrice.toNat < UInt256.size)
    (htoken : p.gasToken ≠ EVM.address 0)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hb : ptr < 2 ^ 220)
    (hov : R.length + 24 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    PaymentOutcome p evm I g s0 mem ptr ret R := by
  have h₁ := safeRuntime_block_7931 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_7931_stack] at h₁
  obtain ⟨evm', σ', z, out, aw₂, k₂, C₂, hsource, hee', hacc', hw', h₂,
      hf', hz', hpres, hsize, hout⟩ :=
    safeTokenTransferTrace (p.tokenInput I) evm h₁ hee hacc hworld hf hm hp hz
      (by change ptr + 100 < 2 ^ 256; omega) (by simp; omega) (by jump_dest)
  have hcallee : ExecFuncBody config (p.tokenInput evm.executionEnv).frame evm
      transferTokenFunction.body
      (.returned ((p.tokenInput I).finalFrame z out) evm'
        (some [.bool (tokenTransferResult z out)])) := by simpa only [hee] using hsource
  have hbody := safePaymentTokenSource hsum hprod htoken hcallee
  have hfinish := safePaymentTokenFinish (tokenTransferResult z out) h₂ (by omega) hret
  cases he : tokenTransferResult z out
  · simp only [he, Bool.false_eq_true, ite_false] at hbody hfinish
    exact .inl ⟨hfinish, hbody⟩
  · simp only [he, ite_true] at hbody hfinish
    obtain ⟨k₃, C₃, h₃⟩ := hfinish
    refine .inr (.inr ⟨p.tokenFinal evm.executionEnv true, evm', σ', _,
      ptr + 100, out, aw₂, k₃, C₃, ?_, hee', hacc', hw',
      ?_, hf', hz', by omega, by omega, ?_, hpres⟩)
    · simpa only [paymentPrice, htoken, ite_false] using hbody
    · simpa only [paymentPrice, htoken, ite_false] using h₃
    · rw [hsize]; omega

end Benchmarks.Safe
