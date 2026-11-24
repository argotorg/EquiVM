import Benchmarks.Safe.ViaIR.PaymentOutcome
import Benchmarks.Safe.ViaIR.PaymentNativeReturn
import Benchmarks.Safe.ViaIR.TokenTransferTrace

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 5000 in
theorem safePaymentTokenTrace (p : PaymentInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr} {guard success hash flag : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5152⟩
      (UInt256.mul p.gasTotal p.gasPrice :: UInt256.ofNat p.gasToken.val :: ⟨0⟩ :: ⟨32⟩ ::
        UInt256.ofNat (p.receiver I).val :: guard :: success :: hash :: flag :: ⟨0⟩ :: R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hsum : p.gasUsed.toNat + p.baseGas.toNat < UInt256.size)
    (hprod : p.gasTotal.toNat * p.gasPrice.toNat < UInt256.size)
    (htoken : p.gasToken ≠ EVM.address 0)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hb : ptr < 2 ^ 220)
    (hov : R.length + 28 ≤ 1024) :
    PaymentOutcome fork p evm I g s0 mem ptr ⟨5097⟩
      (hash :: guard :: success :: hash :: flag :: ⟨0⟩ :: R) := by
  obtain hrev | ⟨evm', σ', z, out, aw₂, k₂, C₂, hsource, hee', hacc', hw', h₂,
      hf', hz', hpres, hsize, hout, hcap⟩ :=
    safeTokenTransferTrace (p.tokenInput I) evm h hee hacc hworld hf hm hp hz
      (by change ptr + 128 < 2 ^ 256; omega) (by omega)
  · exact .inl hrev
  have hcallee : ExecFuncBody fork config (p.tokenInput evm.executionEnv).frame evm
      transferTokenFunction.body
      (.returned ((p.tokenInput I).finalFrame z out) evm'
        (some [.bool (tokenTransferResult z out)])) := by simpa only [hee] using hsource
  have hbody := safePaymentTokenSource hsum hprod htoken hcallee
  have hfinish := safePaymentTokenFinish (tokenTransferResult z out) h₂ (by simp; omega)
  cases he : tokenTransferResult z out
  · simp only [he, Bool.false_eq_true, ite_false] at hbody hfinish
    exact .inl hfinish
  · simp only [he, ite_true] at hbody hfinish
    obtain ⟨k₃, C₃, h₃⟩ := hfinish
    refine .inr (.inr ⟨p.tokenFinal evm.executionEnv true, evm', σ', _,
      ptr + 128, out, aw₂, k₃, C₃, ?_, hee', hacc', hw',
      ?_, hf', hz', by omega, by omega, ?_, hpres, fun _ ↦ hcap⟩)
    · simpa only [paymentPrice, htoken, ite_false] using hbody
    · simpa only [paymentPrice, htoken, ite_false] using h₃
    · rw [hsize]; omega

end Benchmarks.Safe.ViaIR
