import Benchmarks.Safe.SetupSource
import Benchmarks.Safe.SetupDecodeScalars
import Benchmarks.Safe.VoidRoutineOutcome
import Benchmarks.Safe.Blocks.Runtime_024
import Benchmarks.Safe.Blocks.Runtime_017

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeSetupPaymentTrace (evm : EVM.State)
    {I g s0 σ k C aw mem rdata n len ptr locals} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4782⟩ (setupDecodedStack I.calldata n len (ret :: R))
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hl : SetupLocals (setupCalldataInput I.calldata n len) locals)
    (hb : SetupCalldataBounds I.calldata n len)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hptr : ptr < 2 ^ 220)
    (hov : R.length + 36 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    VoidRoutineOutcome config { contract := contract, locals := locals } evm
      [setupPaymentStmt] safeBytecode I g s0 ret R := by
  let p := setupCalldataInput I.calldata n len
  by_cases hpay : p.payment = ⟨0⟩
  · have h₁ := safeRuntime_block_4782_taken (by simp; omega)
      (by change UInt256.isZero p.payment ≠ _; rw [hpay]; decide) (by jump_dest) h
    have h₂ := safeRuntime_block_2790 (by omega) hret h₁
    rw [← hacc] at h₂
    exact .success (execBlock_singleton (safeSetupPaymentSkip p evm hl hpay)) h₂
  have h₁ := safeRuntime_block_4782_fallthrough (by simp; omega)
    (isZero_eq_zero_of_ne hpay) h
  have h₂ := safeRuntime_block_4789 (by simp; omega) (by jump_dest) h₁
  have ht : UInt256.ofNat p.paymentInput.gasToken.val = p.paymentToken :=
    ((canonicalAddress_eq_address_iff _ _ hb.paymentToken).mp rfl).symm
  have hr : UInt256.ofNat p.paymentInput.refundReceiver.val = p.paymentReceiver :=
    ((canonicalAddress_eq_address_iff _ _ hb.paymentReceiver).mp rfl).symm
  have hcall : RD safeBytecode I g s0 ⟨7730⟩
      (UInt256.ofNat p.paymentInput.refundReceiver.val ::
        UInt256.ofNat p.paymentInput.gasToken.val :: p.paymentInput.gasPrice ::
        p.paymentInput.baseGas :: p.paymentInput.gasUsed :: ⟨4802⟩ ::
        setupDecodedStack I.calldata n len (ret :: R)) mem aw rdata σ
        (k + 5 + 8) (C + 20 + 28) := by
    rw [ht, hr]
    exact h₂
  obtain ⟨hrev, hs⟩ | ⟨hstatic, hs⟩ |
      ⟨f', evm', σ', mem', ptr', out, aw', k', C', hs, _, hacc', _, h₃, _⟩ :=
    safePaymentTrace p.paymentInput evm hcall hee hacc hworld hf hm hp hz hptr
      (by simp [setupDecodedStack]; omega) (by jump_dest)
  · exact .reverted (.consRevert (safeSetupPaymentCall p evm hl hpay hs)) hrev
  · exact .staticHalt (.consStatic (safeSetupPaymentCall p evm hl hpay hs)) hstatic
  · have h₄ := safeRuntime_block_4802 (by omega) hret h₃
    rw [← hacc'] at h₄
    exact .success (execBlock_singleton (safeSetupPaymentCall p evm hl hpay hs)) h₄

end Benchmarks.Safe
