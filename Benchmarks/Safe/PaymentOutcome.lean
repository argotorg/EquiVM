import Benchmarks.Safe.PaymentPrepare
import Benchmarks.Safe.PaymentSourcePaths
import Benchmarks.Safe.SafeMulTrace
import Benchmarks.Safe.MemoryPreserves

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def PaymentOutcome (p : PaymentInput) (evm : EVM.State) (I : ExecutionEnv) (g : Sat256)
    (s0 : State) (mem : ByteArray) (ptr : Nat) (ret : UInt256) (R : List UInt256) : Prop :=
  (RDrev safeBytecode g s0 ∧
    ExecFuncBody config p.frame evm handlePaymentFunction.body .reverted) ∨
  (RDstatic safeBytecode g s0 ∧
    ExecFuncBody config p.frame evm handlePaymentFunction.body .staticViolation) ∨
  ∃ (f' : Frame) (evm' : EVM.State) (σ' : AccountMap) (mem' : ByteArray) (ptr' : Nat)
    (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
    ExecFuncBody config p.frame evm handlePaymentFunction.body
      (.returned f' evm' (some [uint256Value (UInt256.mul p.gasTotal (paymentPrice p I))])) ∧
    evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
    RD safeBytecode I g s0 ret (UInt256.mul p.gasTotal (paymentPrice p I) :: R)
      mem' aw' out σ' k' C' ∧
    memLoad ⟨64⟩ mem' = UInt256.ofNat ptr' ∧ memLoad ⟨96⟩ mem' = ⟨0⟩ ∧
    ptr ≤ ptr' ∧ ptr' ≤ ptr + 2 ^ 139 ∧ mem'.size ≤ max mem.size (ptr + 2 ^ 139) ∧
    MemoryPreserves mem mem' 96 ptr

set_option maxRecDepth 100000 in
theorem safePaymentArithmetic (p : PaymentInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7730⟩
      (UInt256.ofNat p.refundReceiver.val :: UInt256.ofNat p.gasToken.val :: p.gasPrice ::
        p.baseGas :: p.gasUsed :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hov : R.length + 24 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧
      ExecFuncBody config p.frame evm handlePaymentFunction.body .reverted) ∨
    ∃ k' C', p.gasUsed.toNat + p.baseGas.toNat < UInt256.size ∧
      p.gasTotal.toNat * (paymentPrice p I).toNat < UInt256.size ∧
      RD safeBytecode I g s0 (paymentAfterArithmeticPC p)
        (UInt256.mul p.gasTotal (paymentPrice p I) :: UInt256.ofNat (p.receiver I).val ::
          ⟨0⟩ :: UInt256.ofNat p.refundReceiver.val :: UInt256.ofNat p.gasToken.val ::
          p.gasPrice :: p.baseGas :: p.gasUsed :: ret :: R) mem aw rdata σ k' C' := by
  obtain ⟨k₁, C₁, h₁⟩ := safePaymentPrepare p h (by omega)
  by_cases hs : p.gasUsed.toNat + p.baseGas.toNat < UInt256.size
  swap
  · exact .inl ⟨safeAddOverflow h₁ (Nat.le_of_not_gt hs) (by simp; omega),
      safePaymentAddOverflow p evm (Nat.le_of_not_gt hs)⟩
  obtain ⟨k₂, C₂, h₂⟩ := safeAddTrace h₁ hs (by simp; omega) (by jump_dest)
  have h₃ := safeRuntime_block_7799 (by simp; omega) (by jump_dest) h₂
  simp only [safeRuntime_block_7799_stack] at h₃
  by_cases hm : p.gasTotal.toNat * (paymentPrice p I).toNat < UInt256.size
  swap
  · refine .inl ⟨safeMulOverflow h₃ (Nat.le_of_not_gt hm) (by simp; omega), ?_⟩
    apply safePaymentMulOverflow p evm hs
    simpa only [hee, paymentPrice] using Nat.le_of_not_gt hm
  have hret : (D_J safeBytecode 0).contains (paymentAfterArithmeticPC p) = true := by
    unfold paymentAfterArithmeticPC
    split <;> jump_dest
  obtain ⟨k₄, C₄, h₄⟩ := safeMulTrace h₃ hm (by simp; omega) hret
  exact .inr ⟨k₄, C₄, hs, hm, h₄⟩

end Benchmarks.Safe
