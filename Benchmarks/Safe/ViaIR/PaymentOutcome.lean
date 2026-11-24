import Benchmarks.Safe.ViaIR.PaymentPrepare
import Benchmarks.Safe.ViaIR.PaymentSourcePaths
import Benchmarks.Safe.ViaIR.SafeMulTrace
import Benchmarks.Safe.ViaIR.SafeAddTrace
import Benchmarks.Safe.ViaIR.MemoryPreserves

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def PaymentOutcome (fork : Ethereum.Fork) (p : PaymentInput) (evm : EVM.State) (I : ExecutionEnv) (g : Sat256)
    (s0 : State) (mem : ByteArray) (ptr : Nat) (ret : UInt256) (R : List UInt256) : Prop :=
  RDrev fork safeBytecode g s0 ∨
  (RDstatic fork safeBytecode g s0 ∧
    ExecFuncBody fork config p.frame evm handlePaymentFunction.body .staticViolation) ∨
  ∃ (f' : Frame) (evm' : EVM.State) (σ' : AccountMap) (mem' : ByteArray) (ptr' : Nat)
    (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
    ExecFuncBody fork config p.frame evm handlePaymentFunction.body
      (.returned f' evm' (some [uint256Value (UInt256.mul p.gasTotal (paymentPrice p I))])) ∧
    evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
    RD fork safeBytecode I g s0 ret (UInt256.mul p.gasTotal (paymentPrice p I) :: R)
      mem' aw' out σ' k' C' ∧
    memLoad ⟨64⟩ mem' = UInt256.ofNat ptr' ∧ memLoad ⟨96⟩ mem' = ⟨0⟩ ∧
    ptr ≤ ptr' ∧ ptr' ≤ ptr + 2 ^ 139 ∧ mem'.size ≤ max mem.size (ptr + 2 ^ 139) ∧
    MemoryPreserves mem mem' 96 ptr ∧ (ptr < 2 ^ 64 → ptr' < 2 ^ 64)

set_option maxRecDepth 5000 in
theorem safePaymentArithmetic (p : PaymentInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata} {scratch₀ scratch₁ : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4979⟩
      (UInt256.ofNat p.refundReceiver.val :: ⟨0⟩ :: p.gasUsed ::
        UInt256.ofNat p.gasToken.val :: scratch₀ :: scratch₁ :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hcBase : calldataWord I.calldata 164 = p.baseGas)
    (hcPrice : calldataWord I.calldata 196 = p.gasPrice) (hov : R.length + 24 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧
      ExecFuncBody fork config p.frame evm handlePaymentFunction.body .reverted) ∨
    ∃ k' C', p.gasUsed.toNat + p.baseGas.toNat < UInt256.size ∧
      p.gasTotal.toNat * (paymentPrice p I).toNat < UInt256.size ∧
      RD fork safeBytecode I g s0 (paymentAfterArithmeticPC p)
        (UInt256.mul p.gasTotal (paymentPrice p I) :: paymentArithmeticSaved p I R)
        mem aw rdata σ k' C' := by
  obtain ⟨k₁, C₁, h₁⟩ := safePaymentPrepare p h hcBase (by omega)
  have hstack : (paymentAddSaved p I R).length + 11 ≤ 1024 := by
    unfold paymentAddSaved
    split <;> simp <;> omega
  by_cases hs : p.gasUsed.toNat + p.baseGas.toNat < UInt256.size
  swap
  · exact .inl ⟨safeAddOverflow h₁ (Nat.le_of_not_gt hs) hstack,
      safePaymentAddOverflow p evm (Nat.le_of_not_gt hs)⟩
  have hret : (D_J safeBytecode 0).contains (paymentAddReturnPC p) = true := by
    unfold paymentAddReturnPC
    split <;> jump_dest
  obtain ⟨k₂, C₂, h₂⟩ := safeAddTrace h₁ hs hstack hret
  have hlt : UInt256.lt p.gasTotal p.gasUsed = ⟨0⟩ := by
    apply ult_zero
    change p.gasUsed.toNat ≤ (p.gasUsed.toNat + p.baseGas.toNat) % UInt256.size
    rw [Nat.mod_eq_of_lt hs]
    omega
  have hmul : ∃ k₃ C₃, RD fork safeBytecode I g s0 ⟨9466⟩
      (p.gasTotal :: paymentPrice p I :: paymentAfterArithmeticPC p ::
        paymentArithmeticSaved p I R) mem aw rdata σ k₃ C₃ := by
    by_cases ht : p.gasToken = EVM.address 0
    · simp only [paymentAddReturnPC, paymentAddSaved, ht, ite_true,
        List.cons_append, List.nil_append] at h₂
      have h₃ := safeRuntime_block_5032_fallthrough (by simp; omega) hlt h₂
      obtain ⟨k₄, C₄, h₄⟩ := safePaymentNativePriceTrace p h₃ hcPrice (by simp; omega)
      exact ⟨k₄, C₄, by simpa only [paymentPrice, paymentAfterArithmeticPC,
        paymentArithmeticSaved, ht, ite_true, List.cons_append, List.nil_append] using h₄⟩
    · simp only [paymentAddReturnPC, paymentAddSaved, ht, ite_false,
        List.cons_append, List.nil_append] at h₂
      have h₃ := safeRuntime_block_5130_fallthrough (by simp; omega) hlt h₂
      have h₄ := safeRuntime_block_5138 (by simp; omega) (by jump_dest) h₃
      change uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 196).toNat 32) =
        p.gasPrice at hcPrice
      exact ⟨_, _, by simpa only [safeRuntime_block_5138_stack, hcPrice,
        paymentPrice, paymentAfterArithmeticPC, paymentArithmeticSaved, ht, ite_false,
        PaymentInput.gasTotal, List.cons_append, List.nil_append] using h₄⟩
  obtain ⟨k₃, C₃, h₃⟩ := hmul
  have hstack' : (paymentArithmeticSaved p I R).length + 13 ≤ 1024 := by
    unfold paymentArithmeticSaved
    split <;> simp <;> omega
  by_cases hm : p.gasTotal.toNat * (paymentPrice p I).toNat < UInt256.size
  swap
  · refine .inl ⟨safeMulOverflow h₃ (Nat.le_of_not_gt hm) (by simp; omega), ?_⟩
    apply safePaymentMulOverflow p evm hs
    simpa only [hee, paymentPrice] using Nat.le_of_not_gt hm
  have hret' : (D_J safeBytecode 0).contains (paymentAfterArithmeticPC p) = true := by
    unfold paymentAfterArithmeticPC
    split <;> jump_dest
  obtain ⟨k₄, C₄, h₄⟩ := safeMulTrace h₃ hm (by omega) hret'
  exact .inr ⟨k₄, C₄, hs, hm, h₄⟩

end Benchmarks.Safe.ViaIR
