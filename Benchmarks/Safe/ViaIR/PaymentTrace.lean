import Benchmarks.Safe.ViaIR.PaymentNativeTrace
import Benchmarks.Safe.ViaIR.PaymentTokenTrace

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

theorem safePaymentTrace (p : PaymentInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr}
    {scratch₀ scratch₁ guard success hash flag : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4979⟩
      (UInt256.ofNat p.refundReceiver.val :: ⟨0⟩ :: p.gasUsed :: UInt256.ofNat p.gasToken.val ::
        scratch₀ :: scratch₁ :: guard :: success :: hash :: flag :: ⟨0⟩ :: R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hcBase : calldataWord I.calldata 164 = p.baseGas)
    (hcPrice : calldataWord I.calldata 196 = p.gasPrice)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hb : ptr < 2 ^ 220)
    (hov : R.length + 32 ≤ 1024) :
    PaymentOutcome fork p evm I g s0 mem ptr ⟨5097⟩
      (hash :: guard :: success :: hash :: flag :: ⟨0⟩ :: R) := by
  rcases safePaymentArithmetic p evm h hee hcBase hcPrice (by simp; omega) with
    hr | ⟨k₁, C₁, hsum, hprod, h₁⟩
  · exact .inl hr.1
  by_cases ht : p.gasToken = EVM.address 0
  · simp only [paymentAfterArithmeticPC, paymentPrice, if_pos ht] at h₁ hprod
    simp only [paymentArithmeticSaved, ht, ite_true, List.cons_append, List.nil_append] at h₁
    exact safePaymentNativeTrace p evm h₁ hee hacc hworld hsum hprod ht
      hf hm hp hz hb (by simp; omega)
  · simp only [paymentAfterArithmeticPC, paymentPrice, if_neg ht] at h₁ hprod
    simp only [paymentArithmeticSaved, ht, ite_false, List.cons_append, List.nil_append] at h₁
    exact safePaymentTokenTrace p evm h₁ hee hacc hworld hsum hprod ht
      hf hm hp hz hb (by simp; omega)

theorem safeInternalPayment {p : PaymentInput} {caller : Frame} {evm : EVM.State}
    {used base price token receiver : Expr} {retVar : Ident} {result : ExecResult}
    (hc : caller.contract = contract) (hi : caller.immutables = ∅)
    (hu : evalExpr? config caller evm used = .ok (uint256Value p.gasUsed))
    (hb : evalExpr? config caller evm base = .ok (uint256Value p.baseGas))
    (hp : evalExpr? config caller evm price = .ok (uint256Value p.gasPrice))
    (ht : evalExpr? config caller evm token = .ok (.address p.gasToken))
    (hr : evalExpr? config caller evm receiver = .ok (.address p.refundReceiver))
    (hbody : ExecFuncBody fork config p.frame evm handlePaymentFunction.body result) :
    ExecStmt fork config caller evm (.internalCall "handlePayment" [used, base, price, token, receiver]
      retVar) (internalCallResult caller retVar result) := by
  apply internalCallFunctionResult (callee := handlePaymentFunction)
    (argVals := [uint256Value p.gasUsed, uint256Value p.baseGas, uint256Value p.gasPrice,
      .address p.gasToken, .address p.refundReceiver]) (locals := p.args)
  · simp [evalExprs?, hu, hb, hp, ht, hr, EvalResult.bind, bind, pure]
  · rw [hc]; rfl
  · rfl
  · convert hbody using 1
    simp only [PaymentInput.frame, hc, hi]

end Benchmarks.Safe.ViaIR
