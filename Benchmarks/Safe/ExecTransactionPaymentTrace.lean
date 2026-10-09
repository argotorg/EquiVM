import Benchmarks.Safe.ExecTransactionPaymentSource
import Benchmarks.Safe.ExecTransactionGasUsed

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeExecTransactionPayment (p : ExecTransactionInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata src ptr locals} {sigPtr guard hash used : UInt256}
    {z : Bool} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3993⟩
      (used :: execResultSaved p src sigPtr guard hash z R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hl : ExecTransactionLocals p locals)
    (hu : locals["gasUsed"]? = some (uint256Value used))
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hb : ptr < 2 ^ 220)
    (hov : R.length + 40 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ ExecBlock config { contract := contract, locals := locals }
      evm (exectransactionTransition.body.drop 16) .reverted) ∨
    (RDstatic safeBytecode g s0 ∧ ExecBlock config { contract := contract, locals := locals }
      evm (exectransactionTransition.body.drop 16) .staticViolation) ∨
    ∃ paid called evm' σ' mem' ptr' out aw' k' C',
      (∀ result, ExecBlock config (execPaymentFinal locals paid called) evm'
        (exectransactionTransition.body.drop 18) result →
        ExecBlock config { contract := contract, locals := locals } evm
          (exectransactionTransition.body.drop 16) result) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ⟨4016⟩
        (paid :: used :: execResultSaved p src sigPtr guard hash z R)
        mem' aw' out σ' k' C' ∧
      memLoad ⟨64⟩ mem' = UInt256.ofNat ptr' ∧ memLoad ⟨96⟩ mem' = ⟨0⟩ ∧
      ptr ≤ ptr' ∧ ptr' ≤ ptr + 2 ^ 139 ∧ 128 ≤ mem'.size := by
  have hli : ExecTransactionLocals p (execPaymentInit locals).locals :=
    hl.set _ _ (by decide)
  have hui : (execPaymentInit locals).locals["gasUsed"]? = some (uint256Value used) := by
    simp [execPaymentInit, Std.HashMap.getElem?_insert, hu]
  have hc := safeExecPaymentCondition p evm hli
  by_cases hzero : p.tx.gasPrice = ⟨0⟩
  · have h₁ := safeRuntime_block_3993_taken (by simp [execResultSaved]; omega)
      (by rw [hzero]; decide) (by jump_dest) h
    have hs : ExecStmt config (execPaymentInit locals) evm execPaymentStmt
        (.ok (execPaymentFinal locals ⟨0⟩ false) evm) :=
      .iteFalse (by simpa only [hzero, ne_self_iff_false, decide_false] using hc) .nil
    exact .inr (.inr ⟨⟨0⟩, false, evm, σ, mem, ptr, rdata, _, _, _,
      fun _ ht ↦ .consNormal (safeExecPaymentInit locals evm) (.consNormal hs ht),
      hee, hacc, hworld, h₁, hf, hz, le_rfl, by omega, hm⟩)
  have h₁ := safeRuntime_block_3993_fallthrough (by simp [execResultSaved]; omega)
    (isZero_eq_zero_of_ne hzero) h
  have h₂ := safeRuntime_block_4001 (by simp [execResultSaved]; omega) (by jump_dest) h₁
  have hcond : evalExpr? config (execPaymentInit locals) evm
      (gtE (.var "gasPrice") (.intLit 0)) = .ok (.bool true) := by
    simpa only [decide_eq_true hzero] using hc
  obtain ⟨hr, hbody⟩ | ⟨hr, hbody⟩ |
      ⟨f', evm', σ', mem', ptr', out, aw', k', C', hbody, he', ha', hw', h₃,
        hf', hz', hple, hphi, _, hpres⟩ :=
    safePaymentTrace (execPaymentInput p used) evm h₂ hee hacc hworld hf hm hp hz hb
      (by simp [execResultSaved]; omega) (by jump_dest)
  · have hs := safeExecPaymentCall p evm hli hui hbody
    exact .inl ⟨hr, .consNormal (safeExecPaymentInit locals evm)
      (.consRevert (.iteTrue hcond (.consRevert hs)))⟩
  · have hs := safeExecPaymentCall p evm hli hui hbody
    exact .inr (.inl ⟨hr, .consNormal (safeExecPaymentInit locals evm)
      (.consStatic (.iteTrue hcond (.consStatic hs)))⟩)
  let paid := UInt256.mul (execPaymentInput p used).gasTotal
    (paymentPrice (execPaymentInput p used) I)
  have hs := safeExecPaymentCall p evm hli hui hbody
  have hstmt : ExecStmt config (execPaymentInit locals) evm execPaymentStmt
      (.ok (execPaymentFinal locals paid true) evm') :=
    .iteTrue hcond (.consNormal hs
      (.consNormal (safeExecPaymentAssign locals evm' paid) .nil))
  have h₄ := safeRuntime_block_4013 (by simp [execResultSaved]; omega) h₃
  exact .inr (.inr ⟨paid, true, evm', σ', mem', ptr', out, aw', _, _,
    fun _ ht ↦ .consNormal (safeExecPaymentInit locals evm) (.consNormal hstmt ht),
    he', ha', hw', h₄, hf', hz', hple, hphi, by have := hpres.size; omega⟩)

end Benchmarks.Safe
