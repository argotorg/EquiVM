import Benchmarks.Safe.ViaIR.ExecTransactionPaymentSource
import Benchmarks.Safe.ViaIR.ExecTransactionSuccessCheck

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def execEventSaved (guard hash paid : UInt256) (z : Bool) (R : List UInt256) :
    List UInt256 :=
  [paid, hash, UInt256.land guard solcAddrMask, z.toUInt256, hash,
    UInt256.isZero z.toUInt256, ⟨0⟩] ++ R

private theorem safeExecPaymentDiscard {I g s0 σ k C aw mem rdata}
    {a b c d : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4758⟩ (a :: b :: c :: d :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨4763⟩ R mem aw rdata σ k' C' := by
  have h₁ := evm_run h with [jumpdest, pop, pop, pop, pop]
  exact ⟨_, _, h₁⟩

set_option maxRecDepth 5000 in
theorem safeExecTransactionPayment (p : ExecTransactionInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr locals} {guard hash used : UInt256}
    {z : Bool} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4749⟩
      (execPaymentSaved p guard hash used z R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hcFields : ExecTransactionCalldataFields I.calldata p)
    (hl : ExecTransactionLocals p locals)
    (hu : locals["gasUsed"]? = some (uint256Value used))
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hb : ptr < 2 ^ 220)
    (hov : R.length + 40 ≤ 1024) :
    RDrev fork safeBytecode g s0 ∨
    (RDstatic fork safeBytecode g s0 ∧ ExecBlock fork config { contract := contract, locals := locals }
      evm (exectransactionTransition.body.drop 16) .staticViolation) ∨
    ∃ paid called evm' σ' mem' ptr' out aw' k' C',
      (∀ result, ExecBlock fork config (execPaymentFinal locals paid called) evm'
        (exectransactionTransition.body.drop 18) result →
        ExecBlock fork config { contract := contract, locals := locals } evm
          (exectransactionTransition.body.drop 16) result) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD fork safeBytecode I g s0 ⟨4763⟩ (execEventSaved guard hash paid z R)
        mem' aw' out σ' k' C' ∧
      memLoad ⟨64⟩ mem' = UInt256.ofNat ptr' ∧ memLoad ⟨96⟩ mem' = ⟨0⟩ ∧
      ptr ≤ ptr' ∧ ptr' ≤ ptr + 2 ^ 139 ∧ 128 ≤ mem'.size ∧
      (ptr < 2 ^ 64 → ptr' < 2 ^ 64) := by
  have hli : ExecTransactionLocals p (execPaymentInit locals).locals :=
    hl.set _ _ (by decide)
  have hui : (execPaymentInit locals).locals["gasUsed"]? = some (uint256Value used) := by
    simp [execPaymentInit, Std.HashMap.getElem?_insert, hu]
  have hc := safeExecPaymentCondition p evm hli
  by_cases hzero : p.tx.gasPrice = ⟨0⟩
  · have h₁ := safeRuntime_block_4749_fallthrough (by simp; omega)
      (by rw [hzero]; decide) h
    obtain ⟨k₂, C₂, h₂⟩ := safeExecPaymentDiscard h₁ (by simp; omega)
    have hs : ExecStmt fork config (execPaymentInit locals) evm execPaymentStmt
        (.ok (execPaymentFinal locals ⟨0⟩ false) evm) :=
      .iteFalse (by simpa only [hzero, ne_self_iff_false, decide_false] using hc) .nil
    exact .inr (.inr ⟨⟨0⟩, false, evm, σ, mem, ptr, rdata, _, k₂, C₂,
      fun _ ht ↦ .consNormal (safeExecPaymentInit locals evm) (.consNormal hs ht),
      hee, hacc, hworld, h₂, hf, hz, le_rfl, by omega, hm, id⟩)
  have h₁ := safeRuntime_block_4749_taken (by simp; omega)
    (by rw [isZero_eq_zero_of_ne hzero]; decide) (by jump_dest) h
  have hcond : evalExpr? config (execPaymentInit locals) evm
      (gtE (.var "gasPrice") (.intLit 0)) = .ok (.bool true) := by
    simpa only [decide_eq_true hzero] using hc
  obtain hrev | ⟨hr, hbody⟩ |
      ⟨f', evm', σ', mem', ptr', out, aw', k', C', hbody, he', ha', hw', h₃,
        hf', hz', hple, hphi, _, hpres, hcap⟩ :=
    safePaymentTrace (execPaymentInput p used) evm h₁ hee hacc hworld
      hcFields.baseGas hcFields.gasPrice hf hm hp hz hb (by simp; omega)
  · exact .inl hrev
  · have hs := safeExecPaymentCall p evm hli hui hbody
    exact .inr (.inl ⟨hr, .consNormal (safeExecPaymentInit locals evm)
      (.consStatic (.iteTrue hcond (.consStatic hs)))⟩)
  let paid := UInt256.mul (execPaymentInput p used).gasTotal
    (paymentPrice (execPaymentInput p used) I)
  have hs := safeExecPaymentCall p evm hli hui hbody
  have hstmt : ExecStmt fork config (execPaymentInit locals) evm execPaymentStmt
      (.ok (execPaymentFinal locals paid true) evm') :=
    .iteTrue hcond (.consNormal hs
      (.consNormal (safeExecPaymentAssign locals evm' paid) .nil))
  have h₄ := safeRuntime_block_5097 (by simp; omega) (by jump_dest) h₃
  obtain ⟨k₅, C₅, h₅⟩ := safeExecPaymentDiscard h₄ (by simp; omega)
  exact .inr (.inr ⟨paid, true, evm', σ', mem', ptr', out, aw', k₅, C₅,
    fun _ ht ↦ .consNormal (safeExecPaymentInit locals evm) (.consNormal hstmt ht),
    he', ha', hw', h₅, hf', hz', hple, hphi, by have := hpres.size; omega, hcap⟩)

end Benchmarks.Safe.ViaIR
