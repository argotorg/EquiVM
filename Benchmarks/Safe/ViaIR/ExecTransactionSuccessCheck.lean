import Benchmarks.Safe.ViaIR.ExecTransactionGasUsed
import Benchmarks.Safe.ViaIR.Blocks.Runtime_023

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def ExecSuccessAllowed (p : ExecTransactionInput) (z : Bool) : Prop :=
  z = true ∨ p.tx.safeTxGas ≠ ⟨0⟩ ∨ p.tx.gasPrice ≠ ⟨0⟩

instance (p : ExecTransactionInput) (z : Bool) : Decidable (ExecSuccessAllowed p z) :=
  inferInstanceAs (Decidable (z = true ∨ p.tx.safeTxGas ≠ ⟨0⟩ ∨ p.tx.gasPrice ≠ ⟨0⟩))

def execSuccessExpr : Expr :=
  orE (.var "success")
    (orE (neE (.var "safeTxGas") (.intLit 0)) (neE (.var "gasPrice") (.intLit 0)))

theorem safeExecSuccessExpr (p : ExecTransactionInput) (evm : EVM.State)
    {locals : Store} {z : Bool} (hl : ExecTransactionLocals p locals)
    (hz : locals["success"]? = some (.bool z)) :
    evalExpr? config { contract := contract, locals := locals } evm execSuccessExpr =
      .ok (.bool (decide (ExecSuccessAllowed p z))) := by
  have he (a : UInt256) : a.toNat = 0 ↔ a = ⟨0⟩ :=
    ⟨uint256_toNat_eq_zero, fun h ↦ by rw [h]; rfl⟩
  have hv (a : UInt256) : (Value.int (a.toNat : Int) == Value.int 0) =
      decide (a = ⟨0⟩) := by
    apply Bool.eq_iff_iff.mpr
    simp [beq_iff_eq, he]
  cases z <;> by_cases hs : p.tx.safeTxGas = ⟨0⟩ <;>
    simp [execSuccessExpr, orE, neE, evalExpr?, Std.HashMap.get?_eq_getElem?,
      hz, hl.tx.safeTxGas, hl.tx.gasPrice, EvalResult.ofOption,
      EvalResult.bind, bind, pure, evalBinaryOp_ne_int_ok, hv, hs, ExecSuccessAllowed]

def execPaymentSaved (p : ExecTransactionInput) (guard hash used : UInt256)
    (z : Bool) (R : List UInt256) : List UInt256 :=
  [⟨0⟩, used, UInt256.ofNat p.tx.gasToken.val, UInt256.isZero p.tx.gasPrice,
    UInt256.ofNat p.tx.refundReceiver.val, UInt256.land guard solcAddrMask, z.toUInt256,
    hash, UInt256.isZero z.toUInt256, ⟨0⟩] ++ R

set_option maxRecDepth 2000 in
theorem safeExecSuccessRoute (p : ExecTransactionInput)
    {I g s0 σ k C aw mem rdata} {guard hash used : UInt256}
    {z : Bool} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4728⟩
      (execResultSaved p guard hash used z R) mem aw rdata σ k C)
    (hc : ExecTransactionCalldataFields I.calldata p) (hov : R.length + 20 ≤ 1024) :
    ∃ flag k' C', (flag = ⟨0⟩ ↔ ExecSuccessAllowed p z) ∧
      RD fork safeBytecode I g s0 ⟨4744⟩
        (flag :: execPaymentSaved p guard hash used z R) mem aw rdata σ k' C' := by
  cases z with
  | true =>
    have h₁ := safeRuntime_block_4728_fallthrough (by simp; omega)
      (by decide) h
    have h₂ := safeRuntime_block_4738_fallthrough (by simp; omega)
      (by decide) h₁
    exact ⟨⟨0⟩, _, _, by simp [ExecSuccessAllowed], h₂⟩
  | false =>
    have h₁ := safeRuntime_block_4728_taken (by simp; omega)
      (by decide) (by jump_dest) h
    have h₂ := safeRuntime_block_5291 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_5291_stack,
      show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 132).toNat 32) =
        p.tx.safeTxGas from hc.safeTxGas] at h₂
    by_cases hs : p.tx.safeTxGas = ⟨0⟩
    · rw [hs] at h₂
      have h₃ := safeRuntime_block_4738_taken (by simp; omega)
        (by decide) (by jump_dest) h₂
      have h₄ := safeRuntime_block_5284 (by simp; omega) (by jump_dest) h₃
      refine ⟨UInt256.isZero p.tx.gasPrice, _, _, ?_, h₄⟩
      by_cases hp : p.tx.gasPrice = ⟨0⟩
      · simp [ExecSuccessAllowed, hs, hp]; decide
      · simp [ExecSuccessAllowed, hs, hp, isZero_eq_zero_of_ne hp]
    · have h₃ := safeRuntime_block_4738_fallthrough (by simp; omega)
        (isZero_eq_zero_of_ne hs) h₂
      rw [isZero_eq_zero_of_ne hs] at h₃
      exact ⟨⟨0⟩, _, _, by simp [ExecSuccessAllowed, hs], h₃⟩

set_option maxRecDepth 2000 in
theorem safeExecSuccessCheck (p : ExecTransactionInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata locals} {guard hash used : UInt256}
    {z : Bool} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4728⟩
      (execResultSaved p guard hash used z R) mem aw rdata σ k C)
    (hc : ExecTransactionCalldataFields I.calldata p)
    (hl : ExecTransactionLocals p locals) (hz : locals["success"]? = some (.bool z))
    (hov : R.length + 20 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ExecBlock fork config { contract := contract, locals := locals }
      evm (exectransactionTransition.body.drop 15) .reverted) ∨
    ∃ k' C',
      (∀ result, ExecBlock fork config { contract := contract, locals := locals } evm
        (exectransactionTransition.body.drop 16) result →
        ExecBlock fork config { contract := contract, locals := locals } evm
          (exectransactionTransition.body.drop 15) result) ∧
      RD fork safeBytecode I g s0 ⟨4749⟩ (execPaymentSaved p guard hash used z R)
        mem aw rdata σ k' C' := by
  obtain ⟨flag, k₁, C₁, hflag, h₁⟩ := safeExecSuccessRoute p h hc hov
  have he := safeExecSuccessExpr p evm hl hz
  by_cases hf : flag = ⟨0⟩
  · have h₂ := safeRuntime_block_4744_fallthrough (by simp [execPaymentSaved]; omega) hf h₁
    have hs : ExecStmt fork config { contract := contract, locals := locals } evm
        (.require execSuccessExpr) (.ok { contract := contract, locals := locals } evm) :=
      .requireTrue (by simpa only [hflag.mp hf, decide_true] using he)
    exact .inr ⟨_, _, fun _ ht ↦ .consNormal hs ht, h₂⟩
  · have h₂ := safeRuntime_block_4744_taken (by simp [execPaymentSaved]; omega)
      hf (by jump_dest) h₁
    have hr := safeRuntime_block_5272 (by simp; omega)
      (by
        change 0 + rdata.size % UInt256.size ≤ rdata.size
        simpa only [Nat.zero_add] using Nat.mod_le rdata.size UInt256.size) h₂
    have hn : ¬ ExecSuccessAllowed p z := fun hc ↦ hf (hflag.mpr hc)
    exact .inl ⟨hr, .consRevert (.requireFalse
      (by simpa only [hn, decide_false] using he))⟩

end Benchmarks.Safe.ViaIR
