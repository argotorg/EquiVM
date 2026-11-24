import Benchmarks.Safe.V1_0227664.ExecTransactionGasUsed
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_020

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V1_0227664.RuntimeBlocks

namespace Benchmarks.Safe.V1_0227664

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
      hz, hl.tx.safeTxGas, hl.tx.gasPrice, uint256Value, EvalResult.ofOption,
      EvalResult.bind, bind, pure, evalBinaryOp_ne_int_ok, hv, hs, ExecSuccessAllowed]

set_option maxRecDepth 100000 in
theorem safeExecSuccessRoute (p : ExecTransactionInput)
    {I g s0 σ k C aw mem rdata src} {sigPtr guard hash before used : UInt256}
    {z : Bool} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3767⟩
      (used :: before :: execResultSaved p src sigPtr guard hash z R) mem aw rdata σ k C)
    (hov : R.length + 20 ≤ 1024) :
    ∃ flag k' C', (flag = ⟨0⟩ ↔ ExecSuccessAllowed p z) ∧
      RD fork safeBytecode I g s0 ⟨3791⟩
        (flag :: used :: execResultSaved p src sigPtr guard hash z R) mem aw rdata σ k' C' := by
  cases z with
  | true =>
    have h₁ := safeRuntime_block_3767_taken (by simp [execResultSaved]; omega)
      (by decide) (by jump_dest) h
    have h₂ := safeRuntime_block_3781_taken (by simp [execResultSaved]; omega)
      (by decide) (by jump_dest) h₁
    exact ⟨⟨0⟩, _, _, by simp [ExecSuccessAllowed], h₂⟩
  | false =>
    have h₁ := safeRuntime_block_3767_fallthrough (by simp [execResultSaved]; omega)
      (by decide) h
    have h₂ := safeRuntime_block_3778 (by simp [execResultSaved]; omega) h₁
    change RD fork safeBytecode I g s0 _
      (UInt256.isZero p.tx.safeTxGas :: used ::
        execResultSaved p src sigPtr guard hash false R) _ _ _ _ _ _ at h₂
    by_cases hs : p.tx.safeTxGas = ⟨0⟩
    · rw [hs] at h₂
      have h₃ := safeRuntime_block_3781_fallthrough
        (by simp [execResultSaved]; omega) (by decide) h₂
      have h₄ := safeRuntime_block_3788 (by simp [execResultSaved]; omega) h₃
      refine ⟨UInt256.isZero p.tx.gasPrice, _, _, ?_, h₄⟩
      by_cases hp : p.tx.gasPrice = ⟨0⟩
      · simp [ExecSuccessAllowed, hs, hp]; decide
      · simp [ExecSuccessAllowed, hs, hp, isZero_eq_zero_of_ne hp]
    · rw [isZero_eq_zero_of_ne hs] at h₂
      have h₃ := safeRuntime_block_3781_taken (by simp [execResultSaved]; omega)
        (by decide) (by jump_dest) h₂
      exact ⟨⟨0⟩, _, _, by simp [ExecSuccessAllowed, hs], h₃⟩

set_option maxRecDepth 100000 in
theorem safeExecSuccessCheck (p : ExecTransactionInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata src locals} {sigPtr guard hash before used : UInt256}
    {z : Bool} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3767⟩
      (used :: before :: execResultSaved p src sigPtr guard hash z R) mem aw rdata σ k C)
    (hl : ExecTransactionLocals p locals) (hz : locals["success"]? = some (.bool z))
    (hov : R.length + 20 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ExecBlock fork config { contract := contract, locals := locals }
      evm (exectransactionTransition.body.drop 15) .reverted) ∨
    ∃ k' C',
      (∀ result, ExecBlock fork config { contract := contract, locals := locals } evm
        (exectransactionTransition.body.drop 16) result →
        ExecBlock fork config { contract := contract, locals := locals } evm
          (exectransactionTransition.body.drop 15) result) ∧
      RD fork safeBytecode I g s0 ⟨3807⟩
        (used :: execResultSaved p src sigPtr guard hash z R) mem aw rdata σ k' C' := by
  obtain ⟨flag, k₁, C₁, hflag, h₁⟩ := safeExecSuccessRoute p h hov
  have he := safeExecSuccessExpr p evm hl hz
  by_cases hf : flag = ⟨0⟩
  · have h₂ := safeRuntime_block_3791_taken (by simp [execResultSaved]; omega)
      (by rw [hf]; decide) (by jump_dest) h₁
    have hs : ExecStmt fork config { contract := contract, locals := locals } evm
        (.require execSuccessExpr) (.ok { contract := contract, locals := locals } evm) :=
      .requireTrue (by simpa only [hflag.mp hf, decide_true] using he)
    exact .inr ⟨_, _, fun _ ht ↦ .consNormal hs ht, h₂⟩
  · have h₂ := safeRuntime_block_3791_fallthrough (by simp [execResultSaved]; omega)
      (isZero_eq_zero_of_ne hf) h₁
    have hr := safeRuntime_block_3797
      (by simp [safeRuntime_block_3791_fallthrough_stack, execResultSaved]; omega)
      (by
        rw [show (⟨0⟩ : UInt256).toNat = 0 by rfl, Nat.zero_add]
        exact Nat.mod_le rdata.size UInt256.size) h₂
    have hn : ¬ ExecSuccessAllowed p z := fun hc ↦ hf (hflag.mpr hc)
    exact .inl ⟨hr, .consRevert (.requireFalse
      (by simpa only [hn, decide_false] using he))⟩

end Benchmarks.Safe.V1_0227664
