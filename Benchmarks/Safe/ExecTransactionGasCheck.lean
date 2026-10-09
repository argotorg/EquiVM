import Benchmarks.Safe.ExecTransactionGasMath

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def execCheckGasFrame (locals : Store) (gas : UInt256) : Frame :=
  { contract := contract, locals := locals.insert "gasForCheck" (uint256Value gas) }

set_option maxRecDepth 100000 in
theorem safeExecGasCheck (p : ExecTransactionInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata src locals} {sigPtr guard hash : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3758⟩
      (execGuardSaved p src sigPtr guard hash R) mem aw rdata σ k C)
    (hl : ExecTransactionLocals p locals) (hov : R.length + 32 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ ExecBlock config { contract := contract, locals := locals }
      evm (exectransactionTransition.body.drop 8) .reverted) ∨
    ∃ gas k' C',
      (∀ result, ExecBlock config (execCheckGasFrame locals gas) evm
        (exectransactionTransition.body.drop 10) result →
        ExecBlock config { contract := contract, locals := locals } evm
          (exectransactionTransition.body.drop 8) result) ∧
      RD safeBytecode I g s0 ⟨3830⟩ (execGuardSaved p src sigPtr guard hash R)
        mem aw rdata σ k' C' := by
  have hsafe (gas : UInt256) : evalExpr? config (execCheckGasFrame locals gas) evm
      (.var "safeTxGas") = .ok (uint256Value p.tx.safeTxGas) :=
    evalLocalValue ((hl.set "gasForCheck" (uint256Value gas) (by decide)).tx.safeTxGas)
  have hgas (gas : UInt256) : evalExpr? config (execCheckGasFrame locals gas) evm
      (.var "gasForCheck") = .ok (uint256Value gas) := by
    apply evalLocalValue
    simp [execCheckGasFrame, Std.HashMap.getElem_insert]
  obtain ⟨hr, hfit⟩ | ⟨k₁, C₁, hfit, h₁⟩ := safeExecRequiredGasTrace p h hov
  · have he := safeEvalExecRequiredGasRevert (hsafe ⟨0⟩) hfit
    refine .inl ⟨hr, .consNormal (.letGas ⟨0⟩) (.consRevert (.requireRevert ?_))⟩
    change evalExpr? config (execCheckGasFrame locals ⟨0⟩) evm
      (geE (.var "gasForCheck") requiredTransactionGasExpr) = .revert
    rw [geE, evalExpr_binary_nonshort (by decide) (by decide), hgas]
    simp only [bind, EvalResult.bind, he]
  let gas := (g.subNat (C₁ + 1 + 2)).toUInt256
  have he := naturalGeSource (hgas gas) (safeEvalExecRequiredGas (hsafe gas) hfit)
  by_cases henough : (execRequiredGas p.tx.safeTxGas).toNat ≤ gas.toNat
  · have hc : UInt256.lt gas (execRequiredGas p.tx.safeTxGas) = ⟨0⟩ := ult_zero henough
    have h₂ := safeRuntime_block_3806_taken (by simp [execGuardSaved]; omega)
      (by rw [hc]; decide) (by jump_dest) h₁
    have hsource : ExecStmt config (execCheckGasFrame locals gas) evm
        (.require (geE (.var "gasForCheck") requiredTransactionGasExpr))
        (.ok (execCheckGasFrame locals gas) evm) :=
      .requireTrue (by simpa only [henough, decide_true] using he)
    exact .inr ⟨gas, _, _, fun _ ht ↦ .consNormal (.letGas gas) (.consNormal hsource ht), h₂⟩
  · have hc : UInt256.lt gas (execRequiredGas p.tx.safeTxGas) = ⟨1⟩ := ult_one (by omega)
    have h₂ := safeRuntime_block_3806_fallthrough (by simp [execGuardSaved]; omega)
      (by rw [hc]; decide) h₁
    have h₃ := safeRuntime_block_3814
      (by simp [safeRuntime_block_3806_fallthrough_stack, execGuardSaved]; omega)
      (by jump_dest) h₂
    have hr := safeRuntime_block_6898
      (by simp [safeRuntime_block_3806_fallthrough_stack, execGuardSaved]; omega) h₃
    exact .inl ⟨hr, .consNormal (.letGas gas)
      (.consRevert (.requireFalse (by simpa only [henough, decide_false] using he)))⟩

end Benchmarks.Safe
