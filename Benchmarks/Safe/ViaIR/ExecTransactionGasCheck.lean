import Benchmarks.Safe.ViaIR.ExecTransactionGasMath

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def execCheckGasFrame (locals : Store) (gas : UInt256) : Frame :=
  { contract := contract, locals := locals.insert "gasForCheck" (uint256Value gas) }

set_option maxRecDepth 2000 in
theorem safeExecGasCheck (p : ExecTransactionInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata src locals} {sigPtr guard hash : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4584⟩
      (execGuardSaved p src sigPtr guard hash (⟨0⟩ :: R)) mem aw rdata σ k C)
    (hcFields : ExecTransactionCalldataFields I.calldata p)
    (hl : ExecTransactionLocals p locals) (hov : R.length + 32 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ExecBlock fork config { contract := contract, locals := locals }
      evm (exectransactionTransition.body.drop 8) .reverted) ∨
    ∃ gas k' C',
      (∀ result, ExecBlock fork config (execCheckGasFrame locals gas) evm
        (exectransactionTransition.body.drop 10) result →
        ExecBlock fork config { contract := contract, locals := locals } evm
          (exectransactionTransition.body.drop 8) result) ∧
      RD fork safeBytecode I g s0 ⟨4639⟩ (execGasSaved p src guard hash (⟨0⟩ :: R))
        mem aw rdata σ k' C' := by
  have hsafe (gas : UInt256) : evalExpr? config (execCheckGasFrame locals gas) evm
      (.var "safeTxGas") = .ok (uint256Value p.tx.safeTxGas) :=
    evalLocalValue ((hl.set "gasForCheck" (uint256Value gas) (by decide)).tx.safeTxGas)
  have hgas (gas : UInt256) : evalExpr? config (execCheckGasFrame locals gas) evm
      (.var "gasForCheck") = .ok (uint256Value gas) := by
    apply evalLocalValue
    simp [execCheckGasFrame]
  obtain ⟨hr, hfit⟩ | ⟨gas, k₁, C₁, hfit, h₁⟩ := safeExecRequiredGasTrace p h hcFields hov
  · have he := safeEvalExecRequiredGasRevert (hsafe ⟨0⟩) hfit
    refine .inl ⟨hr, .consNormal (.letGas ⟨0⟩) (.consRevert (.requireRevert ?_))⟩
    change evalExpr? config (execCheckGasFrame locals ⟨0⟩) evm
      (geE (.var "gasForCheck") requiredTransactionGasExpr) = .revert
    rw [geE, evalExpr_binary_nonshort (by decide) (by decide), hgas]
    simp only [bind, EvalResult.bind, he]
  have he := naturalGeSource (hgas gas) (safeEvalExecRequiredGas (hsafe gas) hfit)
  by_cases henough : (execRequiredGas p.tx.safeTxGas).toNat ≤ gas.toNat
  · have hc : UInt256.lt gas (execRequiredGas p.tx.safeTxGas) = ⟨0⟩ := ult_zero henough
    have h₂ := safeRuntime_block_4634_fallthrough (by simp [execGasSaved]; omega) hc h₁
    have hsource : ExecStmt fork config (execCheckGasFrame locals gas) evm
        (.require (geE (.var "gasForCheck") requiredTransactionGasExpr))
        (.ok (execCheckGasFrame locals gas) evm) :=
      .requireTrue (by simpa only [henough, decide_true] using he)
    exact .inr ⟨gas, _, _, fun _ ht ↦ .consNormal (.letGas gas) (.consNormal hsource ht), h₂⟩
  · have hc : UInt256.lt gas (execRequiredGas p.tx.safeTxGas) = ⟨1⟩ := ult_one (by omega)
    have h₂ := safeRuntime_block_4634_taken (by simp [execGasSaved]; omega)
      (by rw [hc]; decide) (by jump_dest) h₁
    have hr := safeRuntime_block_5381
      (by simp [safeRuntime_block_4634_taken_stack, execGasSaved]; omega) h₂
    exact .inl ⟨hr, .consNormal (.letGas gas)
      (.consRevert (.requireFalse (by simpa only [henough, decide_false] using he)))⟩

theorem safeExecGasCheckCanReject (p : ExecTransactionInput) (evm : EVM.State)
    {locals : Store} (hl : ExecTransactionLocals p locals) :
    ExecBlock fork config { contract := contract, locals := locals } evm
      (exectransactionTransition.body.drop 8) .reverted := by
  have hs : evalExpr? config (execCheckGasFrame locals ⟨0⟩) evm (.var "safeTxGas") =
      .ok (uint256Value p.tx.safeTxGas) :=
    evalLocalValue ((hl.set "gasForCheck" (uint256Value ⟨0⟩) (by decide)).tx.safeTxGas)
  have hg : evalExpr? config (execCheckGasFrame locals ⟨0⟩) evm (.var "gasForCheck") =
      .ok (uint256Value ⟨0⟩) := by
    apply evalLocalValue
    simp [execCheckGasFrame]
  by_cases hf : ExecGasFits p.tx.safeTxGas
  · have hpositive : 0 < (execRequiredGas p.tx.safeTxGas).toNat := by
      rw [execRequiredGas, uadd_toNat]
      change 0 < ((execGasMaximum p.tx.safeTxGas).toNat + 500) % UInt256.size
      rw [Nat.mod_eq_of_lt hf.2]
      omega
    have he := naturalGeSource hg (safeEvalExecRequiredGas hs hf)
    refine .consNormal (.letGas ⟨0⟩) (.consRevert (.requireFalse ?_))
    simpa only [show (⟨0⟩ : UInt256).toNat = 0 by rfl,
      Nat.not_le_of_lt hpositive, decide_false] using he
  · have he := safeEvalExecRequiredGasRevert hs hf
    refine .consNormal (.letGas ⟨0⟩) (.consRevert (.requireRevert ?_))
    change evalExpr? config (execCheckGasFrame locals ⟨0⟩) evm
      (geE (.var "gasForCheck") requiredTransactionGasExpr) = .revert
    rw [geE, evalExpr_binary_nonshort (by decide) (by decide), hg]
    simp only [bind, EvalResult.bind, he]

end Benchmarks.Safe.ViaIR
