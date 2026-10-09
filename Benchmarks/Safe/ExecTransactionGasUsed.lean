import Benchmarks.Safe.ExecTransactionExecuteTrace
import Benchmarks.Safe.SafeSubSource
import Benchmarks.Safe.SafeSubTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def execResultSaved (p : ExecTransactionInput) (src : Nat)
    (sigPtr guard hash : UInt256) (z : Bool) (R : List UInt256) : List UInt256 :=
  [guard, hash, z.toUInt256, sigPtr, UInt256.ofNat p.tx.refundReceiver.val,
    UInt256.ofNat p.tx.gasToken.val, p.tx.gasPrice, p.tx.baseGas, p.tx.safeTxGas, p.tx.operation,
    UInt256.ofNat p.tx.payload.size, UInt256.ofNat src, p.tx.value,
    UInt256.ofNat p.tx.target.val] ++ R

def execGasUsedFrame (locals : Store) (before after : UInt256) : Frame :=
  { contract := contract
    locals := (locals.insert "gasAfter" (uint256Value after)).insert
      "gasUsed" (uint256Value (UInt256.sub before after)) }

set_option maxRecDepth 100000 in
theorem safeExecGasUsed (p : ExecTransactionInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata src locals} {sigPtr guard hash before : UInt256}
    {z : Bool} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3940⟩
      (z.toUInt256 :: before :: execGuardSaved p src sigPtr guard hash R)
      mem aw rdata σ k C)
    (hb : locals["gasBefore"]? = some (uint256Value before))
    (hov : R.length + 28 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ ExecBlock config { contract := contract, locals := locals }
      evm (exectransactionTransition.body.drop 13) .reverted) ∨
    ∃ after k' C',
      (∀ result, ExecBlock config (execGasUsedFrame locals before after) evm
        (exectransactionTransition.body.drop 15) result →
        ExecBlock config { contract := contract, locals := locals } evm
          (exectransactionTransition.body.drop 13) result) ∧
      RD safeBytecode I g s0 ⟨3953⟩
        (UInt256.sub before after :: before :: execResultSaved p src sigPtr guard hash z R)
        mem aw rdata σ k' C' := by
  let after := (g.subNat (C + 9 + 2)).toUInt256
  have h₁ := safeRuntime_block_3940 (by simp [execGuardSaved]; omega) (by jump_dest) h
  change RD safeBytecode I g s0 _
    (after :: before :: ⟨3953⟩ :: before :: execResultSaved p src sigPtr guard hash z R)
    _ _ _ _ _ _ at h₁
  let f : Frame :=
    { contract := contract, locals := locals.insert "gasAfter" (uint256Value after) }
  have ha : evalExpr? config f evm (.var "gasBefore") = .ok (uint256Value before) := by
    apply evalLocalValue
    simp [f, Std.HashMap.getElem?_insert, hb]
  have hy : evalExpr? config f evm (.var "gasAfter") = .ok (uint256Value after) := by
    apply evalLocalValue
    simp [f]
  by_cases hfit : after.toNat ≤ before.toNat
  · obtain ⟨k₂, C₂, h₂⟩ := safeSubTrace h₁ hfit (by simp [execResultSaved]; omega)
      (by jump_dest)
    have hs := safeInternalSub rfl ha hy hfit (retVar := "gasUsed")
    exact .inr ⟨after, k₂, C₂,
      fun _ ht ↦ .consNormal (.letGas after) (.consNormal hs ht), h₂⟩
  · have hr := safeSubUnderflow h₁ (by omega) (by simp [execResultSaved]; omega)
    have hs := safeInternalSubUnderflow rfl ha hy (by omega) (retVar := "gasUsed")
    exact .inl ⟨hr, .consNormal (.letGas after) (.consRevert hs)⟩

end Benchmarks.Safe
