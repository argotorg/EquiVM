import Benchmarks.Safe.ViaIR.ExecTransactionExecuteTrace
import Benchmarks.Safe.ViaIR.SafeSubSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def execResultSaved (p : ExecTransactionInput) (guard hash used : UInt256)
    (z : Bool) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat p.tx.gasToken.val, UInt256.isZero p.tx.gasPrice,
    UInt256.ofNat p.tx.refundReceiver.val, UInt256.land guard solcAddrMask,
    z.toUInt256, hash, used, ⟨0⟩] ++ R

def execGasUsedFrame (locals : Store) (before after : UInt256) : Frame :=
  { contract := contract
    locals := (locals.insert "gasAfter" (uint256Value after)).insert
      "gasUsed" (uint256Value (UInt256.sub before after)) }

set_option maxRecDepth 2000 in
theorem safeExecGasUsed (p : ExecTransactionInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata locals} {guard hash before : UInt256}
    {z : Bool} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4710⟩
      (execExecutedStack p before guard hash z R)
      mem aw rdata σ k C)
    (hb : locals["gasBefore"]? = some (uint256Value before))
    (hov : R.length + 28 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ExecBlock fork config { contract := contract, locals := locals }
      evm (exectransactionTransition.body.drop 13) .reverted) ∨
    ∃ after k' C',
      (∀ result, ExecBlock fork config (execGasUsedFrame locals before after) evm
        (exectransactionTransition.body.drop 15) result →
        ExecBlock fork config { contract := contract, locals := locals } evm
          (exectransactionTransition.body.drop 13) result) ∧
      RD fork safeBytecode I g s0 ⟨4728⟩
        (execResultSaved p guard hash (UInt256.sub before after) z R)
        mem aw rdata σ k' C' := by
  let after := (g.subNat (C + 1 + 2)).toUInt256
  let f : Frame :=
    { contract := contract, locals := locals.insert "gasAfter" (uint256Value after) }
  have ha : evalExpr? config f evm (.var "gasBefore") = .ok (uint256Value before) := by
    apply evalLocalValue
    simp [f, Std.HashMap.getElem?_insert, hb]
  have hy : evalExpr? config f evm (.var "gasAfter") = .ok (uint256Value after) := by
    apply evalLocalValue
    simp [f]
  by_cases hfit : after.toNat ≤ before.toNat
  · have h₁ := safeRuntime_block_4710_fallthrough (by simp; omega)
      (ugt_zero hfit) h
    have hg : UInt256.gt (UInt256.sub before after) before = ⟨0⟩ :=
      ugt_zero (by rw [usub_toNat hfit]; omega)
    have h₂ := safeRuntime_block_4719_fallthrough (by simp; omega) hg h₁
    have hs := safeInternalSub (fork := fork) rfl ha hy hfit (retVar := "gasUsed")
    exact .inr ⟨after, _, _,
      fun _ ht ↦ .consNormal (.letGas after) (.consNormal hs ht), h₂⟩
  · have h₁ := safeRuntime_block_4710_taken (by simp; omega)
      (by rw [ugt_one (by exact Nat.lt_of_not_ge hfit)]; decide) (by jump_dest) h
    have hr := safeRuntime_block_5321 (by simp; omega) h₁
    have hs := safeInternalSubUnderflow (fork := fork) rfl ha hy (by omega) (retVar := "gasUsed")
    exact .inl ⟨hr, .consNormal (.letGas after) (.consRevert hs)⟩

end Benchmarks.Safe.ViaIR
