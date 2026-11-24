import Benchmarks.Safe.ViaIR.ExecTransactionGasSource
import Benchmarks.Safe.ViaIR.ExecGuardCallPrepare
import Benchmarks.Safe.ViaIR.SafeAddTrace
import Benchmarks.Safe.ViaIR.Blocks.Runtime_021
import Benchmarks.Safe.ViaIR.Blocks.Runtime_022
import Benchmarks.Safe.ViaIR.Blocks.Runtime_026

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def execGasSaved (p : ExecTransactionInput) (src : Nat) (guard hash : UInt256)
    (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat p.tx.target.val, UInt256.ofNat src,
    UInt256.ofNat p.tx.refundReceiver.val, UInt256.land guard solcAddrMask,
    UInt256.ofNat p.tx.gasToken.val, hash, UInt256.ofNat p.tx.payload.size] ++ R

set_option maxRecDepth 100000 in
theorem safeExecRequiredGasTrace (p : ExecTransactionInput)
    {I g s0 σ k C aw mem rdata src} {sigPtr guard hash : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4584⟩
      (execGuardSaved p src sigPtr guard hash (⟨0⟩ :: R)) mem aw rdata σ k C)
    (hc : ExecTransactionCalldataFields I.calldata p) (hov : R.length + 32 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ¬ ExecGasFits p.tx.safeTxGas) ∨
    ∃ gas k' C', ExecGasFits p.tx.safeTxGas ∧ RD fork safeBytecode I g s0 ⟨4634⟩
      (gas :: execRequiredGas p.tx.safeTxGas :: execGasSaved p src guard hash (⟨0⟩ :: R))
      mem aw rdata σ k' C' := by
  have hword : uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 132).toNat 32) =
      p.tx.safeTxGas := hc.safeTxGas
  by_cases hfirst : p.tx.safeTxGas.toNat + 2500 < UInt256.size
  swap
  · have hgt : UInt256.gt p.tx.safeTxGas (p.tx.safeTxGas + UInt256.ofNat 2500) = ⟨1⟩ := by
      rw [u256_add_comm]
      exact checkedAddOverflowGt _ _ (by
        change UInt256.size ≤ p.tx.safeTxGas.toNat + 2500
        omega)
    have h₁ := safeRuntime_block_4584_taken (by simp; omega)
      (by rw [hword, hgt]; decide) (by jump_dest) h
    have hr := safeRuntime_block_5344 (by
      simp; omega) h₁
    exact .inl ⟨hr, fun hf ↦ hfirst hf.1⟩
  have hgt : UInt256.gt p.tx.safeTxGas (p.tx.safeTxGas + UInt256.ofNat 2500) = ⟨0⟩ := by
    rw [u256_add_comm]
    exact checkedAddNoOverflowGt _ _ hfirst
  have h₁ := safeRuntime_block_4584_fallthrough (by simp; omega)
    (by rw [hword]; exact hgt) h
  let gas := (g.subNat (C + 3 + 2)).toUInt256
  simp only [safeRuntime_block_4584_fallthrough_stack, hword] at h₁
  change RD fork safeBytecode I g s0 ⟨4612⟩
    ((p.tx.safeTxGas + ⟨2500⟩) :: execGasScaled p.tx.safeTxGas :: gas ::
      execGasSaved p src guard hash (⟨0⟩ :: R)) mem aw rdata σ _ _ at h₁
  have hmax : ∃ k' C', RD fork safeBytecode I g s0 ⟨4621⟩
      (gas :: execGasMaximum p.tx.safeTxGas :: execGasSaved p src guard hash (⟨0⟩ :: R))
      mem aw rdata σ k' C' := by
    by_cases hlt : (execGasScaled p.tx.safeTxGas).toNat < (p.tx.safeTxGas + ⟨2500⟩).toNat
    · have h₂ := safeRuntime_block_4612_taken (by simp [execGasSaved]; omega)
        (by rw [ult_one hlt]; decide) (by jump_dest) h₁
      have h₃ := safeRuntime_block_5446 (by simp [execGasSaved]; omega) (by jump_dest) h₂
      have he : execGasMaximum p.tx.safeTxGas = p.tx.safeTxGas + ⟨2500⟩ := by
        rw [execGasMaximum, maximumWord, max_eq_right (le_of_lt hlt), u256_ofNat_toNat]
      exact ⟨_, _, by simpa only [safeRuntime_block_5446_stack, he] using h₃⟩
    · have h₂ := safeRuntime_block_4612_fallthrough (by simp [execGasSaved]; omega)
        (ult_zero (by omega)) h₁
      have h₃ := safeRuntime_block_4619 (by simp [execGasSaved]; omega) h₂
      have he : execGasMaximum p.tx.safeTxGas = execGasScaled p.tx.safeTxGas := by
        rw [execGasMaximum, maximumWord, max_eq_left (by omega), u256_ofNat_toNat]
      exact ⟨_, _, by simpa only [safeRuntime_block_4619_stack, he] using h₃⟩
  obtain ⟨k₂, C₂, h₂⟩ := hmax
  by_cases hsecond : (execGasMaximum p.tx.safeTxGas).toNat + 500 < UInt256.size
  swap
  · have hgt : UInt256.gt (execGasMaximum p.tx.safeTxGas)
        (execGasMaximum p.tx.safeTxGas + UInt256.ofNat 500) = ⟨1⟩ := by
      rw [u256_add_comm]
      exact checkedAddOverflowGt _ _ (by
        change UInt256.size ≤ (execGasMaximum p.tx.safeTxGas).toNat + 500; omega)
    have h₃ := safeRuntime_block_4621_taken (by simp [execGasSaved]; omega)
      (by rw [hgt]; decide) (by jump_dest) h₂
    have hr := safeRuntime_block_5426 (by
      simp; omega) h₃
    exact .inl ⟨hr, fun hf ↦ hsecond hf.2⟩
  have hgt : UInt256.gt (execGasMaximum p.tx.safeTxGas)
      (execGasMaximum p.tx.safeTxGas + UInt256.ofNat 500) = ⟨0⟩ := by
    rw [u256_add_comm]
    exact checkedAddNoOverflowGt _ _ hsecond
  have h₃ := safeRuntime_block_4621_fallthrough (by simp [execGasSaved]; omega) hgt h₂
  exact .inr ⟨gas, _, _, ⟨hfirst, hsecond⟩, h₃⟩

end Benchmarks.Safe.ViaIR
