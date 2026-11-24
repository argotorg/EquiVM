import Benchmarks.Safe.ViaIR.ExecGuardCallPrepare
import Benchmarks.Safe.ViaIR.ExecGuardSource
import Benchmarks.Safe.ViaIR.IRMemoryAllocation
import Benchmarks.Safe.ViaIR.RawValueCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000 in
theorem safeExecGuardCallTrace (p : ExecTransactionInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src sigPtr locals} {guard hash : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5454⟩
      (execGuardSaved p src (UInt256.ofNat sigPtr) guard hash (⟨0⟩ :: R))
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hcFields : ExecTransactionCalldataFields I.calldata p)
    (hl : ExecTransactionLocals p locals)
    (hg : locals["guard"]? = some (.address (AccountAddress.ofUInt256 guard)))
    (hz : UInt256.land guard solcAddrMask ≠ ⟨0⟩)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hsig : BytesMemory mem sigPtr p.signatures)
    (ha : sigPtr + 32 + p.signatures.size ≤ ptr) (hptr : ptr < 2 ^ 64)
    (hin : src + p.tx.payload.size ≤ I.calldata.size)
    (hd : I.calldata.extract src (src + p.tx.payload.size) = p.tx.payload)
    (hs : src < UInt256.size)
    (hb : ptr + 452 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size <
      UInt256.size)
    (ho : p.tx.operation.toNat < 2) (hov : R.length + 48 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ExecStmt fork config { contract := contract, locals := locals }
      evm execGuardCheck .reverted) ∨
    ∃ evm' words aw' out k' C',
      ExecStmt fork config { contract := contract, locals := locals } evm execGuardCheck
        (.ok { contract := contract
               locals := locals.insert "_guardChecked" (collapseReturns []) } evm') ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧
      words.length = (p.signatures.size + 31) / 32 ∧
      RD fork safeBytecode I g s0 ⟨4584⟩
        (execGuardSaved p src ⟨0⟩ guard hash (⟨0⟩ :: R))
        (writeWord
          (execGuardCallMemory I.calldata mem ptr src p (UInt256.ofNat I.source.val) words)
          64 (UInt256.ofNat ptr)) aw' out evm'.accountMap k' C' := by
  have ht : AccountAddress.ofUInt256 guard =
      AccountAddress.ofUInt256 (UInt256.land guard solcAddrMask) := by
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      addressOfNat_eq_of_masked_word guard
  have hguard : AccountAddress.ofUInt256 guard ≠ 0 := by
    rw [ht]
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      maskedAddress_ne_zero_of_mask_ne_zero hz
  have he : evalExpr? config { contract := contract, locals := locals } evm (.var "guard") =
      .ok (.address (AccountAddress.ofUInt256 guard)) := evalLocalValue hg
  have hargs := safeExecGuardArguments p evm hl
  by_cases hc : extCodeSizeWord σ (UInt256.land guard solcAddrMask) = ⟨0⟩
  · obtain ⟨_, _, h₁⟩ := safeRuntime_block_5454_taken
      (by simp; omega) (by rw [hc]; decide) (by jump_dest) h
    have hr := safeRuntime_block_111 (by simp; omega) h₁
    exact .inl ⟨hr, optionalCheckedCallNoCode he hguard ht (by simpa only [hacc] using hc)⟩
  obtain ⟨_, _, h₁⟩ := safeRuntime_block_5454_fallthrough
    (by simp; omega) (isZero_eq_zero_of_ne hc) h
  obtain ⟨words, _, _, _, _, hn, hp, h₂⟩ :=
    safeExecGuardCallPrepare p h₁ hcFields hf hsig ha hin hs hb ho (by simp; omega)
  obtain ⟨evm', σ', called, out, aw', k', C', hcall, hee', hacc', hw', h₃, _⟩ :=
    rawValueCallTraceFrom evm h₂ hee hacc hworld (by native_decide)
      (by simp [execGuardSaved]; omega) (Or.inr rfl)
  rw [callOutputMem_zero] at h₃
  let count := 420 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size
  have htyped : typedCallViaEVM fork config evm (EVM.address (AccountAddress.ofUInt256 guard))
      "checkTransaction" 0 (execGuardArguments p evm.executionEnv.source)
      (called, evm', out) := by
    refine ⟨(execGuardCallMemory I.calldata mem ptr src p
      (UInt256.ofNat I.source.val) words).readWithPadding ptr count, ?_, ?_⟩
    · rw [hee, safeExecGuardCallEncoding p I.source (by omega)]
      congr 1
      exact (execGuardCallMemory_read I.calldata mem ptr src p
        (UInt256.ofNat I.source.val) words hin hd hn hp).symm
    · simpa only [addressOfAddress, ht, ulit_toNat' ptr (by omega), count,
        ulit_toNat' (420 + ABI.paddedSize p.tx.payload.size +
          ABI.paddedSize p.signatures.size) (by omega)] using hcall
  cases called
  · have h₄ := safeRuntime_block_5651_taken (by simp [execGuardSaved]; omega)
      (by decide) (by jump_dest) h₃
    have hr := safeRuntime_block_5682 (by simp [execGuardSaved]; omega) (by
      change 0 + out.size % UInt256.size ≤ out.size
      simpa only [Nat.zero_add] using Nat.mod_le out.size UInt256.size) h₄
    exact .inl ⟨hr, optionalCheckedCallFailure he hguard ht
      (by simpa only [hacc] using hc) hargs htyped⟩
  · have h₄ := safeRuntime_block_5651_fallthrough (by simp [execGuardSaved]; omega)
      (by decide) h₃
    have h₅ := safeRuntime_block_5657_fallthrough (by simp [execGuardSaved]; omega)
      (by decide) h₄
    have h₆ := safeRuntime_block_5662 (by simp; omega) (by jump_dest) h₅
    simp only [safeRuntime_block_5662_stack] at h₆
    obtain ⟨aw₇, k₇, C₇, h₇⟩ := safeIRAllocateValidTrace (len := 0) h₆ (by decide)
      (by simpa only [show ABI.paddedSize 0 = 0 by decide, Nat.add_zero] using hptr)
      (by simp; omega) (by jump_dest)
    simp only [show ABI.paddedSize 0 = 0 by decide, Nat.add_zero] at h₇
    have h₈ := safeRuntime_block_5674 (by simp; omega) (by jump_dest) h₇
    rw [← hacc'] at h₈
    exact .inr ⟨evm', words, aw₇, out, _, _, optionalCheckedCallSuccess he hguard ht
      (by simpa only [hacc] using hc) hargs htyped rfl, hee', hw', hn, h₈⟩

end Benchmarks.Safe.ViaIR
