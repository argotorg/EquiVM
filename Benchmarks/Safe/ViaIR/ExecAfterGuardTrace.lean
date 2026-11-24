import Benchmarks.Safe.ViaIR.ExecAfterGuardMemory
import Benchmarks.Safe.ViaIR.RawValueCall
import Benchmarks.Safe.ViaIR.LocalArrays
import Benchmarks.Safe.ViaIR.IRMemoryAllocation
import Benchmarks.Safe.ViaIR.Blocks.Runtime_007
import Benchmarks.Safe.ViaIR.Blocks.Runtime_024

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 5000 in
theorem safeExecAfterGuardTrace {I g s0 σ k C aw mem rdata}
    {hash guard ptr : UInt256} {R : List UInt256} {frame : Frame}
    (z : Bool) (evm : EVM.State)
    (h : RD fork safeBytecode I g s0 ⟨4813⟩
      (UInt256.land guard solcAddrMask :: z.toUInt256 :: hash ::
        UInt256.isZero z.toUInt256 :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hg : frame.locals["guard"]? = some (.address (AccountAddress.ofUInt256 guard)))
    (hh : frame.locals["txHash"]? = some (wordBytes32Value hash))
    (hz : frame.locals["success"]? = some (.bool z))
    (hf : memLoad ⟨64⟩ mem = ptr) (hb : ptr.toNat + 68 < UInt256.size)
    (hcap : ptr.toNat < 2 ^ 64) (hov : R.length + 20 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ExecStmt fork config frame evm execAfterGuardStmt .reverted) ∨
    ∃ frame' evm' σ' mem' aw' out a b c k' C',
      ExecStmt fork config frame evm execAfterGuardStmt (.ok frame' evm') ∧
      frame'.locals["success"]? = some (.bool z) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD fork safeBytecode I g s0 ⟨4819⟩
        (a :: b :: c :: UInt256.isZero z.toUInt256 :: ⟨0⟩ :: R)
        mem' aw' out σ' k' C' := by
  have ht : AccountAddress.ofUInt256 guard =
      AccountAddress.ofUInt256 (UInt256.land guard solcAddrMask) := by
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      addressOfNat_eq_of_masked_word guard
  have he := evalLocalValue (cfg := config) (evm := evm) hg
  have hargs : evalExprs? config frame evm [.var "txHash", .var "success"] =
      .ok [wordBytes32Value hash, .bool z] := by
    simp only [evalExprs?, evalLocalValue hh, evalLocalValue hz, bind, EvalResult.bind, pure]
  by_cases hzero : UInt256.land guard solcAddrMask = ⟨0⟩
  · have h₁ := safeRuntime_block_4813_fallthrough (by simp; omega) hzero h
    have ha : AccountAddress.ofUInt256 guard = 0 := by rw [ht, hzero]; rfl
    exact .inr ⟨frame, evm, σ, mem, _, rdata, _, _, _, _, _,
      optionalCheckedCallZero (ha ▸ he), hz, hee, hacc, hworld, h₁⟩
  have hguard : AccountAddress.ofUInt256 guard ≠ 0 := by
    rw [ht]
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      maskedAddress_ne_zero_of_mask_ne_zero hzero
  have h₁ := safeRuntime_block_4813_taken (by simp; omega) hzero (by jump_dest) h
  by_cases hc : extCodeSizeWord σ (UInt256.land guard solcAddrMask) = ⟨0⟩
  · obtain ⟨_, _, h₂⟩ := safeRuntime_block_4831_taken (by simp; omega)
      (by rw [hc]; decide) (by jump_dest) h₁
    have hr := safeRuntime_block_973 (by simp; omega) h₂
    exact .inl ⟨hr, optionalCheckedCallNoCode he hguard ht
      (by simpa only [hacc] using hc)⟩
  obtain ⟨k₂, C₂, h₂⟩ := safeRuntime_block_4831_fallthrough (by simp; omega)
    (isZero_eq_zero_of_ne hc) h₁
  have hmem := safeExecAfterGuardMemory (hash := hash) z hf hb
  change memLoad (UInt256.ofNat 64) mem = ptr at hf
  have h₃ := safeRuntime_block_4842 (by simp; omega) h₂
  rw [hmem] at h₃
  simp only [safeRuntime_block_4842_stack, hf] at h₃
  obtain ⟨evm', σ', called, out, aw', k', C', hcall, he', ha', hw', h₄, _⟩ :=
    rawValueCallTraceFrom evm h₃ hee hacc hworld (by native_decide) (by simp; omega)
      (Or.inr rfl)
  rw [callOutputMem_zero] at h₄
  have htyped : typedCallViaEVM fork config evm (EVM.address (AccountAddress.ofUInt256 guard))
      "checkAfterExecution" 0 [wordBytes32Value hash, .bool z] (called, evm', out) := by
    refine ⟨(execAfterGuardMemory mem ptr hash z).readWithPadding ptr.toNat 68,
      safeExecAfterGuardEncoding mem ptr hash z, ?_⟩
    simpa only [addressOfAddress, ht] using hcall
  cases called
  · have h₅ := safeRuntime_block_4882_taken (by simp; omega) (by decide) (by jump_dest) h₄
    have hr := safeRuntime_block_4920 (by simp; omega) (by
      change 0 + out.size % UInt256.size ≤ out.size
      simpa only [Nat.zero_add] using Nat.mod_le out.size UInt256.size) h₅
    exact .inl ⟨hr, optionalCheckedCallFailure he hguard ht
      (by simpa only [hacc] using hc) hargs htyped⟩
  · have h₅ := safeRuntime_block_4882_fallthrough (by simp; omega) (by decide) h₄
    have h₆ := safeRuntime_block_4888_taken (by simp; omega) (by decide) (by jump_dest) h₅
    have h₇ := safeRuntime_block_4899 (by simp; omega) (by jump_dest) h₆
    simp only [safeRuntime_block_4899_stack] at h₇
    have hptr : UInt256.ofNat ptr.toNat = ptr := u256_ofNat_toNat _
    rw [← hptr] at h₇
    obtain ⟨aw₈, k₈, C₈, h₈⟩ := safeIRAllocateValidTrace (len := 0) h₇ (by decide)
      (by simpa only [show ABI.paddedSize 0 = 0 from rfl, Nat.add_zero] using hcap)
      (by simp; omega) (by jump_dest)
    have h₉ := safeRuntime_block_4910_fallthrough (by simp; omega) (by rfl) h₈
    have h₁₀ := safeRuntime_block_4915 (by simp; omega) (by jump_dest) h₉
    have h₁₁ := safeRuntime_block_4892 (by simp; omega) (by jump_dest) h₁₀
    refine .inr ⟨_, evm', σ', _, aw₈, out, _, _, _, _, _,
      optionalCheckedCallSuccess he hguard ht (by simpa only [hacc] using hc) hargs htyped rfl,
      ?_, he', ha', hw', h₁₁⟩
    simp [Std.HashMap.getElem?_insert, hz]

end Benchmarks.Safe.ViaIR
