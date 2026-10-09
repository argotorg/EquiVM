import Benchmarks.Safe.ExecAfterGuardMemory
import Benchmarks.Safe.RawValueCall
import Benchmarks.Safe.LocalArrays

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeExecAfterGuardTrace {I g s0 σ k C aw mem rdata}
    {paid used hash guard ptr : UInt256} {R : List UInt256} {frame : Frame}
    (z : Bool) (evm : EVM.State)
    (h : RD safeBytecode I g s0 ⟨4144⟩
      (paid :: used :: guard :: hash :: z.toUInt256 :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hg : frame.locals["guard"]? = some (.address (AccountAddress.ofUInt256 guard)))
    (hh : frame.locals["txHash"]? = some (wordBytes32Value hash))
    (hz : frame.locals["success"]? = some (.bool z))
    (hf : memLoad ⟨64⟩ mem = ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr.toNat)
    (hb : ptr.toNat + 68 < UInt256.size) (hov : R.length + 20 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ ExecStmt config frame evm execAfterGuardStmt .reverted) ∨
    ∃ frame' evm' σ' mem' aw' out k' C',
      ExecStmt config frame evm execAfterGuardStmt (.ok frame' evm') ∧
      frame'.locals["success"]? = some (.bool z) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ⟨4255⟩ (guard :: hash :: z.toUInt256 :: R)
        mem' aw' out σ' k' C' ∧
      (mem' = mem ∨ mem' = execAfterGuardMemory mem ptr hash z) := by
  have ht : AccountAddress.ofUInt256 guard =
      AccountAddress.ofUInt256 (UInt256.land guard solcAddrMask) := by
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      addressOfNat_eq_of_masked_word guard
  have he := evalLocalValue (cfg := config) (evm := evm) hg
  have hargs : evalExprs? config frame evm [.var "txHash", .var "success"] =
      .ok [wordBytes32Value hash, .bool z] := by
    simp only [evalExprs?, evalLocalValue hh, evalLocalValue hz, bind, EvalResult.bind, pure]
  by_cases hzero : UInt256.land guard solcAddrMask = ⟨0⟩
  · have h₁ := safeRuntime_block_4144_taken (by simp; omega)
      (by rw [safeAddressMask, hzero]; decide) (by jump_dest) h
    have ha : AccountAddress.ofUInt256 guard = 0 := by rw [ht, hzero]; rfl
    exact .inr ⟨frame, evm, σ, mem, _, rdata, _, _,
      optionalCheckedCallZero (ha ▸ he), hz, hee, hacc, hworld, h₁, .inl rfl⟩
  have hguard : AccountAddress.ofUInt256 guard ≠ 0 := by
    rw [ht]
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      maskedAddress_ne_zero_of_mask_ne_zero hzero
  have h₁ := safeRuntime_block_4144_fallthrough (by simp; omega)
    (by rw [safeAddressMask]; exact isZero_eq_zero_of_ne hzero) h
  by_cases hc : extCodeSizeWord σ (UInt256.land guard solcAddrMask) = ⟨0⟩
  · obtain ⟨_, _, h₂⟩ := safeRuntime_block_4162_fallthrough (by simp; omega)
      (by rw [safeAddressMask, hc]; decide) h₁
    have hr := safeRuntime_block_4229 (by
      simp only [safeRuntime_block_4162_fallthrough_stack, List.length_cons]; omega) h₂
    exact .inl ⟨hr, optionalCheckedCallNoCode he hguard ht
      (by simpa only [hacc] using hc)⟩
  obtain ⟨k₂, C₂, h₂⟩ := safeRuntime_block_4162_taken (by simp; omega)
    (by rw [safeAddressMask, isZero_eq_zero_of_ne hc]; decide) (by jump_dest) h₁
  have hmem := safeExecAfterGuardMemory (hash := hash) z hf hb
  have hfree : memLoad (UInt256.ofNat 64)
      (safeRuntime_block_4162_taken_memory (mem := mem) (x1 := hash) (x2 := z.toUInt256)) =
      ptr := by
    rw [hmem]
    exact safeExecAfterGuardMemoryFree z hf hm hp
  dsimp only [safeRuntime_block_4162_taken_memory] at hfree
  change memLoad (UInt256.ofNat 64) mem = ptr at hf
  simp only [hf] at hfree
  rw [hmem] at h₂
  simp only [safeRuntime_block_4162_taken_stack, safeAddressMask, hfree, hf] at h₂
  have hlen : UInt256.sub (UInt256.ofNat 68 + ptr) ptr = UInt256.ofNat 68 := by
    rw [u256_add_comm, word_add_sub_left]
  rw [hlen] at h₂
  have h₃ := safeRuntime_block_4232 (by simp; omega) h₂
  obtain ⟨evm', σ', called, out, aw', k', C', hcall, he', ha', hw', h₄, _⟩ :=
    rawValueCallTraceFrom evm h₃ hee hacc hworld (by native_decide) (by simp; omega)
      (Or.inr rfl)
  rw [callOutputMem_zero] at h₄
  have htyped : typedCallViaEVM config evm (EVM.address (AccountAddress.ofUInt256 guard))
      "checkAfterExecution" 0 [wordBytes32Value hash, .bool z] (called, evm', out) := by
    refine ⟨(execAfterGuardMemory mem ptr hash z).readWithPadding ptr.toNat 68,
      safeExecAfterGuardEncoding mem ptr hash z, ?_⟩
    simpa only [addressOfAddress, ht] using hcall
  cases called
  · have h₅ := safeRuntime_block_4236_fallthrough (by simp; omega) (by decide) h₄
    have hr := safeRuntime_block_4243 (by
      simp only [safeRuntime_block_4236_fallthrough_stack, List.length_cons]; omega) h₅
    exact .inl ⟨hr, optionalCheckedCallFailure he hguard ht
      (by simpa only [hacc] using hc) hargs htyped⟩
  · have h₅ := safeRuntime_block_4236_taken (by simp; omega) (by decide) (by jump_dest) h₄
    have h₆ := safeRuntime_block_4250 (by simp; omega) h₅
    refine .inr ⟨_, evm', σ', _, aw', out, _, _,
      optionalCheckedCallSuccess he hguard ht (by simpa only [hacc] using hc) hargs htyped rfl,
      ?_, he', ha', hw', h₆, .inr rfl⟩
    simp [Std.HashMap.getElem?_insert, hz]

end Benchmarks.Safe
