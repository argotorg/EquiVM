import Benchmarks.Safe.ViaIR.PostModuleMemory
import Benchmarks.Safe.ViaIR.RawValueCall
import Benchmarks.Safe.ViaIR.Decoders
import Benchmarks.Safe.ViaIR.IRMemoryAllocation
import Benchmarks.Safe.ViaIR.Blocks.Runtime_027
import Benchmarks.Safe.ViaIR.Blocks.Runtime_046

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safePostModuleCheckTrace {I g s0 σ k C aw mem rdata}
    {hash guard ptr ret : UInt256} {R : List UInt256} (z : Bool) (evm : EVM.State)
    (h : RD fork safeBytecode I g s0 ⟨10191⟩
      (guard :: hash :: z.toUInt256 :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hf : memLoad ⟨64⟩ mem = ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr.toNat)
    (hb : ptr.toNat + 68 < UInt256.size) (hov : R.length + 16 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧
      (ExecStmt fork config (postModuleFrame (AccountAddress.ofUInt256 guard) hash z) evm
        postModuleCheck .reverted ∨ UInt256.land guard solcAddrMask ≠ ⟨0⟩)) ∨
    ∃ frame evm' σ' mem' aw' rdata' scratch₁ scratch₂ k' C',
      ExecStmt fork config (postModuleFrame (AccountAddress.ofUInt256 guard) hash z) evm
        postModuleCheck (.ok frame evm') ∧
      frame.locals["success"]? = some (.bool z) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD fork safeBytecode I g s0 ⟨10210⟩
        (scratch₁ :: scratch₂ :: z.toUInt256 :: ⟨0⟩ :: ret :: R)
        mem' aw' rdata' σ' k' C' ∧
      (mem' = mem ∨ mem' = postModuleReturnMemory mem ptr hash z) := by
  have ht : AccountAddress.ofUInt256 guard =
      AccountAddress.ofUInt256 (UInt256.land guard solcAddrMask) := by
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      addressOfNat_eq_of_masked_word guard
  by_cases hz : UInt256.land guard solcAddrMask = ⟨0⟩
  · have h₁ := safeRuntime_block_10191_fallthrough (by simp; omega)
      (by rw [safeAddressMask, u256_land_comm solcAddrMask guard]; exact hz) h
    have ha : AccountAddress.ofUInt256 guard = 0 := by rw [ht, hz]; rfl
    refine .inr ⟨postModuleFrame 0 hash z, evm, σ, mem, _, rdata, _, _, _, _, ?_, ?_,
      hee, hacc, hworld, h₁, .inl rfl⟩
    · simpa only [ha] using safePostModuleCheckZero evm hash z
    · simp [postModuleFrame, postModuleArgs, Std.HashMap.getElem_insert]
  have hguard : AccountAddress.ofUInt256 guard ≠ 0 := by
    rw [ht]
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      maskedAddress_ne_zero_of_mask_ne_zero hz
  have h₁ := safeRuntime_block_10191_taken (by simp; omega)
    (by rw [safeAddressMask, u256_land_comm solcAddrMask guard]; exact hz) (by jump_dest) h
  simp only [safeRuntime_block_10191_taken_stack, safeAddressMask,
    u256_land_comm solcAddrMask guard] at h₁
  by_cases hc : extCodeSizeWord σ (UInt256.land guard solcAddrMask) = ⟨0⟩
  · obtain ⟨_, _, h₂⟩ := safeRuntime_block_10295_taken (by simp; omega)
      (by rw [hc]; decide) (by jump_dest) h₁
    have hr := safeRuntime_block_111 (by simp; omega) h₂
    exact .inl ⟨hr, .inl (safePostModuleCheckNoCode hguard ht
      (by simpa only [hacc] using hc))⟩
  obtain ⟨k₂, C₂, h₂⟩ := safeRuntime_block_10295_fallthrough (by simp; omega)
    (isZero_eq_zero_of_ne hc) h₁
  have hmem := safePostModuleMemory (hash := hash) z hf hb
  change memLoad (UInt256.ofNat 64) mem = ptr at hf
  have h₃ := safeRuntime_block_10303 (by simp; omega) h₂
  rw [hmem] at h₃
  simp only [safeRuntime_block_10303_stack, hf] at h₃
  obtain ⟨evm', σ', called, out, aw', k', C', hcall, he, ha, hw, h₄, _⟩ :=
    rawValueCallTraceFrom evm h₃ hee hacc hworld (by native_decide) (by simp; omega)
      (Or.inr rfl)
  rw [callOutputMem_zero] at h₄
  have htyped : typedCallViaEVM fork config evm
      (EVM.address (AccountAddress.ofUInt256 guard)) "checkAfterModuleExecution" 0
      [.fixedBytes bytes32Width (EVM.Word.toBytesBE hash), .bool z] (called, evm', out) := by
    refine ⟨_, safePostModuleEncoding mem ptr hash z, ?_⟩
    simpa only [addressOfAddress, ht] using hcall
  cases called
  · have h₅ := safeRuntime_block_10345_taken (by simp; omega) (by decide) (by jump_dest) h₄
    have hr := safeRuntime_block_5682 (by simp; omega) (by
      change 0 + out.size % UInt256.size ≤ out.size
      simpa only [Nat.zero_add] using Nat.mod_le out.size UInt256.size) h₅
    exact .inl ⟨hr, .inl
      (safePostModuleCheckFailed hguard ht (by simpa only [hacc] using hc) htyped)⟩
  · have h₅ := safeRuntime_block_10345_fallthrough (by simp; omega) (by decide) h₄
    have h₆ := safeRuntime_block_10351_taken (by simp; omega) (by decide) (by jump_dest) h₅
    have h₇ := safeRuntime_block_10361 (by simp; omega) (by jump_dest) h₆
    simp only [safeRuntime_block_10361_stack] at h₇
    have hptr : UInt256.ofNat ptr.toNat = ptr := u256_ofNat_toNat _
    rw [← hptr] at h₇
    obtain hr | ⟨aw₈, k₈, C₈, hfit, h₈⟩ := safeIRAllocateTrace (len := 0) h₇ (by decide)
      (by simpa only [ABI.paddedSize, Nat.zero_add, Nat.zero_div, Nat.zero_mul,
        Nat.add_zero] using ptr.val.isLt) (by simp; omega) (by jump_dest)
    · exact .inl ⟨hr, .inr hz⟩
    simp only [show ABI.paddedSize 0 = 0 by decide, Nat.add_zero, hptr] at h₈
    have h₉ := safeRuntime_block_10374 (by simp; omega) (by jump_dest) h₈
    have h₁₀ := safeRuntime_block_10355 (by simp; omega) (by jump_dest) h₉
    refine .inr ⟨_, evm', σ', _, aw₈, out, _, _, _, _,
      safePostModuleCheckSuccess hguard ht (by simpa only [hacc] using hc) htyped,
      ?_, he, ha, hw, h₁₀, .inr rfl⟩
    simp [postModuleFrame, postModuleArgs, Std.HashMap.getElem_insert]

end Benchmarks.Safe.ViaIR
