import Benchmarks.Safe.PostModuleMemory
import Benchmarks.Safe.RawValueCall
import Benchmarks.Safe.Decoders
import Benchmarks.Safe.Blocks.Runtime_033

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safePostModuleCheckTrace {I g s0 σ k C aw mem rdata}
    {hash guard ptr ret : UInt256} {R : List UInt256} (z : Bool) (evm : EVM.State)
    (h : RD safeBytecode I g s0 ⟨7476⟩
      (z.toUInt256 :: hash :: guard :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hf : memLoad ⟨64⟩ mem = ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr.toNat)
    (hb : ptr.toNat + 68 < UInt256.size) (hov : R.length + 16 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧
      ExecStmt config (postModuleFrame (AccountAddress.ofUInt256 guard) hash z) evm
        postModuleCheck .reverted) ∨
    ∃ frame evm' σ' mem' aw' rdata' k' C',
      ExecStmt config (postModuleFrame (AccountAddress.ofUInt256 guard) hash z) evm
        postModuleCheck (.ok frame evm') ∧
      frame.locals["success"]? = some (.bool z) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ⟨7585⟩
        (z.toUInt256 :: hash :: guard :: ret :: R) mem' aw' rdata' σ' k' C' ∧
      (mem' = mem ∨ mem' = postModuleMemory mem ptr hash z) := by
  have ht : AccountAddress.ofUInt256 guard =
      AccountAddress.ofUInt256 (UInt256.land guard solcAddrMask) := by
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      addressOfNat_eq_of_masked_word guard
  by_cases hz : UInt256.land guard solcAddrMask = ⟨0⟩
  · have h₁ := safeRuntime_block_7476_taken (by simp; omega)
      (by rw [safeAddressMask, hz]; decide) (by jump_dest) h
    have ha : AccountAddress.ofUInt256 guard = 0 := by rw [ht, hz]; rfl
    refine Or.inr ⟨postModuleFrame 0 hash z, evm, σ, mem, _, rdata, _, _, ?_, ?_,
      hee, hacc, hworld, h₁, Or.inl rfl⟩
    · simpa only [ha] using safePostModuleCheckZero evm hash z
    · simp [postModuleFrame, postModuleArgs, Std.HashMap.getElem_insert]
  have hguard : AccountAddress.ofUInt256 guard ≠ 0 := by
    rw [ht]
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      maskedAddress_ne_zero_of_mask_ne_zero hz
  have h₁ := safeRuntime_block_7476_fallthrough (by simp; omega)
    (by rw [safeAddressMask]; exact isZero_eq_zero_of_ne hz) h
  by_cases hc : extCodeSizeWord σ (UInt256.land guard solcAddrMask) = ⟨0⟩
  · obtain ⟨_, _, h₂⟩ := safeRuntime_block_7492_fallthrough (by simp; omega)
      (by rw [safeAddressMask, hc]; decide) h₁
    have hr := safeRuntime_block_7559 (by
      simp only [safeRuntime_block_7492_fallthrough_stack, List.length_cons]; omega) h₂
    exact Or.inl ⟨hr, safePostModuleCheckNoCode hguard ht (by simpa only [hacc] using hc)⟩
  obtain ⟨k₂, C₂, h₂⟩ := safeRuntime_block_7492_taken (by simp; omega)
    (by rw [safeAddressMask, isZero_eq_zero_of_ne hc]; decide) (by jump_dest) h₁
  have hmem := safePostModuleMemory (hash := hash) z hf hb
  have hfree : memLoad (UInt256.ofNat 64)
      (safeRuntime_block_7492_taken_memory (mem := mem) (x0 := z.toUInt256) (x1 := hash)) =
      ptr := by
    rw [hmem]
    exact safePostModuleMemoryFree z hf hm hp
  dsimp only [safeRuntime_block_7492_taken_memory] at hfree
  change memLoad (UInt256.ofNat 64) mem = ptr at hf
  simp only [hf] at hfree
  rw [hmem] at h₂
  simp only [safeRuntime_block_7492_taken_stack, safeAddressMask, hfree, hf] at h₂
  have hlen : UInt256.sub (UInt256.ofNat 68 + ptr) ptr = UInt256.ofNat 68 := by
    rw [u256_add_comm, word_add_sub_left]
  rw [hlen] at h₂
  have h₃ := safeRuntime_block_7562 (by simp; omega) h₂
  obtain ⟨evm', σ', called, out, aw', k', C', hcall, he, ha, hw, h₄, _⟩ :=
    rawValueCallTraceFrom evm h₃ hee hacc hworld (by native_decide) (by simp; omega)
      (Or.inr rfl)
  rw [callOutputMem_zero] at h₄
  have htyped : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256 guard)) "checkAfterModuleExecution" 0
      [.fixedBytes bytes32Width (EVM.Word.toBytesBE hash), .bool z] (called, evm', out) := by
    refine ⟨_, safePostModuleEncoding mem ptr hash z, ?_⟩
    simpa only [addressOfAddress, ht] using hcall
  cases called
  · have h₅ := safeRuntime_block_7566_fallthrough (by simp; omega) (by decide) h₄
    have hr := safeRuntime_block_7573 (by
      simp only [safeRuntime_block_7566_fallthrough_stack, List.length_cons]; omega) h₅
    exact Or.inl ⟨hr,
      safePostModuleCheckFailed hguard ht (by simpa only [hacc] using hc) htyped⟩
  · have h₅ := safeRuntime_block_7566_taken (by simp; omega) (by decide) (by jump_dest) h₄
    have h₆ := safeRuntime_block_7580 (by simp; omega) h₅
    refine Or.inr ⟨_, evm', σ', _, aw', out, _, _,
      safePostModuleCheckSuccess hguard ht (by simpa only [hacc] using hc) htyped,
      ?_, he, ha, hw, h₆, Or.inr rfl⟩
    simp [postModuleFrame, postModuleArgs, Std.HashMap.getElem_insert]

end Benchmarks.Safe
