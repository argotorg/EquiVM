import Benchmarks.Safe.PreModuleReturnMemory
import Benchmarks.Safe.Bytes32ReturnDecoder
import Benchmarks.Safe.Blocks.Runtime_031
import Benchmarks.Safe.Blocks.Runtime_032

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safePreModuleCallFailure {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7346⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) : RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_7346_fallthrough (by omega) (by decide) h
  exact safeRuntime_block_7353 (by
    simp only [safeRuntime_block_7346_fallthrough_stack, List.length_cons]; omega) h₁

theorem safePreModuleReturn {I g s0 σ k C aw mem out}
    {ptr a b c oldHash : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7346⟩ (⟨1⟩ :: a :: b :: c :: oldHash :: R)
      (preModuleOutputMemory mem out ptr) aw out σ k C)
    (hf : memLoad ⟨64⟩ mem = ptr) (hm : ptr.toNat + 32 ≤ mem.size) (hp : 96 ≤ ptr.toNat)
    (hb : out.size < 2 ^ 255) (hov : R.length + 9 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ config.externalABI.decode? "checkModuleTransaction" out = none) ∨
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨7399⟩ (calldataWord out 0 :: R)
      (preModuleReturnMemory mem out ptr) aw' out σ k' C' ∧
      config.externalABI.decode? "checkModuleTransaction" out =
        some [.fixedBytes bytes32Width (EVM.Word.toBytesBE (calldataWord out 0))] := by
  have h₁ := safeRuntime_block_7346_taken (by simp; omega) (by decide) (by jump_dest) h
  have h₂ := safeRuntime_block_7360 (by simp; omega) (by jump_dest) h₁
  have hfree : memLoad (UInt256.ofNat 64) (preModuleOutputMemory mem out ptr) = ptr :=
    preModuleOutputFree hf (by omega) hp
  simp only [safeRuntime_block_7360_stack, safeRuntime_block_7360_memory, hfree] at h₂
  change RD safeBytecode I g s0 _ (ptr :: (ptr + UInt256.ofNat out.size) ::
    UInt256.ofNat 7396 :: oldHash :: R) (preModuleReturnMemory mem out ptr) _ out σ _ _ at h₂
  by_cases hl : 32 ≤ out.size
  · obtain ⟨aw', k', C', h₃⟩ := safeBytes32DecoderValid h₂ (by simp; omega) hl hb
      (by jump_dest)
    rw [preModuleReturnWord hm hp hl] at h₃
    have h₄ := safeRuntime_block_7396 (by simp; omega) h₃
    refine Or.inr ⟨_, _, _, h₄, ?_⟩
    change (ABI.decodeReturnValueWithMode? .modern abiBytes32 out).map (fun v ↦ [v]) = _
    rw [decodeBytes32ReturnLong hl hb]
    rfl
  · refine Or.inl ⟨safeBytes32DecoderShort h₂ (by simp; omega) (by omega), ?_⟩
    change (ABI.decodeReturnValueWithMode? .modern abiBytes32 out).map (fun v ↦ [v]) = _
    rw [decodeBytes32ReturnShort (by omega)]
    rfl

end Benchmarks.Safe
