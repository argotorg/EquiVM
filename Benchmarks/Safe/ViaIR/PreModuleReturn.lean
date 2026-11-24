import Benchmarks.Safe.ViaIR.PreModuleReturnMemory
import Benchmarks.Safe.ViaIR.Bytes32ReturnDecoder
import Benchmarks.Safe.ViaIR.IRMemoryAllocation
import Benchmarks.Safe.ViaIR.Blocks.Runtime_027
import Benchmarks.Safe.ViaIR.Blocks.Runtime_045

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safePreModuleCallFailure {I g s0 σ k C aw mem rdata ptr} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9990⟩ (⟨0⟩ :: ptr :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_9990_taken (by omega) (by decide) (by jump_dest) h
  exact safeRuntime_block_5682 (by
    simp only [safeRuntime_block_9990_taken_stack, List.length_cons]; omega)
    (by
      change 0 + rdata.size % UInt256.size ≤ rdata.size
      simpa only [Nat.zero_add] using Nat.mod_le rdata.size UInt256.size) h₁

theorem safePreModuleReturn {I g s0 σ k C aw mem out}
    {ptr : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9990⟩ (⟨1⟩ :: ptr :: R)
      (preModuleOutputMemory mem out ptr) aw out σ k C)
    (hf : memLoad ⟨64⟩ mem = ptr) (hm : ptr.toNat + 32 ≤ mem.size) (hp : 96 ≤ ptr.toNat)
    (hbptr : ptr.toNat + 32 < UInt256.size)
    (hb : out.size < 2 ^ 255) (hov : R.length + 13 ≤ 1024) :
    RDrev fork safeBytecode g s0 ∨
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨10003⟩ (⟨0⟩ :: calldataWord out 0 :: R)
      (preModuleReturnMemory mem out ptr) aw' out σ k' C' ∧
      config.externalABI.decode? "checkModuleTransaction" out =
        some [.fixedBytes bytes32Width (EVM.Word.toBytesBE (calldataWord out 0))] := by
  have hout : out.size < UInt256.size := lt_trans hb (by decide)
  have h₁ := safeRuntime_block_9990_fallthrough (by simp; omega) (by decide) h
  have h₂ := safeRuntime_block_9997_taken (by simp; omega) (by decide) (by jump_dest) h₁
  have hstart : ∃ k' C', RD fork safeBytecode I g s0 ⟨10028⟩
      (ptr :: UInt256.ofNat (min 32 out.size) :: ptr :: R)
      (preModuleOutputMemory mem out ptr) aw out σ k' C' := by
    by_cases hl : 32 ≤ out.size
    · have ht := safeRuntime_block_10014_fallthrough (by simp; omega)
        (ugt_zero (by rw [ulit_toNat' _ hout]; exact hl)) h₂
      rw [Nat.min_eq_left hl]
      exact ⟨_, _, ht⟩
    · have ht := safeRuntime_block_10014_taken (by simp; omega) (by
        rw [ugt_one (by rw [ulit_toNat' _ hout]; change out.size < 32; omega)]; decide)
        (by jump_dest) h₂
      have hr := safeRuntime_block_10056 (by simp; omega) (by jump_dest) ht
      rw [Nat.min_eq_right (by omega)]
      exact ⟨_, _, hr⟩
  obtain ⟨_, _, h₃⟩ := hstart
  have h₄ := safeRuntime_block_10028 (by simp; omega) (by jump_dest) h₃
  have hpad : ABI.paddedSize (min 32 out.size) ≤ 32 := by unfold ABI.paddedSize; omega
  have hlen : min 32 out.size + 31 < UInt256.size := by change _ < 2 ^ 256; omega
  have hbadd : ptr.toNat + ABI.paddedSize (min 32 out.size) < UInt256.size := by omega
  have hptr : UInt256.ofNat ptr.toNat = ptr := u256_ofNat_toNat _
  simp only [safeRuntime_block_10028_stack] at h₄
  rw [← hptr] at h₄
  obtain hr | ⟨aw', k', C', hfit, h₅⟩ := safeIRAllocateTrace h₄ hlen hbadd
    (by simp; omega) (by jump_dest)
  · exact .inl hr
  rw [hptr] at h₅
  have hnext : UInt256.ofNat (ptr.toNat + ABI.paddedSize (min 32 out.size)) =
      preModuleNextPtr ptr out := by
    rw [preModuleNextPtr, roundedCalldataLengthMask _ hlen,
      ← wordOfNatAdd _ _ hbadd, hptr]
  rw [hnext] at h₅
  change RD fork safeBytecode I g s0 ⟨10041⟩
    (UInt256.ofNat (min 32 out.size) :: ptr :: ⟨32⟩ :: ptr :: R)
    (preModuleReturnMemory mem out ptr) aw' out σ k' C' at h₅
  by_cases hl : 32 ≤ out.size
  · obtain ⟨aw'', k'', C'', h₆⟩ := safeBytes32DecoderValid h₅ (by omega) (by omega)
      (by change _ < 2 ^ 255; omega)
    rw [preModuleReturnWord hm hp hl] at h₆
    refine .inr ⟨_, _, _, h₆, ?_⟩
    change (ABI.decodeReturnValueWithMode? .modern abiBytes32 out).map (fun v ↦ [v]) = _
    rw [decodeBytes32ReturnLong hl hb]
    rfl
  · exact .inl (safeBytes32DecoderShort h₅ (by omega) (by omega))

end Benchmarks.Safe.ViaIR
