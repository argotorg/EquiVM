import Benchmarks.Safe.TokenTransferMemory
import Benchmarks.Safe.Blocks.Runtime_038
import Benchmarks.Safe.Blocks.Runtime_039
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: solc's assembly conjunction of CALL success and a nonzero return word.
theorem callSuccessNonzeroWord (z : Bool) (w : UInt256) :
    UInt256.isZero (UInt256.lor (UInt256.isZero z.toUInt256) (UInt256.isZero w)) =
      (z && decide (w ≠ ⟨0⟩)).toUInt256 := by
  by_cases hw : w = ⟨0⟩
  · subst w; cases z <;> decide +kernel
  · rw [isZero_eq_zero_of_ne hw]
    cases z <;> simp only [hw, ne_eq, not_false_eq_true, decide_true,
      Bool.false_and, Bool.true_and] <;> decide +kernel

-- GENERALIZES callOutput32_read_below to arbitrary windows above the output buffer.
theorem callOutput32_read_above (mem out : ByteArray) (dst : UInt256) (off count : Nat)
    (hb : out.size < UInt256.size) (hin : off + count ≤ mem.size)
    (hd : dst.toNat ≤ mem.size) (hl : dst.toNat + 32 ≤ off) :
    (callOutputMem mem out dst ⟨32⟩).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [callOutputMem, callOutputLen32 hb]
  apply copyWindowReadAbove _ _ _ _ _ _ _ (by omega) hd hin
  omega

set_option maxRecDepth 100000 in
theorem safeTokenTransferReturn {I g s0 σ k C aw mem out}
    {ptr amount receiver token ret : UInt256} {R : List UInt256} (z : Bool)
    (h : RD safeBytecode I g s0 ⟨9005⟩
      (z.toUInt256 :: ptr :: ⟨0⟩ :: amount :: receiver :: token :: ret :: R)
      (callOutputMem mem out ⟨0⟩ ⟨32⟩) aw out σ k C)
    (hb : out.size < UInt256.size) (hov : R.length + 11 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret ((tokenTransferResult z out).toUInt256 :: R)
      (callOutputMem mem out ⟨0⟩ ⟨32⟩) aw' out σ k' C' := by
  by_cases hz : out.size = 0
  · have h₁ := safeRuntime_block_9005_taken (by simp; omega)
      (by rw [hz]; decide) (by jump_dest) h
    simp only [safeRuntime_block_9005_taken_stack] at h₁
    have h₂ := safeRuntime_block_9027 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_9027_stack] at h₂
    have h₃ := safeRuntime_block_9045 (by simp; omega) hret h₂
    simp only [safeRuntime_block_9045_stack] at h₃
    exact ⟨_, _, _, by simpa only [tokenTransferResult, hz, ite_true] using h₃⟩
  have hnz : UInt256.ofNat out.size ≠ ⟨0⟩ := by
    intro he
    have he' := congrArg UInt256.toNat he
    rw [ulit_toNat' out.size hb] at he'
    exact hz he'
  have h₁ := safeRuntime_block_9005_fallthrough (by simp; omega)
    (by exact isZero_eq_zero_of_ne hnz) h
  simp only [safeRuntime_block_9005_fallthrough_stack] at h₁
  by_cases hs : out.size = 32
  · have h₂ := safeRuntime_block_9012_taken (by simp; omega)
      (by rw [hs]; decide) (by jump_dest) h₁
    have h₃ := safeRuntime_block_9035 (by simp; omega) h₂
    have hw : memLoad ⟨0⟩ (callOutputMem mem out ⟨0⟩ ⟨32⟩) = calldataWord out 0 := by
      apply memLoad_of_wordRead
      exact callOutput32_read_word _ _ _ hb (by omega) (by exact Nat.zero_le _)
    simp only [safeRuntime_block_9035_stack, hw, callSuccessNonzeroWord] at h₃
    have h₄ := safeRuntime_block_9045 (by simp; omega) hret h₃
    simp only [safeRuntime_block_9045_stack] at h₄
    exact ⟨_, _, _, by simpa only [tokenTransferResult, hz, hs, ite_false, ite_true] using h₄⟩
  · have hns : UInt256.ofNat out.size ≠ UInt256.ofNat 32 := by
      intro he
      have he' := congrArg UInt256.toNat he
      rw [ulit_toNat' out.size hb] at he'
      exact hs he'
    have h₂ := safeRuntime_block_9012_fallthrough (by simp; omega)
      (by exact u256_eq_of_ne hns) h₁
    have h₃ := safeRuntime_block_9020 (by simp; omega) (by jump_dest) h₂
    simp only [safeRuntime_block_9020_stack] at h₃
    have h₄ := safeRuntime_block_9045 (by simp; omega) hret h₃
    simp only [safeRuntime_block_9045_stack] at h₄
    exact ⟨_, _, _, by simpa only [tokenTransferResult, hz, hs, ite_false] using h₄⟩

end Benchmarks.Safe
