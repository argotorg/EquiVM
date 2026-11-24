import Benchmarks.Safe.ViaIR.TokenTransferMemory
import Benchmarks.Safe.ViaIR.Blocks.Runtime_025
import Benchmarks.Safe.ViaIR.Blocks.Runtime_026
import Reasoning.HeapMemory

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

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

set_option maxRecDepth 5000 in
theorem safeTokenTransferReturn {I g s0 σ k C aw mem out}
    {amount guard success hash flag : UInt256} {R : List UInt256} (z : Bool)
    (h : RD fork safeBytecode I g s0 ⟨5215⟩
      (z.toUInt256 :: amount :: guard :: success :: hash :: flag :: ⟨0⟩ :: R)
      (callOutputMem mem out ⟨0⟩ ⟨32⟩) aw out σ k C)
    (hb : out.size < UInt256.size) (hov : R.length + 12 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨5231⟩
      ((tokenTransferResult z out).toUInt256 :: amount :: guard :: success :: hash ::
        flag :: ⟨0⟩ :: R) (callOutputMem mem out ⟨0⟩ ⟨32⟩) aw' out σ k' C' := by
  by_cases hz : out.size = 0
  · have h₁ := safeRuntime_block_5215_taken (by simp; omega)
      (by rw [hz]; decide) (by jump_dest) h
    have h₂ := safeRuntime_block_5260 (by simp; omega) (by jump_dest) h₁
    exact ⟨_, _, _, by simpa only [safeRuntime_block_5260_stack,
      tokenTransferResult, hz, ite_true] using h₂⟩
  have hnz : UInt256.ofNat out.size ≠ ⟨0⟩ := by
    intro he
    have he' := congrArg UInt256.toNat he
    rw [ulit_toNat' out.size hb] at he'
    exact hz he'
  have h₁ := safeRuntime_block_5215_fallthrough (by simp; omega)
    (isZero_eq_zero_of_ne hnz) h
  by_cases hs : out.size = 32
  · have h₂ := safeRuntime_block_5222_taken (by simp; omega)
      (by rw [hs]; decide) (by jump_dest) h₁
    have h₃ := safeRuntime_block_5248 (by simp; omega) (by jump_dest) h₂
    have hw : memLoad ⟨0⟩ (callOutputMem mem out ⟨0⟩ ⟨32⟩) = calldataWord out 0 := by
      apply memLoad_of_wordRead
      exact callOutput32_read_word _ _ _ hb (by omega) (by exact Nat.zero_le _)
    exact ⟨_, _, _, by simpa only [safeRuntime_block_5248_stack, hw,
      callSuccessNonzeroWord, tokenTransferResult, hz, hs, ite_false, ite_true] using h₃⟩
  · have hns : UInt256.ofNat 32 ≠ UInt256.ofNat out.size := by
      intro he
      have he' := congrArg UInt256.toNat he
      rw [ulit_toNat' out.size hb] at he'
      exact hs he'.symm
    have h₂ := safeRuntime_block_5222_fallthrough (by simp; omega)
      (u256_eq_of_ne hns) h₁
    have h₃ := safeRuntime_block_5229 (by simp; omega) h₂
    exact ⟨_, _, _, by simpa only [safeRuntime_block_5229_stack,
      tokenTransferResult, hz, hs, ite_false] using h₃⟩

end Benchmarks.Safe.ViaIR
