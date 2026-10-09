import Benchmarks.Safe.ReturnDataMemory
import Benchmarks.Safe.MemoryPreserves
import Benchmarks.Safe.Blocks.Runtime_034
import Benchmarks.Safe.Blocks.Runtime_035
import Benchmarks.Safe.Blocks.Runtime_030

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def paymentReturnMemory (mem : ByteArray) (ptr : Nat) (out : ByteArray) : ByteArray :=
  if out.size = 0 then mem else returnDataMemory mem ptr out

def paymentReturnEnd (ptr : Nat) (out : ByteArray) : Nat :=
  if out.size = 0 then ptr else ptr + 32 + ABI.paddedSize out.size

theorem paymentReturnMemory_free {mem out : ByteArray} {ptr : Nat}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (paymentReturnMemory mem ptr out) = UInt256.ofNat (paymentReturnEnd ptr out) := by
  by_cases hz : out.size = 0
  · simpa only [paymentReturnMemory, paymentReturnEnd, hz, ite_true] using hf
  · simpa only [paymentReturnMemory, paymentReturnEnd, hz, ite_false] using
      returnDataMemory_free mem out ptr hp

theorem paymentReturnMemory_size (mem out : ByteArray) (ptr : Nat) (hp : 96 ≤ ptr) :
    mem.size ≤ (paymentReturnMemory mem ptr out).size ∧
      (paymentReturnMemory mem ptr out).size ≤ max mem.size (paymentReturnEnd ptr out) := by
  by_cases hz : out.size = 0
  · simp only [paymentReturnMemory, paymentReturnEnd, hz, ite_true]
    exact ⟨le_refl _, Nat.le_max_left _ _⟩
  · simp only [paymentReturnMemory, paymentReturnEnd, hz, ite_false,
      returnDataMemory_size _ _ _ hp]
    have hh : out.size ≤ ABI.paddedSize out.size := by dsimp [ABI.paddedSize]; omega
    omega

theorem paymentReturnMemory_preserved (mem out : ByteArray) (ptr : Nat) (hp : 96 ≤ ptr) :
    MemoryPreserves mem (paymentReturnMemory mem ptr out) 96 ptr := by
  refine ⟨(paymentReturnMemory_size mem out ptr hp).1, ?_⟩
  intro off count hl hh hin
  by_cases hz : out.size = 0
  · simp only [paymentReturnMemory, hz, ite_true]
  · simpa only [paymentReturnMemory, hz, ite_false] using
      returnDataMemory_preserved mem out ptr off count hin hl hh

theorem paymentReturnEnd_bounds (ptr : Nat) (out : ByteArray) (hb : out.size < 2 ^ 138) :
    ptr ≤ paymentReturnEnd ptr out ∧ paymentReturnEnd ptr out ≤ ptr + 2 ^ 139 := by
  unfold paymentReturnEnd
  split
  · omega
  · dsimp [ABI.paddedSize]; omega

set_option maxRecDepth 100000 in
theorem safePaymentReturnBuffer {I g s0 σ k C aw mem ptr out}
    {z x y w : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7835⟩ (z :: x :: y :: w :: R) mem aw out σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hb : ptr + out.size + 64 < UInt256.size) (hov : R.length + 7 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨7885⟩
      (UInt256.ofNat out.size :: (if out.size = 0 then ⟨96⟩ else UInt256.ofNat ptr) :: z :: R)
      (paymentReturnMemory mem ptr out) aw' out σ k' C' := by
  by_cases hz : out.size = 0
  · have h₁ := safeRuntime_block_7835_taken (by omega)
      (by rw [hz]; decide) (by jump_dest) h
    simp only [safeRuntime_block_7835_taken_stack] at h₁
    have h₂ := safeRuntime_block_7880 (by simp; omega) h₁
    exact ⟨_, _, _, by simpa only [safeRuntime_block_7880_stack, paymentReturnMemory,
      hz, ite_true] using h₂⟩
  · have hw : UInt256.ofNat out.size ≠ ⟨0⟩ := by
      intro he
      have he' := congrArg UInt256.toNat he
      rw [ulit_toNat' out.size (by omega)] at he'
      exact hz he'
    have h₁ := safeRuntime_block_7835_fallthrough (by omega)
      (by exact u256_eq_of_ne hw) h
    simp only [safeRuntime_block_7835_fallthrough_stack] at h₁
    obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_7848_packed (by simp; omega)
      (by rw [ulit_toNat' out.size (by omega)]; change 0 + out.size ≤ out.size; omega)
      (by jump_dest) h₁
    have hm : safeRuntime_block_7848_memory (mem := mem) (rdata := out) =
        returnDataMemory mem ptr out := safeReturnDataMemory hf hb
    change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
    exact ⟨_, _, _, by simpa only [safeRuntime_block_7848_stack, hm, hf,
      paymentReturnMemory, hz, ite_false] using h₂⟩

set_option maxRecDepth 100000 in
theorem safePaymentNativeFinish {I g s0 σ k C aw mem out}
    {size buf receiver payment refund token price base used ret : UInt256} {R : List UInt256}
    (z : Bool)
    (h : RD safeBytecode I g s0 ⟨7885⟩
      (size :: buf :: z.toUInt256 :: ⟨0⟩ :: receiver :: payment :: refund :: token ::
        price :: base :: used :: ret :: R) mem aw out σ k C)
    (hov : R.length + 16 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    if z then ∃ k' C', RD safeBytecode I g s0 ret (payment :: R) mem aw out σ k' C'
    else RDrev safeBytecode g s0 := by
  cases z
  · have h₁ := safeRuntime_block_7885_fallthrough (by simp; omega) (by rfl) h
    simp only [safeRuntime_block_7885_fallthrough_stack] at h₁
    have h₂ := safeRuntime_block_7895 (by simp; omega) (by jump_dest) h₁
    exact safeRuntime_block_6898 (by
      simp only [safeRuntime_block_7895_stack, List.length_cons]; omega) h₂
  · have h₁ := safeRuntime_block_7885_taken (by simp; omega) (by decide) (by jump_dest) h
    simp only [safeRuntime_block_7885_taken_stack] at h₁
    have h₂ := safeRuntime_block_7911 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_7911_stack] at h₂
    have h₃ := safeRuntime_block_7965 (by simp; omega) hret h₂
    exact ⟨_, _, by simpa only [safeRuntime_block_7965_stack] using h₃⟩

set_option maxRecDepth 100000 in
theorem safePaymentTokenFinish {I g s0 σ k C aw mem out}
    {receiver payment refund token price base used ret : UInt256} {R : List UInt256}
    (z : Bool)
    (h : RD safeBytecode I g s0 ⟨7944⟩
      (z.toUInt256 :: receiver :: payment :: refund :: token :: price :: base :: used :: ret :: R)
      mem aw out σ k C)
    (hov : R.length + 16 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    if z then ∃ k' C', RD safeBytecode I g s0 ret (payment :: R) mem aw out σ k' C'
    else RDrev safeBytecode g s0 := by
  cases z
  · have h₁ := safeRuntime_block_7944_fallthrough (by simp; omega) (by rfl) h
    simp only [safeRuntime_block_7944_fallthrough_stack] at h₁
    have h₂ := safeRuntime_block_7949 (by simp; omega) (by jump_dest) h₁
    exact safeRuntime_block_6898 (by
      simp only [safeRuntime_block_7949_stack, List.length_cons]; omega) h₂
  · have h₁ := safeRuntime_block_7944_taken (by simp; omega) (by decide) (by jump_dest) h
    simp only [safeRuntime_block_7944_taken_stack] at h₁
    have h₂ := safeRuntime_block_7965 (by simp; omega) hret h₁
    exact ⟨_, _, by simpa only [safeRuntime_block_7965_stack] using h₂⟩

end Benchmarks.Safe
