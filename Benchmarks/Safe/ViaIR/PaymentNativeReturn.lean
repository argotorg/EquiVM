import Benchmarks.Safe.ViaIR.ReturnDataMemory
import Benchmarks.Safe.ViaIR.MemoryPreserves
import Benchmarks.Safe.ViaIR.Blocks.Runtime_025
import Benchmarks.Safe.ViaIR.Blocks.Runtime_026
import Benchmarks.Safe.ViaIR.Blocks.Runtime_044

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

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

set_option maxRecDepth 5000 in
theorem safePaymentReturnBuffer {I g s0 σ k C aw mem ptr out}
    {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10382⟩ (ret :: R) mem aw out σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hb : ptr + out.size + 64 < UInt256.size) (hov : R.length + 11 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev fork safeBytecode g s0 ∨
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret
      ((if out.size = 0 then ⟨96⟩ else UInt256.ofNat ptr) :: R)
      (paymentReturnMemory mem ptr out) aw' out σ k' C' ∧
      (ptr < 2 ^ 64 → paymentReturnEnd ptr out < 2 ^ 64) := by
  simpa only [paymentReturnMemory, paymentReturnEnd] using
    safeIRReturnBufferTrace h hf hb hov hret

set_option maxRecDepth 5000 in
theorem safePaymentNativeFinish {I g s0 σ k C aw mem out}
    {buf payment guard success hash : UInt256} {R : List UInt256} (z : Bool)
    (h : RD fork safeBytecode I g s0 ⟨5088⟩
      (buf :: z.toUInt256 :: payment :: guard :: success :: hash :: R) mem aw out σ k C)
    (hov : R.length + 12 ≤ 1024) :
    if z then ∃ k' C', RD fork safeBytecode I g s0 ⟨5097⟩
      (payment :: hash :: guard :: success :: hash :: R) mem aw out σ k' C'
    else RDrev fork safeBytecode g s0 := by
  cases z
  · have h₁ := safeRuntime_block_5088_taken (by simp; omega) (by decide) (by jump_dest) h
    have h₂ := safeRuntime_block_5106 (by simp [safeRuntime_block_5088_taken_stack]; omega)
      (by jump_dest) h₁
    exact safeRuntime_block_9772 (by simp [safeRuntime_block_5088_taken_stack]; omega) h₂
  · have h₁ := safeRuntime_block_5088_fallthrough (by simp; omega) (by decide) h
    have h₂ := safeRuntime_block_5095 (by simp; omega) h₁
    exact ⟨_, _, h₂⟩

set_option maxRecDepth 5000 in
theorem safePaymentTokenFinish {I g s0 σ k C aw mem out}
    {payment guard success hash : UInt256} {R : List UInt256} (z : Bool)
    (h : RD fork safeBytecode I g s0 ⟨5231⟩
      (z.toUInt256 :: payment :: guard :: success :: hash :: R) mem aw out σ k C)
    (hov : R.length + 12 ≤ 1024) :
    if z then ∃ k' C', RD fork safeBytecode I g s0 ⟨5097⟩
      (payment :: hash :: guard :: success :: hash :: R) mem aw out σ k' C'
    else RDrev fork safeBytecode g s0 := by
  cases z
  · have h₁ := safeRuntime_block_5231_taken (by simp; omega) (by decide) (by jump_dest) h
    have h₂ := safeRuntime_block_5243 (by simp [safeRuntime_block_5231_taken_stack]; omega)
      (by jump_dest) h₁
    exact safeRuntime_block_9727 (by simp [safeRuntime_block_5231_taken_stack]; omega) h₂
  · have h₁ := safeRuntime_block_5231_fallthrough (by simp; omega) (by decide) h
    have h₂ := safeRuntime_block_5237 (by simp; omega) (by jump_dest) h₁
    exact ⟨_, _, h₂⟩

end Benchmarks.Safe.ViaIR
