import Benchmarks.Safe.ExecGuardCallPrepare
import Benchmarks.Safe.CalldataBufferMemory
import Benchmarks.Safe.CalldataLengthRounding
import Benchmarks.Safe.Blocks.Runtime_021

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def execAllocatedStack (p : ExecTransactionInput) (src ptr : Nat)
    (before sigPtr guard hash : UInt256) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat (ptr + 32 + ABI.paddedSize p.tx.payload.size),
    UInt256.ofNat p.tx.payload.size, UInt256.ofNat p.tx.payload.size, UInt256.ofNat src,
    UInt256.ofNat ptr, p.tx.value, UInt256.ofNat p.tx.target.val, ⟨3940⟩, before] ++
    execGuardSaved p src sigPtr guard hash R

set_option maxRecDepth 100000 in
theorem safeExecAllocate (p : ExecTransactionInput)
    {I g s0 σ k C aw mem rdata src ptr} {sigPtr guard hash : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3830⟩ (execGuardSaved p src sigPtr guard hash R)
      mem aw rdata σ k C)
    (hf : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr)
    (hp : ptr + 64 + p.tx.payload.size < UInt256.size) (hs : src < UInt256.size)
    (hov : R.length + 28 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨3904⟩
      (execAllocatedStack p src ptr (g.subNat (C + 3 + 2)).toUInt256 sigPtr guard hash R)
      (calldataBufferMemory I.calldata mem src ptr p.tx.payload.size p.tx.payload.size
        (ptr + 32 + ABI.paddedSize p.tx.payload.size)) aw' rdata σ k' C' := by
  have hpad : ABI.paddedSize p.tx.payload.size ≤ p.tx.payload.size + 31 := by
    unfold ABI.paddedSize; omega
  have hend : UInt256.ofNat ptr +
      (UInt256.ofNat 32 + UInt256.ofNat (ABI.paddedSize p.tx.payload.size)) =
      UInt256.ofNat (ptr + 32 + ABI.paddedSize p.tx.payload.size) := by
    rw [wordOfNatAdd _ _ (by omega), wordOfNatAdd _ _ (by omega)]
    rw [Nat.add_assoc]
  have hstart : (UInt256.ofNat 32 + UInt256.ofNat ptr).toNat = ptr + 32 := by
    rw [wordOfNatAdd _ _ (by omega), ulit_toNat' _ (by omega)]
    omega
  have htail : ((UInt256.ofNat 32 + UInt256.ofNat ptr) +
      UInt256.ofNat p.tx.payload.size).toNat = ptr + 32 + p.tx.payload.size := by
    rw [uadd_toNat, hstart, ulit_toNat' p.tx.payload.size (by omega),
      Nat.mod_eq_of_lt (by omega)]
  obtain ⟨aw', k', C', h₁⟩ := safeRuntime_block_3830_packed (by simp; omega) h
  simp only [safeRuntime_block_3830_stack, safeRuntime_block_3830_memory, hf,
    roundedCalldataLength p.tx.payload.size (by omega),
    roundedCalldataLengthMask p.tx.payload.size (by omega), hend, hstart, htail,
    ulit_toNat' ptr (by omega), ulit_toNat' p.tx.payload.size (by omega),
    ulit_toNat' src hs] at h₁
  have he : (UInt256.ofNat 32 + UInt256.ofNat ptr) +
      UInt256.ofNat (ABI.paddedSize p.tx.payload.size) =
      UInt256.ofNat (ptr + 32 + ABI.paddedSize p.tx.payload.size) := by
    rw [u256_add_comm (UInt256.ofNat 32), u256_add_assoc]
    exact hend
  rw [he] at h₁
  exact ⟨aw', k', C', h₁⟩

end Benchmarks.Safe
