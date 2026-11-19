import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.MemoryCharge

/-! The compiler's Boolean decoder for memory, used by safe-transfer return checks. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightBoolMemory_short {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw base finish : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hshort : UInt256.slt (UInt256.sub finish base) (UInt256.ofNat 32) ≠ ⟨0⟩)
    (rd : RD midnightBytecode I g s0 ⟨20432⟩ (base :: finish :: R) mem aw rdata σ k C) :
    RDrev midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_20432_taken hstack hshort (by jump_dest) rd
  exact midnightBlocks.midnight_block_6350
    (by simp only [midnightBlocks.midnight_block_20432_taken_stack, List.length_cons]; omega) rd1

theorem midnightBoolMemory_dirty {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw base finish : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub finish base) (UInt256.ofNat 32) = ⟨0⟩)
    (hdirty : ¬ (memLoad base mem = ⟨0⟩ ∨ memLoad base mem = ⟨1⟩))
    (rd : RD midnightBytecode I g s0 ⟨20432⟩ (base :: finish :: R) mem aw rdata σ k C) :
    RDrev midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_20432_fallthrough hstack hlen rd
  have rd2 := midnightBlocks.midnight_block_20444_taken (by omega)
    (fun he ↦ hdirty ((boolWordClean_iff _).mp (u256_sub_eq_zero_iff_eq.mp he).symm))
    (by jump_dest) rd1
  exact midnightBlocks.midnight_block_6350
    (by simp only [midnightBlocks.midnight_block_20444_taken_stack, List.length_cons]; omega) rd2

theorem midnightBoolMemory_cleanCharge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw base finish ret : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub finish base) (UInt256.ofNat 32) = ⟨0⟩)
    (hclean : memLoad base mem = ⟨0⟩ ∨ memLoad base mem = ⟨1⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨20432⟩ (base :: finish :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryCharge 0 aw aw' C C' ∧ RD midnightBytecode I g s0 ret (memLoad base mem :: R)
      mem aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_20432_fallthrough
    (by simp only [List.length_cons]; omega) hlen rd
  have rd2 := midnightBlocks.midnight_block_20444_fallthrough
    (by simp only [List.length_cons]; omega)
    (u256_sub_eq_zero_iff_eq.mpr ((boolWordClean_iff _).mpr hclean).symm) rd1
  have rd3 := midnightBlocks.midnight_block_20454 (by omega) hret rd2
  have h0 := MemoryCharge.refl aw C
  have hc3 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd3 (by memory_charge h0)
  exact ⟨_, _, _, hc3, rd3⟩

theorem midnightBoolMemory_clean {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw base finish ret : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub finish base) (UInt256.ofNat 32) = ⟨0⟩)
    (hclean : memLoad base mem = ⟨0⟩ ∨ memLoad base mem = ⟨1⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨20432⟩ (base :: finish :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g s0 ret (memLoad base mem :: R)
      mem aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', _, rd'⟩ := midnightBoolMemory_cleanCharge hstack hlen hclean hret rd
  exact ⟨aw', k', C', rd'⟩

end Benchmarks.Midnight
