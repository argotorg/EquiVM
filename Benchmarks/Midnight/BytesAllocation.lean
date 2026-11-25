import Benchmarks.Midnight.ReturnData

variable {fork : Ethereum.Fork}

/-! The common uint64 length check and bytes allocation size at PC 19016. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

-- GENERALIZES returnDataAllocation_end: separate machine-word arithmetic from the uint64 check.
theorem bytesAllocationEnd {ptr : UInt256} {size : Nat}
    (hs : size + 94 < UInt256.size)
    (hp : ptr.toNat + returnDataAllocation size < UInt256.size) :
    allocationEnd ptr (UInt256.ofNat (returnDataAllocation size)) = returnDataPtr ptr size := by
  have hb : returnDataAllocation size < UInt256.size := by omega
  have hr : (returnDataAllocation size + 31) / 32 * 32 = returnDataAllocation size := by
    dsimp only [returnDataAllocation]; omega
  apply u256_inj
  rw [allocationEnd_toNat (by
      rw [UInt256.toNat_ofNat_of_lt hb]; dsimp only [returnDataAllocation]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hb, hr]; exact hp),
    UInt256.toNat_ofNat_of_lt hb, hr, returnDataPtr, uadd_word_ofNat_toNat _ _ hp]

theorem midnightBytesLengthTooLarge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw len : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hlarge : 2^64 ≤ len.toNat) (hstack : R.length + 4 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨19016⟩ (len :: R) mem aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  have hgt : UInt256.gt len
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)) =
      ⟨1⟩ := by
    apply ugt_one
    change 18446744073709551615 < len.toNat
    omega
  have rd1 := midnightBlocks.midnight_block_19016_taken hstack (by rw [hgt]; decide)
    (by jump_dest) rd
  exact midnightBlocks.midnight_block_15087 (by simp only [List.length_cons]; omega) rd1

-- GENERALIZES midnightBytesAllocationSize by retaining the gas charge.
theorem midnightBytesAllocationSize_charge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw len ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256}
    (hsmall : len.toNat < 2^64) (hstack : R.length + 5 ≤ 1024)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨19016⟩ (len :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', MemoryCharge 0 aw aw C C' ∧ RD fork midnightBytecode I g s0 ret
      (UInt256.ofNat (returnDataAllocation len.toNat) :: R) mem aw rdata σ k' C' := by
  have hgt : UInt256.gt len
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)) =
      ⟨0⟩ := by
    apply ugt_zero
    change len.toNat ≤ 18446744073709551615
    omega
  have rd1 := midnightBlocks.midnight_block_19016_fallthrough
    (by simpa only [List.length_cons, Nat.add_assoc] using hstack) hgt rd
  have rd2 := midnightBlocks.midnight_block_19031 (by omega) hret rd1
  have hs := returnDataAllocation_word (size := len.toNat) (by change _ < 2^256; omega)
  rw [u256_ofNat_toNat] at hs
  simp only [midnightBlocks.midnight_block_19031_stack, hs] at rd2
  have h0 := MemoryCharge.refl aw C
  have hc := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd2 (by memory_charge h0)
  exact ⟨_, _, hc, rd2⟩

theorem midnightBytesAllocationSize {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw len ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256}
    (hsmall : len.toNat < 2^64) (hstack : R.length + 5 ≤ 1024)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨19016⟩ (len :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD fork midnightBytecode I g s0 ret
      (UInt256.ofNat (returnDataAllocation len.toNat) :: R) mem aw rdata σ k' C' := by
  obtain ⟨k', C', _, rd'⟩ := midnightBytesAllocationSize_charge hsmall hstack hret rd
  exact ⟨k', C', rd'⟩

end Benchmarks.Midnight
