import Benchmarks.Midnight.AllocationArithmetic

variable {fork : Ethereum.Fork}

/-! Length checking and allocation arithmetic for arrays of memory pointers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def pointerArrayAllocation (n : Nat) : Nat := 32 + 32 * n

theorem pointerArrayAllocation_word {word : UInt256} (hb : word.toNat < 2^64) :
    UInt256.ofNat 32 + UInt256.shiftLeft word (UInt256.ofNat 5) =
      UInt256.ofNat (pointerArrayAllocation word.toNat) := by
  have hs0 := ushl5_ofNat_toNat word.toNat (by omega)
  rw [u256_ofNat_toNat] at hs0
  have hs : (UInt256.shiftLeft word (UInt256.ofNat 5)).toNat = 32 * word.toNat := hs0
  apply u256_inj
  rw [uadd_toNat, hs]
  change (32 + 32 * word.toNat) % UInt256.size =
    (UInt256.ofNat (pointerArrayAllocation word.toNat)).toNat
  rw [UInt256.toNat_ofNat_of_lt (by change 32 + 32 * word.toNat < 2^256; omega),
    Nat.mod_eq_of_lt (by change 32 + _ < 2^256; omega)]
  rfl

theorem pointerArrayAllocation_end {ptr : UInt256} {n : Nat}
    (hn : n < 2^64) (hp : ptr.toNat < 2^64) :
    allocationEnd ptr (UInt256.ofNat (pointerArrayAllocation n)) =
      ptr + UInt256.ofNat (pointerArrayAllocation n) := by
  have hs : pointerArrayAllocation n < UInt256.size := by
    change 32 + 32 * n < 2^256; omega
  have he : (pointerArrayAllocation n + 31) / 32 * 32 = pointerArrayAllocation n := by
    unfold pointerArrayAllocation
    omega
  apply u256_inj
  rw [allocationEnd_toNat (by
      rw [UInt256.toNat_ofNat_of_lt hs]
      change 32 + 32 * n + 31 < 2^256
      omega)
    (by
      rw [UInt256.toNat_ofNat_of_lt hs, he]
      change _ + (32 + 32 * n) < 2^256
      omega),
    UInt256.toNat_ofNat_of_lt hs, he, uadd_word_ofNat_toNat _ _ (by
      change _ + (32 + 32 * n) < 2^256; omega)]

theorem midnightPointerArrayLengthTooLarge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw len : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hlarge : 2^64 ≤ len.toNat) (hstack : R.length + 4 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨18477⟩ (len :: R) mem aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  have hg : UInt256.gt len
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) = ⟨1⟩ := by
    apply ugt_one
    change 18446744073709551615 < len.toNat
    omega
  have rd1 := midnightBlocks.midnight_block_18477_taken hstack (by rw [hg]; decide)
    (by jump_dest) rd
  exact midnightBlocks.midnight_block_15087 (by simp only [List.length_cons]; omega) rd1

theorem midnightPointerArraySize {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw len ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256}
    (hsmall : len.toNat < 2^64) (hstack : R.length + 5 ≤ 1024)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨18477⟩ (len :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD fork midnightBytecode I g s0 ret
      (UInt256.ofNat (pointerArrayAllocation len.toNat) :: R) mem aw rdata σ k' C' := by
  have hg : UInt256.gt len
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) = ⟨0⟩ := by
    apply ugt_zero
    change len.toNat ≤ 18446744073709551615
    omega
  have rd1 := midnightBlocks.midnight_block_18477_fallthrough
    (by simpa only [List.length_cons, Nat.add_assoc] using hstack) hg rd
  have rd2 := midnightBlocks.midnight_block_18492 (by omega) hret rd1
  simp only [midnightBlocks.midnight_block_18492_stack, pointerArrayAllocation_word hsmall] at rd2
  exact ⟨_, _, rd2⟩

end Benchmarks.Midnight
