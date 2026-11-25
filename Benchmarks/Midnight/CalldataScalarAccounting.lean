import Benchmarks.Midnight.CalldataAddress
import Benchmarks.Midnight.ArrayAllocation
import Benchmarks.Midnight.MemoryAccounting

variable {fork : Ethereum.Fork}

/-! Memory accounting for calldata addresses and checked array lengths. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCalldataAddress_ok_accounted {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw head ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨18342⟩ (head :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', MemoryAccounting mem aw C' ∧ RD fork midnightBytecode I g s0 ret (calldataWord I.calldata head.toNat :: R)
      mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18342_fallthrough hstack
    (addressCheck_zero hcanon) rd
  have rd2 := midnightBlocks.midnight_block_18361 (by
    simp only [List.length_cons]; omega) hvalid rd1
  have ha2 := memoryAccountingAt rd2 (by memory_account ha)
  exact ⟨_, _, ha2, rd2⟩

theorem midnightPointerArraySize_accounted {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw len ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256}
    (hsmall : len.toNat < 2^64) (hstack : R.length + 5 ≤ 1024)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨18477⟩ (len :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', MemoryAccounting mem aw C' ∧ RD fork midnightBytecode I g s0 ret
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
  have ha2 := memoryAccountingAt rd2 (by memory_account ha)
  exact ⟨_, _, ha2, rd2⟩

end Benchmarks.Midnight
