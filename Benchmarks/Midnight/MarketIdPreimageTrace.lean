import Benchmarks.Midnight.MarketIdMemory
import Benchmarks.Midnight.MarketBytesMemory
import Benchmarks.Midnight.AllocationArithmetic
import Benchmarks.Midnight.RuntimeBlocks_078

variable {fork : Ethereum.Fork}

/-! Hashing the initialization code and assembling the final CREATE2 preimage. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMarketIdPreimage {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root ptr : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (m : MarketData) (hstack : R.length + 8 ≤ 1024)
    (hbound : root.toNat + 128 < 2^64) (hptr : ptr.toNat + 32 < UInt256.size)
    (hsmall : 11 + m.encodingSize < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hlen : memLoad ptr mem = UInt256.ofNat (11 + m.encodingSize))
    (hbytes : mem.readWithPadding (ptr.toNat + 32) (11 + m.encodingSize) = m.initcode)
    (rd : RD fork midnightBytecode I g s0 ⟨20659⟩
      (ptr :: (ptr + UInt256.ofNat 32) :: UInt256.ofNat m.midnight.val :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨20728⟩ (root :: (root + UInt256.ofNat 32) :: R)
      (marketIdMemory mem root m) aw' rdata σ k' C' := by
  have hh : keccakWord (ptr + UInt256.ofNat 32) (UInt256.ofNat (11 + m.encodingSize)) mem =
      uInt256OfByteArray (KEC m.initcode) := by
    rw [keccakWord, uadd_word_ofNat_toNat _ _ hptr, UInt256.toNat_ofNat_of_lt hsmall, hbytes]
    exact (uInt256OfByteArray_eq _).symm
  have ha (n : Nat) (hn : n ≤ 128) : (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have he : allocationEnd root (UInt256.ofNat 117) = root + UInt256.ofNat 128 := rfl
  have hc : allocationCheck root (allocationEnd root (UInt256.ofNat 117)) = ⟨0⟩ :=
    allocationCheck_bounded (by decide) (by simpa using hbound)
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_20659_packed (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_20659_stack,
    midnightBlocks.midnight_block_20659_memory, hfree, hlen, hh, packedAddressMask,
    ha 32 (by decide), ha 33 (by decide), ha 53 (by decide), ha 85 (by decide)] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := midnightAllocate
    (by simp only [List.length_cons]; omega) hc (by jump_dest) rd1
  rw [he] at rd2
  refine ⟨aw2, k2, C2, ?_⟩
  simpa only [marketIdMemory, marketIdPayload, writeWordArray, Reasoning.Theory.writeWord,
    Nat.add_assoc, Nat.reduceAdd] using rd2

end Benchmarks.Midnight
