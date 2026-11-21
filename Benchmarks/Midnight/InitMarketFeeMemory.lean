import Benchmarks.Midnight.InitMarketTickTrace
import Benchmarks.Midnight.AllocationArithmetic

/-! The seven copied default fees and their newly allocated memory region. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def initMarketSettlementFeeWords (word : UInt256) : List UInt256 :=
  [settlementFeeWord word 0, settlementFeeWord word 1, settlementFeeWord word 2,
    settlementFeeWord word 3, settlementFeeWord word 4, settlementFeeWord word 5,
    settlementFeeWord word 6]

def initMarketFeeMemory (mem : ByteArray) (root word : UInt256) : ByteArray :=
  writeWord (writeWordArray mem root.toNat (initMarketSettlementFeeWords word)) 64
    (root + UInt256.ofNat 224)

theorem initMarketSettlementFeeWords_get (word : UInt256) (i : Fin 7) :
    (initMarketSettlementFeeWords word)[i.val]'(by change i.val < 7; exact i.isLt) =
      settlementFeeWord word i.val := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;> rfl

theorem initMarketFeeMemory_words (mem : ByteArray) (root word : UInt256)
    (hroot : 96 ≤ root.toNat) (hb : root.toNat + 224 < UInt256.size) :
    MemoryWords (initMarketFeeMemory mem root word) root.toNat (initMarketSettlementFeeWords word) :=
  (MemoryWords.of_writeWordArray mem root.toNat (initMarketSettlementFeeWords word) hb (by simp [initMarketSettlementFeeWords])).writeWord
    (root + UInt256.ofNat 224) (Or.inr hroot)

theorem initMarketFeeMemory_prefix (mem : ByteArray) (root word : UInt256) (limit : Nat)
    (hlimit : limit ≤ root.toNat) : MemoryPrefix mem (initMarketFeeMemory mem root word) limit :=
  (memoryPrefix_writeWordArray mem root.toNat limit (initMarketSettlementFeeWords word) hlimit).trans
    (memoryPrefix_writeWord _ 64 limit _ (Or.inr (by decide)))

theorem initMarketFeeMemory_free (mem : ByteArray) (root word : UInt256) :
    memLoad (UInt256.ofNat 64) (initMarketFeeMemory mem root word) =
      root + UInt256.ofNat 224 := memLoad_writeWord ..

set_option maxRecDepth 2000000 in
theorem midnightInitMarketFeeCopy {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root word : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 13 ≤ 1024)
    (hb : root.toNat + 224 < 2^64)
    (rd : RD midnightBytecode I g s0 ⟨21213⟩
      (word :: (root + UInt256.ofNat 32) :: root :: word :: R)
      (writeWord mem root.toNat (settlementFeeWord word 0)) aw rdata σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g s0 ⟨21305⟩
      (root :: (root + UInt256.ofNat 32) :: (root + UInt256.ofNat 64) ::
        (root + UInt256.ofNat 96) :: (root + UInt256.ofNat 128) ::
        (root + UInt256.ofNat 160) :: (root + UInt256.ofNat 192) :: R)
      (initMarketFeeMemory mem root word) aw' rdata σ k' C' := by
  have hp (n : Nat) (hn : n ≤ 224) : (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_21213_packed (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_21213_stack] at rd1
  have hmemory : midnightBlocks.midnight_block_21213_memory
      (mem := writeWord mem root.toNat (settlementFeeWord word 0))
      (x0 := word) (x1 := root + UInt256.ofNat 32) (x2 := root) (x3 := word) =
      writeWordArray mem root.toNat (initMarketSettlementFeeWords word) := by
    simp only [midnightBlocks.midnight_block_21213_memory, initMarketSettlementFeeWords, writeWordArray,
      settlementFeeWord, u256_land_comm (UInt256.ofNat 65535), hp 32 (by omega),
      hp 64 (by omega), hp 96 (by omega), hp 128 (by omega), hp 160 (by omega), hp 192 (by omega),
      Nat.add_assoc, Nat.reduceAdd]
    rfl
  rw [hmemory] at rd1
  have he : allocationEnd root (UInt256.ofNat 224) = root + UInt256.ofNat 224 := by
    unfold allocationEnd
    rfl
  have hc : allocationCheck root (allocationEnd root (UInt256.ofNat 224)) = ⟨0⟩ := by
    rw [he]
    exact allocationCheck_ok (by rw [hp 224 le_rfl]; exact hb) (by rw [hp 224 le_rfl]; omega)
  obtain ⟨aw2, k2, C2, rd2⟩ := midnightAllocate (by simp only [List.length_cons]; omega)
    hc (by jump_dest) rd1
  rw [he] at rd2
  exact ⟨aw2, k2, C2, rd2⟩

end Benchmarks.Midnight
