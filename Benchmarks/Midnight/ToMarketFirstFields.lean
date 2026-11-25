import Benchmarks.Midnight.MarketValueDecode
import Benchmarks.Midnight.MemoryBytes
import Benchmarks.Midnight.MemoryAddressDecode

variable {fork : Ethereum.Fork}

/-! The first three stored-market fields and the collateral-array offset check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def marketFirstWords (bytes : ByteArray) (start : Nat) : List UInt256 :=
  [calldataWord bytes start, calldataWord bytes (start + 32), calldataWord bytes (start + 64)]

def marketFirstMemory (mem : ByteArray) (ptr : UInt256) (bytes : ByteArray) (start : Nat) : ByteArray :=
  writeWordArray mem ptr.toNat (marketFirstWords bytes start)

theorem midnightToMarketFirstFields {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem bytes rdata : ByteArray} {aw ptr anchor x y : UInt256} {σ : AccountMap}
    {base start k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hbytes : MemoryBytes mem base bytes) (hhead : start + 256 ≤ bytes.size)
    (hanchor : anchor.toNat + 32 = base + start)
    (hregion : base + bytes.size ≤ ptr.toNat) (hptr : ptr.toNat + 256 < 2^64)
    (rd : RD fork midnightBytecode I g s0 ⟨961⟩ (x :: y :: ptr :: anchor :: R)
      mem aw rdata σ k C) :
    (decodeMarketData bytes start = none ∧ RDrev fork midnightBytecode g s0) ∨
    ((calldataWord bytes (start + 32)).toNat < EVM.addressModulus ∧
      (calldataWord bytes (start + 64)).toNat < EVM.addressModulus ∧
      (calldataWord bytes (start + 96)).toNat < 2^64 ∧
      ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨1022⟩
        (calldataWord bytes (start + 96) :: x :: y :: ptr :: anchor :: R)
        (marketFirstMemory mem ptr bytes start) aw' rdata σ k' C') := by
  have load {m : ByteArray} (hb : MemoryBytes m base bytes) (off : Nat) (ho : off + 32 ≤ 256) :
      memLoad (anchor + UInt256.ofNat (32 + off)) m = calldataWord bytes (start + off) := by
    apply hb.load_word (by omega)
    rw [uadd_word_ofNat_toNat _ _ (by have h := hb.bound; omega)]
    omega
  have h0 : memLoad (anchor + UInt256.ofNat 32) mem = calldataWord bytes start := by
    simpa only [Nat.add_zero] using load hbytes 0 (by decide)
  let m1 := writeWord mem ptr.toNat (calldataWord bytes start)
  have hb1 : MemoryBytes m1 base bytes := hbytes.writeWord _ (Or.inl hregion)
  have h32 : memLoad (anchor + UInt256.ofNat 64) m1 = calldataWord bytes (start + 32) :=
    load hb1 32 (by decide)
  have rd1 := midnightBlocks.midnight_block_961 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_961_stack, midnightBlocks.midnight_block_961_memory,
    h0] at rd1
  change RD fork midnightBytecode I g s0 ⟨23130⟩
    ((anchor + UInt256.ofNat 64) :: ⟨980⟩ :: x :: y :: ptr :: anchor :: R) m1 _ rdata σ _ _ at rd1
  by_cases hm : (calldataWord bytes (start + 32)).toNat < EVM.addressModulus
  · obtain ⟨aw2, k2, C2, rd2⟩ := midnightMemoryAddress_ok
      (by simp only [List.length_cons]; omega) (by rw [h32]; exact hm) (by jump_dest) rd1
    rw [h32] at rd2
    have hp32 : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
    let m2 := writeWord m1 (ptr.toNat + 32) (calldataWord bytes (start + 32))
    have hb2 : MemoryBytes m2 base bytes := hb1.writeWord _ (Or.inl (by omega))
    have h64 : memLoad (anchor + UInt256.ofNat 96) m2 = calldataWord bytes (start + 64) :=
      load hb2 64 (by decide)
    have rd3 := midnightBlocks.midnight_block_980 (by omega) (by jump_dest) rd2
    simp only [midnightBlocks.midnight_block_980_stack, midnightBlocks.midnight_block_980_memory,
      hp32] at rd3
    change RD fork midnightBytecode I g s0 ⟨23130⟩
      ((anchor + UInt256.ofNat 96) :: ⟨997⟩ :: x :: y :: ptr :: anchor :: R) m2 _ rdata σ _ _ at rd3
    by_cases hl : (calldataWord bytes (start + 64)).toNat < EVM.addressModulus
    · obtain ⟨aw4, k4, C4, rd4⟩ := midnightMemoryAddress_ok
        (by simp only [List.length_cons]; omega) (by rw [h64]; exact hl) (by jump_dest) rd3
      rw [h64] at rd4
      have hp64 : (ptr + UInt256.ofNat 64).toNat = ptr.toNat + 64 :=
        uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
      let m3 := writeWord m2 (ptr.toNat + 64) (calldataWord bytes (start + 64))
      have hb3 : MemoryBytes m3 base bytes := hb2.writeWord _ (Or.inl (by omega))
      have h96 : memLoad (anchor + UInt256.ofNat 128) m3 = calldataWord bytes (start + 96) :=
        load hb3 96 (by decide)
      have hmem : (calldataWord bytes (start + 64)).toByteArray.write 0 m2
          (ptr + UInt256.ofNat 64).toNat 32 = marketFirstMemory mem ptr bytes start := by
        rw [hp64]
        simp only [marketFirstMemory, marketFirstWords, writeWordArray, Nat.add_assoc, Nat.reduceAdd]
        rfl
      by_cases hoff : (calldataWord bytes (start + 96)).toNat < 2^64
      · right
        refine ⟨hm, hl, hoff, ?_⟩
        have hg : UInt256.gt (memLoad (anchor + UInt256.ofNat 128) m3)
            (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
              (UInt256.ofNat 1)) = ⟨0⟩ := by
          rw [h96]
          apply ugt_zero
          change _ ≤ 18446744073709551615
          omega
        have rd5 := midnightBlocks.midnight_block_997_fallthrough (by omega)
          (by rw [hp64]; exact hg) rd4
        simp only [midnightBlocks.midnight_block_997_fallthrough_stack,
          midnightBlocks.midnight_block_997_fallthrough_memory, hmem] at rd5
        have hload : memLoad (anchor + UInt256.ofNat 128)
            (marketFirstMemory mem ptr bytes start) = calldataWord bytes (start + 96) := by
          rw [← hmem, hp64]
          exact h96
        rw [hload] at rd5
        exact ⟨_, _, _, rd5⟩
      · left
        refine ⟨?_, ?_⟩
        · have hc : solcMaxU64 < (calldataWord bytes (start + 96)).toNat := by
            change 18446744073709551615 < _; omega
          simp [decodeMarketData, hc]
        · have hg : UInt256.gt (memLoad (anchor + UInt256.ofNat 128) m3)
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
                (UInt256.ofNat 1)) = ⟨1⟩ := by
            rw [h96]
            apply ugt_one
            change 18446744073709551615 < _
            omega
          have rd5 := midnightBlocks.midnight_block_997_taken (by omega)
            (by
              rw [hp64]
              change UInt256.gt (memLoad (anchor + UInt256.ofNat 128) m3) _ ≠ _
              rw [hg]
              decide) (by jump_dest) rd4
          exact midnightBlocks.midnight_block_712 (by
            simp only [midnightBlocks.midnight_block_997_taken_stack, List.length_cons]; omega) rd5
    · left
      refine ⟨by simp [decodeMarketData, MarketData.canonicalAt, hl], ?_⟩
      exact midnightMemoryAddress_bad (by simp only [List.length_cons]; omega)
        (by rw [h64]; exact hl) rd3
  · left
    refine ⟨by simp [decodeMarketData, MarketData.canonicalAt, hm], ?_⟩
    exact midnightMemoryAddress_bad (by simp only [List.length_cons]; omega)
      (by rw [h32]; exact hm) rd1

end Benchmarks.Midnight
