import Benchmarks.Midnight.MarketValueDecode
import Benchmarks.Midnight.MemoryBytes
import Benchmarks.Midnight.MemoryAddressDecode

variable {fork : Ethereum.Fork}

/-! The market fields decoded after the collateral loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def marketTailWords (bytes : ByteArray) (start : Nat) (arrayPtr : UInt256) : List UInt256 :=
  [arrayPtr, calldataWord bytes (start + 128), calldataWord bytes (start + 160),
    calldataWord bytes (start + 192)]

def marketTailMemory (mem : ByteArray) (ptr arrayPtr : UInt256) (bytes : ByteArray) (start : Nat) :
    ByteArray := writeWordArray mem (ptr.toNat + 96) (marketTailWords bytes start arrayPtr)

theorem midnightToMarketLastFields {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem bytes rdata : ByteArray} {aw ptr arrayPtr anchor x0 x1 x2 x3 : UInt256} {σ : AccountMap}
    {base start k C : Nat} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hbytes : MemoryBytes mem base bytes) (hhead : start + 256 ≤ bytes.size)
    (hanchor : anchor.toNat + 32 = base + start)
    (hregion : base + bytes.size ≤ ptr.toNat) (hptr : ptr.toNat + 256 < 2^64)
    (rd : RD fork midnightBytecode I g s0 ⟨1100⟩
      (x0 :: x1 :: x2 :: x3 :: arrayPtr :: ptr :: anchor :: R) mem aw rdata σ k C) :
    (decodeMarketData bytes start = none ∧ RDrev fork midnightBytecode g s0) ∨
    ((calldataWord bytes (start + 192)).toNat < EVM.addressModulus ∧
      (calldataWord bytes (start + 224)).toNat < EVM.addressModulus ∧
      ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨1159⟩
        (calldataWord bytes (start + 224) :: ptr :: ⟨1184⟩ ::
          x0 :: x1 :: x2 :: x3 :: arrayPtr :: ptr :: anchor :: R)
        (marketTailMemory mem ptr arrayPtr bytes start) aw' rdata σ k' C') := by
  have load {m : ByteArray} (hb : MemoryBytes m base bytes) (off : Nat) (ho : off + 32 ≤ 256) :
      memLoad (anchor + UInt256.ofNat (32 + off)) m = calldataWord bytes (start + off) := by
    apply hb.load_word (by omega)
    rw [uadd_word_ofNat_toNat _ _ (by have h := hb.bound; omega)]
    omega
  have add (off : Nat) (ho : off ≤ 224) : (ptr + UInt256.ofNat off).toNat = ptr.toNat + off :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  let m1 := writeWord mem (ptr + UInt256.ofNat 96).toNat arrayPtr
  have hb1 : MemoryBytes m1 base bytes := hbytes.writeWord _ (Or.inl (by rw [add 96 (by decide)]; omega))
  have h128 : memLoad (anchor + UInt256.ofNat 160) m1 = calldataWord bytes (start + 128) :=
    load hb1 128 (by decide)
  let m2 := writeWord m1 (ptr + UInt256.ofNat 128).toNat (calldataWord bytes (start + 128))
  have hb2 : MemoryBytes m2 base bytes := hb1.writeWord _ (Or.inl (by rw [add 128 (by decide)]; omega))
  have h160 : memLoad (anchor + UInt256.ofNat 192) m2 = calldataWord bytes (start + 160) :=
    load hb2 160 (by decide)
  let m3 := writeWord m2 (ptr + UInt256.ofNat 160).toNat (calldataWord bytes (start + 160))
  have hb3 : MemoryBytes m3 base bytes := hb2.writeWord _ (Or.inl (by rw [add 160 (by decide)]; omega))
  have h192 : memLoad (anchor + UInt256.ofNat 224) m3 = calldataWord bytes (start + 192) :=
    load hb3 192 (by decide)
  have hmem : midnightBlocks.midnight_block_1100_memory (mem := mem)
      (x4 := arrayPtr) (x5 := ptr) (x6 := anchor) = m3 := by
    change writeWord (writeWord m1 (ptr + UInt256.ofNat 128).toNat
      (memLoad (anchor + UInt256.ofNat 160) m1)) (ptr + UInt256.ofNat 160).toNat
      (memLoad (anchor + UInt256.ofNat 192)
        (writeWord m1 (ptr + UInt256.ofNat 128).toNat (memLoad (anchor + UInt256.ofNat 160) m1))) = m3
    rw [h128]
    change writeWord m2 (ptr + UInt256.ofNat 160).toNat
      (memLoad (anchor + UInt256.ofNat 192) m2) = m3
    rw [h160]
  have rd1 := midnightBlocks.midnight_block_1100 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_1100_stack, hmem] at rd1
  by_cases he : (calldataWord bytes (start + 192)).toNat < EVM.addressModulus
  · obtain ⟨aw2, k2, C2, rd2⟩ := midnightMemoryAddress_ok
      (by simp only [List.length_cons]; omega) (by rw [h192]; exact he) (by jump_dest) rd1
    rw [h192] at rd2
    let m4 := writeWord m3 (ptr + UInt256.ofNat 192).toNat (calldataWord bytes (start + 192))
    have hb4 : MemoryBytes m4 base bytes := hb3.writeWord _ (Or.inl (by rw [add 192 (by decide)]; omega))
    have h224 : memLoad (anchor + UInt256.ofNat 256) m4 = calldataWord bytes (start + 224) :=
      load hb4 224 (by decide)
    have rd3 := midnightBlocks.midnight_block_1148
      (by simp only [List.length_cons]; omega) (by jump_dest) rd2
    simp only [midnightBlocks.midnight_block_1148_stack, midnightBlocks.midnight_block_1148_memory] at rd3
    change RD fork midnightBytecode I g s0 ⟨23130⟩
      ((anchor + UInt256.ofNat 256) :: ⟨1159⟩ :: ptr :: ⟨1184⟩ ::
        x0 :: x1 :: x2 :: x3 :: arrayPtr :: ptr :: anchor :: R) m4 _ rdata σ _ _ at rd3
    by_cases hl : (calldataWord bytes (start + 224)).toNat < EVM.addressModulus
    · right
      refine ⟨he, hl, ?_⟩
      obtain ⟨aw4, k4, C4, rd4⟩ := midnightMemoryAddress_ok
        (by simp only [List.length_cons]; omega) (by rw [h224]; exact hl) (by jump_dest) rd3
      rw [h224] at rd4
      have hm4 : m4 = marketTailMemory mem ptr arrayPtr bytes start := by
        simp only [m4, m3, m2, m1, marketTailMemory, marketTailWords, writeWordArray,
          add 96 (by decide), add 128 (by decide), add 160 (by decide), add 192 (by decide),
          Nat.add_assoc, Nat.reduceAdd]
      rw [hm4] at rd4
      exact ⟨aw4, k4, C4, rd4⟩
    · left
      refine ⟨by simp [decodeMarketData, MarketData.canonicalAt, hl], ?_⟩
      exact midnightMemoryAddress_bad (by simp only [List.length_cons]; omega)
        (by rw [h224]; exact hl) rd3
  · left
    refine ⟨by simp [decodeMarketData, MarketData.canonicalAt, he], ?_⟩
    exact midnightMemoryAddress_bad (by simp only [List.length_cons]; omega)
      (by rw [h192]; exact he) rd1

end Benchmarks.Midnight
