import Benchmarks.Midnight.CalldataBoolUint128
import Benchmarks.Midnight.LiquidatePositionMemory
import Benchmarks.Midnight.RuntimeBlocks_040
import Benchmarks.Midnight.RuntimeBlocks_041

/-! Fixed offer-field stores before the first dynamic byte-string allocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem offerRoot_writeWord (mem : ByteArray) (off : Nat) (word : UInt256)
    (hm : 416 ≤ mem.size) (ho : 416 ≤ off) :
    memLoad (UInt256.ofNat 384) (writeWord mem off word) = memLoad (UInt256.ofNat 384) mem :=
  memLoad_writeWord_preserved _ _ _ _ hm (Or.inl ho)

theorem offerRoot_writeBytes (mem : ByteArray) (off : Nat) (word : UInt256)
    (hm : 416 ≤ mem.size) (ho : 416 ≤ off) :
    memLoad (UInt256.ofNat 384) (word.toByteArray.write 0 mem off 32) =
      memLoad (UInt256.ofNat 384) mem := offerRoot_writeWord mem off word hm ho

def offerMiddleWords (bytes : ByteArray) (base : Nat) (maker : UInt256) : List UInt256 :=
  [maker, calldataWord bytes (base + 96), calldataWord bytes (base + 128),
    calldataWord bytes (base + 160), calldataWord bytes (base + 192)]

def offerMiddleMemory (mem bytes : ByteArray) (base : Nat) (maker : UInt256) : ByteArray :=
  writeWordArray mem 896 (offerMiddleWords bytes base maker)

theorem midnightOfferStoreMarket {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw market rel : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨10530⟩ (market :: rel :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (writeWord mem 832 market) aw' C' ∧
      RD midnightBytecode I g s0 ⟨19003⟩
        ((rel + UInt256.ofNat 36) :: ⟨10547⟩ :: rel :: R)
        (writeWord mem 832 market) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_10530 hstack (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_10530_memory
    memory_fund ha)
  simp only [midnightBlocks.midnight_block_10530_stack,
    midnightBlocks.midnight_block_10530_memory, hroot] at ha1 rd1
  exact ⟨_, _, _, ha1, rd1⟩

theorem midnightOfferStoreBuy {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw buy rel : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨10547⟩ (buy :: rel :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (writeWord mem 864 buy) aw' C' ∧
      RD midnightBytecode I g s0 ⟨18342⟩
        ((rel + UInt256.ofNat 68) :: ⟨10567⟩ :: rel :: R)
        (writeWord mem 864 buy) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_10547 hstack (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_10547_memory
    memory_fund ha)
  simp only [midnightBlocks.midnight_block_10547_stack,
    midnightBlocks.midnight_block_10547_memory, hroot] at ha1 rd1
  exact ⟨_, _, _, ha1, rd1⟩

set_option maxHeartbeats 800000 in
theorem midnightOfferStoreMiddle {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw maker rel : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (hrel : rel.toNat < 2^64) (hm : 416 ≤ mem.size)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨10567⟩ (maker :: rel :: R) mem aw rdata σ k C) :
    ∃ aw' k' C',
      MemoryFunding credit (offerMiddleMemory mem I.calldata (rel.toNat + 4) maker) aw' C' ∧
      RD midnightBytecode I g s0 ⟨18342⟩
        ((rel + UInt256.ofNat 228) :: ⟨10639⟩ :: rel :: R)
        (offerMiddleMemory mem I.calldata (rel.toNat + 4) maker) aw' rdata σ k' C' := by
  have hadd (off : Nat) (ho : off ≤ 228) :
      (rel + UInt256.ofNat off).toNat = rel.toNat + off :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have rd1 := midnightBlocks.midnight_block_10567 hstack (by jump_dest) rd
  simp (disch := first | assumption | decide +kernel |
    (simp only [writeWord_fold, writeWord_sparse_size]; omega)) only
    [midnightBlocks.midnight_block_10567_stack, midnightBlocks.midnight_block_10567_memory,
      offerRoot_writeBytes, hroot] at rd1
  have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
  simp only [hadd 100 (by decide), hadd 132 (by decide), hadd 164 (by decide),
    hadd 196 (by decide)] at ha1 rd1
  simp only [offerMiddleMemory, offerMiddleWords, writeWordArray, Nat.add_assoc, Nat.reduceAdd]
  exact ⟨_, _, _, ha1, rd1⟩

end Benchmarks.Midnight
