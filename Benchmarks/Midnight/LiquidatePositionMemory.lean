import Benchmarks.Midnight.PositionUpdateMemory
import Benchmarks.Midnight.MarketBytesMemory

/-! The liquidation prologue saves its market and computes the borrower's position slot. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: fold the opcode form of a full memory-word write.
theorem writeWord_fold (mem : ByteArray) (off : Nat) (word : UInt256) :
    word.toByteArray.write 0 mem off 32 = writeWord mem off word := rfl

-- LIBRARY CANDIDATE: a scratch-word write preserves every later complete word.
theorem memLoad_wordAt0Mem {mem : ByteArray} (word read : UInt256)
    (hlo : 32 ≤ read.toNat) (hhi : read.toNat + 32 ≤ mem.size) :
    memLoad read (wordAt0Mem word mem) = memLoad read mem :=
  memLoad_writeWord_preserved mem 0 read word hhi (Or.inr hlo)

theorem MarketStored.writeWord_below {mem : ByteArray} {ptr arrayPtr root : UInt256}
    {m : MarketData} {off : Nat} (h : MarketStored mem ptr arrayPtr root m)
    (word : UInt256) (hbelow : off + 32 ≤ ptr.toNat) :
    MarketStored (writeWord mem off word) ptr arrayPtr root m := by
  have ha := h.array
  have he := h.extent
  have hb := h.bound
  refine ⟨h.words.writeWord word (Or.inr hbelow),
    h.header.writeWord word (Or.inr (by omega)),
    h.collaterals.writeWord_below word hb ?_, h.lower, ha, he, hb⟩
  rw [uadd_word_ofNat_toNat _ 32 (by change _ < 2^256; omega)]
  omega

def liquidateIdMemory (mem : ByteArray) (id : UInt256) : ByteArray :=
  writeWord mem 768 id

def liquidateMarketMemory (mem : ByteArray) (id : UInt256) : ByteArray :=
  writeWord (twoWordHashMem id ⟨1⟩ (liquidateIdMemory mem id)) 672
    (solcMappingSlot ⟨1⟩ id)

def liquidatePositionMemory (mem : ByteArray) (id borrower : UInt256) : ByteArray :=
  positionReadMemory (liquidateMarketMemory mem id) id borrower

theorem liquidateIdMemory_size {mem : ByteArray} (id : UInt256) (hm : 832 ≤ mem.size) :
    (liquidateIdMemory mem id).size = mem.size := by
  rw [liquidateIdMemory, writeWord_sparse_size]
  omega

theorem liquidateIdMemory_id (mem : ByteArray) (id : UInt256) :
    memLoad (UInt256.ofNat 768) (liquidateIdMemory mem id) = id :=
  memLoad_writeWord _ _ _

theorem liquidateIdMemory_load {mem : ByteArray} (id read : UInt256)
    (hi : read.toNat + 32 ≤ mem.size) (hd : read.toNat + 32 ≤ 768 ∨ 800 ≤ read.toNat) :
    memLoad read (liquidateIdMemory mem id) = memLoad read mem :=
  memLoad_writeWord_preserved _ _ _ _ hi hd

theorem liquidateMarketMemory_size {mem : ByteArray} (id : UInt256) (hm : 832 ≤ mem.size) :
    (liquidateMarketMemory mem id).size = mem.size := by
  rw [liquidateMarketMemory, writeWord_sparse_size,
    twoWordHashMem_size_of_ge_64 _ _ (by rw [liquidateIdMemory_size id hm]; omega),
    liquidateIdMemory_size id hm]
  omega

theorem liquidateMarketMemory_id {mem : ByteArray} (id : UInt256) (hm : 832 ≤ mem.size) :
    memLoad (UInt256.ofNat 768) (liquidateMarketMemory mem id) = id := by
  have hs : 800 ≤ (liquidateIdMemory mem id).size := by
    rw [liquidateIdMemory_size id hm]; omega
  rw [liquidateMarketMemory, memLoad_writeWord_preserved _ _ _ _ (by
      change 800 ≤ _
      rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; exact hs) (Or.inr (by decide)),
    memLoad_twoWordHashMem _ _ (UInt256.ofNat 768) (by decide) hs, liquidateIdMemory_id]

theorem liquidateMarketMemory_load {mem : ByteArray} (id read : UInt256)
    (hm : 832 ≤ mem.size) (hlo : 64 ≤ read.toNat) (hi : read.toNat + 32 ≤ mem.size)
    (hd : read.toNat + 32 ≤ 672 ∨ 704 ≤ read.toNat)
    (hid : read.toNat + 32 ≤ 768 ∨ 800 ≤ read.toNat) :
    memLoad read (liquidateMarketMemory mem id) = memLoad read mem := by
  have hs : 64 ≤ (liquidateIdMemory mem id).size := by
    rw [liquidateIdMemory_size id hm]; omega
  rw [liquidateMarketMemory, memLoad_writeWord_preserved _ _ _ _ (by
      rw [twoWordHashMem_size_of_ge_64 _ _ hs, liquidateIdMemory_size id hm]; exact hi) hd,
    memLoad_twoWordHashMem _ _ _ hlo (by rw [liquidateIdMemory_size id hm]; exact hi),
    liquidateIdMemory_load id read hi hid]

theorem liquidatePositionMemory_size {mem : ByteArray} (id borrower : UInt256)
    (hm : 832 ≤ mem.size) : (liquidatePositionMemory mem id borrower).size = mem.size := by
  rw [liquidatePositionMemory, positionReadMemory_size _ _ _ (by
    rw [liquidateMarketMemory_size id hm]; omega), liquidateMarketMemory_size id hm]

theorem liquidatePositionMemory_load {mem : ByteArray} (id borrower read : UInt256)
    (hm : 832 ≤ mem.size) (hlo : 64 ≤ read.toNat) (hi : read.toNat + 32 ≤ mem.size)
    (hd : read.toNat + 32 ≤ 672 ∨ 704 ≤ read.toNat)
    (hid : read.toNat + 32 ≤ 768 ∨ 800 ≤ read.toNat) :
    memLoad read (liquidatePositionMemory mem id borrower) = memLoad read mem := by
  rw [liquidatePositionMemory, positionReadMemory,
    memLoad_twoWordHashMem _ _ _ hlo (by
      rw [twoWordHashMem_size_of_ge_64 _ _ (by
        rw [liquidateMarketMemory_size id hm]; omega), liquidateMarketMemory_size id hm]
      exact hi), memLoad_twoWordHashMem _ _ _ hlo (by
      rw [liquidateMarketMemory_size id hm]; exact hi),
    liquidateMarketMemory_load id read hm hlo hi hd hid]

theorem liquidatePositionMemory_market {mem : ByteArray} {ptr arrayPtr root id borrower : UInt256}
    {m : MarketData} (h : MarketStored mem ptr arrayPtr root m) (hp : 832 ≤ ptr.toNat) :
    MarketStored (liquidatePositionMemory mem id borrower) ptr arrayPtr root m := by
  unfold liquidatePositionMemory liquidateMarketMemory liquidateIdMemory
  apply MarketStored.preserve _ (positionReadMemory_prefix _ _ _ _)
  apply MarketStored.writeWord_below _ _ (by omega)
  apply MarketStored.preserve _ (twoWordHashMem_prefix _ _ _ _)
  exact h.writeWord_below _ (by omega)

end Benchmarks.Midnight
