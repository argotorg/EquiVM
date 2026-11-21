import Benchmarks.Midnight.TakeEntry

/-! The fixed spill slots produced by take's entry decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem takeEntryMemory_size {mem bytes : ByteArray} (hm : 832 ≤ mem.size) :
    (takeEntryMemory mem bytes).size = mem.size := by
  rw [takeEntryMemory, takeScalarsMemory_size, offerPrepareMemory_size hm]
  omega

theorem takeEntryMemory_load {mem bytes : ByteArray} (hm : 832 ≤ mem.size) (read : UInt256)
    (hin : read.toNat + 32 ≤ mem.size) (hlo : 96 ≤ read.toNat)
    (h192 : read.toNat + 32 ≤ 192 ∨ 224 ≤ read.toNat)
    (h288 : read.toNat + 32 ≤ 288 ∨ 320 ≤ read.toNat)
    (h384 : read.toNat + 32 ≤ 384 ∨ 416 ≤ read.toNat)
    (h544 : read.toNat + 32 ≤ 544 ∨ 576 ≤ read.toNat) :
    memLoad read (takeEntryMemory mem bytes) = memLoad read mem := by
  simp (disch := first | assumption | (try simp only [writeWord_sparse_size]; omega)) only
    [takeEntryMemory, takeScalarsMemory, offerPrepareMemory, memLoad_writeWord_preserved]
  rw [memLoad_writeWord_preserved _ 64 read _ (by rw [writeWord_sparse_size]; omega)
    (Or.inr hlo), memLoad_writeWord_preserved _ 384 read _ hin h384]

theorem takeEntryMemory_root {mem bytes : ByteArray} (hm : 832 ≤ mem.size) :
    memLoad (UInt256.ofNat 384) (takeEntryMemory mem bytes) = ⟨832⟩ := by
  simp (disch := first | assumption | decide +kernel |
    (try simp only [writeWord_sparse_size,
      show (UInt256.ofNat 384).toNat = 384 from rfl,
      show (UInt256.ofNat 544).toNat = 544 from rfl,
      show (UInt256.ofNat 288).toNat = 288 from rfl]; omega)) only
    [takeEntryMemory, takeScalarsMemory, offerPrepareMemory,
      memLoad_writeWord_preserved, memLoad_writeWord]
  exact memLoad_writeWord _ (UInt256.ofNat 384) _

theorem takeEntryMemory_taker {mem bytes : ByteArray} (hm : 832 ≤ mem.size) :
    memLoad (UInt256.ofNat 544) (takeEntryMemory mem bytes) = calldataWord bytes 100 := by
  simp (disch := first | assumption | decide +kernel |
    (try simp only [writeWord_sparse_size,
      show (UInt256.ofNat 384).toNat = 384 from rfl,
      show (UInt256.ofNat 544).toNat = 544 from rfl,
      show (UInt256.ofNat 288).toNat = 288 from rfl]; omega)) only
    [takeEntryMemory, takeScalarsMemory, offerPrepareMemory,
      memLoad_writeWord_preserved, memLoad_writeWord]
  exact memLoad_writeWord _ (UInt256.ofNat 544) _

theorem takeEntryMemory_receiver {mem bytes : ByteArray} (hm : 832 ≤ mem.size) :
    memLoad (UInt256.ofNat 288) (takeEntryMemory mem bytes) = calldataWord bytes 132 := by
  simp (disch := first | assumption | decide +kernel |
    (try simp only [writeWord_sparse_size,
      show (UInt256.ofNat 384).toNat = 384 from rfl,
      show (UInt256.ofNat 544).toNat = 544 from rfl,
      show (UInt256.ofNat 288).toNat = 288 from rfl]; omega)) only
    [takeEntryMemory, takeScalarsMemory, offerPrepareMemory,
      memLoad_writeWord_preserved, memLoad_writeWord]
  exact memLoad_writeWord _ (UInt256.ofNat 288) _

theorem takeEntryMemory_callback (mem bytes : ByteArray) :
    memLoad (UInt256.ofNat 192) (takeEntryMemory mem bytes) = calldataWord bytes 164 :=
  memLoad_writeWord _ _ _

end Benchmarks.Midnight
