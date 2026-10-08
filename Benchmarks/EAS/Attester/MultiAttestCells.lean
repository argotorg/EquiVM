import Benchmarks.EAS.Attester.MultiAttestMemory
import Benchmarks.EAS.Attester.PairCellMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

theorem multiAttestRowMemory_preserves {mem cd : ByteArray}
    {free base i schemaPtr uidPtr n off : Nat}
    (hlo : 96 ≤ off) (hin : off + 32 ≤ mem.size) (hfit : off < UInt256.size)
    (hf : off + 32 ≤ free)
    (hs : off + 32 ≤ base + 32 + 32 * i ∨ base + 64 + 32 * i ≤ off) :
    memLoad (UInt256.ofNat off) (multiAttestRowMemory mem cd free base i schemaPtr uidPtr n) =
      memLoad (UInt256.ofNat off) mem := by
  have hp := attestDataMemory_prefix mem cd free uidPtr n
  rw [multiAttestRowMemory,
    pairSlotMemory_preserves hlo (by have := hp.size; omega) hfit (by omega) (by omega)]
  exact hp.load_preserved hlo hf hin hfit

theorem multiAttestRowMemory_data_preserved {mem cd : ByteArray}
    {free base i schemaPtr uidPtr n off : Nat}
    (hfree : 96 ≤ free) (hslot : base + 64 + 32 * i ≤ free)
    (hn : 0 < n) (hfit : free + 32 + 480 * n < UInt256.size)
    (hlo : free ≤ off) (hhi : off + 32 ≤ free + 32 + 480 * n) :
    memLoad (UInt256.ofNat off) (multiAttestRowMemory mem cd free base i schemaPtr uidPtr n) =
      memLoad (UInt256.ofNat off) (attestDataMemory mem cd free uidPtr n) := by
  apply pairSlotMemory_preserves (by omega)
    (by rw [attestDataMemory_size hfree hn]; omega) (by omega) hhi (.inr (by omega))

theorem multiAttestRowMemory_slot {mem cd : ByteArray} {free base i schemaPtr uidPtr n : Nat}
    (hslot : base + 32 + 32 * i < UInt256.size) :
    memLoad (UInt256.ofNat (base + 32 + 32 * i))
      (multiAttestRowMemory mem cd free base i schemaPtr uidPtr n) =
        UInt256.ofNat (free + 32 + 480 * n) :=
  pairSlotMemory_slot hslot

theorem multiAttestRowMemory_fields {mem cd : ByteArray} {free base i schemaPtr uidPtr n : Nat}
    (hslot : base + 64 + 32 * i ≤ free) (hfit : free + 96 + 480 * n < UInt256.size) :
    memLoad (UInt256.ofNat (free + 32 + 480 * n))
        (multiAttestRowMemory mem cd free base i schemaPtr uidPtr n) =
          calldataWord cd (schemaPtr + 32 * i) ∧
      memLoad (UInt256.ofNat (free + 64 + 480 * n))
        (multiAttestRowMemory mem cd free base i schemaPtr uidPtr n) = UInt256.ofNat free := by
  constructor
  · exact pairSlotMemory_first (by omega) (by omega)
  · convert pairSlotMemory_second (mem := attestDataMemory mem cd free uidPtr n)
      (free := free + 32 + 480 * n) (slot := base + 32 + 32 * i)
      (first := calldataWord cd (schemaPtr + 32 * i)) (second := UInt256.ofNat free)
      (by omega) (by omega) using 1
    congr 2; omega

theorem multiAttestRowsMemory_preserves {mem cd : ByteArray}
    {free base schemaPtr i remaining off : Nat} {secondData : UInt256}
    (hspan : base + 32 + 32 * (i + remaining) ≤ free)
    (hlo : 96 ≤ off) (hin : off + 32 ≤ mem.size) (hfit : off < UInt256.size)
    (hf : off + 32 ≤ free)
    (hs : off + 32 ≤ base + 32 + 32 * i ∨ base + 32 + 32 * (i + remaining) ≤ off) :
    memLoad (UInt256.ofNat off)
      (multiAttestRowsMemory mem cd free base schemaPtr secondData i remaining) =
        memLoad (UInt256.ofNat off) mem := by
  induction remaining generalizing mem free i with
  | zero => rfl
  | succ remaining ih =>
      rw [multiAttestRowsMemory]
      have hp := multiAttestRowMemory_prefix mem cd free base i schemaPtr
        (rowData cd secondData i).toNat (rowLength cd secondData i).toNat (by omega)
      rw [ih (by omega) (by have := hp.size; omega) (by omega) (by omega)]
      exact multiAttestRowMemory_preserves hlo hin hfit hf (by omega)

end Benchmarks.EAS.Attester
