import Benchmarks.EAS.Attester.StructAllocMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

def attestCellHeaderMemory (mem : ByteArray) (free : Nat) : ByteArray :=
  writeCascade mem [(64, UInt256.ofNat (free + 192)), (free, ⟨0⟩), (free + 32, ⟨0⟩),
    (free + 64, ⟨1⟩), (free + 96, ⟨0⟩)]

def attestCellPayloadMemory (mem : ByteArray) (free : Nat) (input : UInt256) : ByteArray :=
  writeWord (attestCellHeaderMemory mem free) (free + 224) input

def attestCellMemory (mem : ByteArray) (free : Nat) (input : UInt256) : ByteArray :=
  writeCascade (attestCellPayloadMemory mem free input)
    [(free + 192, ⟨32⟩), (64, UInt256.ofNat (free + 256)),
      (free + 128, UInt256.ofNat (free + 192)), (free + 160, ⟨0⟩)]

def attestCellSlotMemory (mem : ByteArray) (free slot : Nat) (input : UInt256) : ByteArray :=
  writeWord (attestCellMemory mem free input) slot (UInt256.ofNat free)

theorem attestCellHeaderMemory_freePtr {mem : ByteArray} {free : Nat} (hfree : 96 ≤ free) :
    memLoad (UInt256.ofNat 64) (attestCellHeaderMemory mem free) = UInt256.ofNat (free + 192) := by
  simp only [attestCellHeaderMemory, writeCascade, Reasoning.Theory.writeWord]
  simp (disch := (simp only [wordWrite_size,
    show (UInt256.ofNat 64).toNat = 64 from rfl]; omega)) only
    [memLoad_write_disjoint, memLoad_write_same]
  exact memLoad_write_same _ _ _ _ rfl

theorem attestCellPayloadMemory_freePtr {mem : ByteArray} {free : Nat} {input : UInt256}
    (hfree : 96 ≤ free) :
    memLoad (UInt256.ofNat 64) (attestCellPayloadMemory mem free input) =
      UInt256.ofNat (free + 192) := by
  unfold attestCellPayloadMemory Reasoning.Theory.writeWord
  rw [memLoad_write_disjoint]
  · exact attestCellHeaderMemory_freePtr hfree
  all_goals simp only [attestCellHeaderMemory, writeCascade, Reasoning.Theory.writeWord,
    wordWrite_size, show (UInt256.ofNat 64).toNat = 64 from rfl] <;> omega

theorem attestCellMemory_freePtr {mem : ByteArray} {free : Nat} {input : UInt256}
    (hfree : 96 ≤ free) :
    memLoad (UInt256.ofNat 64) (attestCellMemory mem free input) =
      UInt256.ofNat (free + 256) := by
  simp only [attestCellMemory, writeCascade, Reasoning.Theory.writeWord]
  rw [memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_same]
  all_goals simp only [wordWrite_size, show (UInt256.ofNat 64).toNat = 64 from rfl] <;> omega

theorem attestCellMemory_size {mem : ByteArray} {free : Nat} {input : UInt256}
    (hfree : 96 ≤ free) :
    (attestCellMemory mem free input).size = max mem.size (free + 256) := by
  simp only [attestCellMemory, attestCellPayloadMemory, attestCellHeaderMemory,
    writeCascade, Reasoning.Theory.writeWord, wordWrite_size]
  omega

theorem attestCellMemory_prefix (mem : ByteArray) (free : Nat) (input : UInt256) :
    MemoryPrefix mem (attestCellMemory mem free input) free := by
  have hh : MemoryPrefix mem (attestCellHeaderMemory mem free) free := by
    apply memoryPrefix_sparse_cascade
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  exact (hh.trans (memoryPrefix_sparse_writeWord _ _ _ input (.inl (by omega)))).trans
    (memoryPrefix_sparse_cascade _ _ _ (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> simp <;> omega))

theorem attestCellSlotMemory_freePtr {mem : ByteArray} {free slot : Nat} {input : UInt256}
    (hfree : 96 ≤ free) (hslot : 96 ≤ slot) :
    memLoad (UInt256.ofNat 64) (attestCellSlotMemory mem free slot input) =
      UInt256.ofNat (free + 256) := by
  unfold attestCellSlotMemory Reasoning.Theory.writeWord
  rw [memLoad_write_disjoint]
  · exact attestCellMemory_freePtr hfree
  · change 64 + 32 ≤ _
    rw [attestCellMemory_size hfree]; omega
  · exact .inl hslot

theorem attestCellSlotMemory_size {mem : ByteArray} {free slot : Nat} {input : UInt256}
    (hfree : 96 ≤ free) (hslot : slot + 32 ≤ free + 256) :
    (attestCellSlotMemory mem free slot input).size = max mem.size (free + 256) := by
  rw [attestCellSlotMemory, writeWord_sparse_size, attestCellMemory_size hfree]
  omega

theorem attestCellSlotMemory_prefix (mem : ByteArray) (free slot limit : Nat) (input : UInt256)
    (hf : limit ≤ free) (hs : limit ≤ slot) :
    MemoryPrefix mem (attestCellSlotMemory mem free slot input) limit :=
  ((attestCellMemory_prefix _ _ _).mono hf).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (.inl hs))

def attestFillMemory (mem : ByteArray) (free slots : Nat) (values : Nat → UInt256)
    (i : Nat) : Nat → ByteArray
  | 0 => mem
  | n + 1 => attestFillMemory (attestCellSlotMemory mem free (slots + 32 * i) (values i))
      (free + 256) slots values (i + 1) n

theorem attestFillMemory_freePtr {mem : ByteArray} {free slots i : Nat}
    {values : Nat → UInt256} (hfree : 96 ≤ free) (hslots : 96 ≤ slots)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free) (n : Nat) :
    memLoad (UInt256.ofNat 64) (attestFillMemory mem free slots values i n) =
      UInt256.ofNat (free + 256 * n) := by
  induction n generalizing mem free i with
  | zero => simpa only [attestFillMemory, Nat.mul_zero, Nat.add_zero] using hptr
  | succ n ih =>
      rw [attestFillMemory, ih (by omega) (attestCellSlotMemory_freePtr hfree (by omega))]
      congr 1; omega

theorem attestFillMemory_prefix (mem : ByteArray) (free slots limit i n : Nat)
    (values : Nat → UInt256) (hf : limit ≤ free) (hs : limit ≤ slots) :
    MemoryPrefix mem (attestFillMemory mem free slots values i n) limit := by
  induction n generalizing mem free i with
  | zero => exact .refl _ _
  | succ n ih =>
      exact (attestCellSlotMemory_prefix _ _ _ _ _ hf (by omega)).trans
        (ih _ _ _ (by omega))

theorem attestFillMemory_size {mem : ByteArray} {free slots i n : Nat} {values : Nat → UInt256}
    (hfree : 96 ≤ free) (hslots : slots + 32 * (i + n) ≤ free) (hn : 0 < n) :
    (attestFillMemory mem free slots values i n).size = max mem.size (free + 256 * n) := by
  induction n generalizing mem free i with
  | zero => omega
  | succ n ih =>
      rw [attestFillMemory]
      cases n with
      | zero =>
          simp only [attestFillMemory,
            attestCellSlotMemory_size (slot := slots + 32 * i) hfree (by omega)]
      | succ n =>
          rw [ih (by omega) (by omega) (by omega),
            attestCellSlotMemory_size (slot := slots + 32 * i) hfree (by omega)]
          omega

theorem attestFillMemory_length {mem : ByteArray} {free base i n len : Nat}
    {values : Nat → UInt256} (hbase : 96 ≤ base) (hin : base + 32 ≤ mem.size)
    (hf : base + 32 ≤ free) (hfit : base < UInt256.size)
    (hlen : memLoad (UInt256.ofNat base) mem = UInt256.ofNat len) :
    memLoad (UInt256.ofNat base) (attestFillMemory mem free (base + 32) values i n) =
      UInt256.ofNat len :=
  ((attestFillMemory_prefix _ _ _ (base + 32) _ _ _ hf (le_refl _)).load_preserved
    hbase (le_refl _) hin hfit).trans hlen

end Benchmarks.EAS.Attester
