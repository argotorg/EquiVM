import Benchmarks.Midnight.MemoryPaid

variable {fork : Ethereum.Fork}

/-! Memory size and its cumulative gas payment, retained through runtime summaries. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem memoryWords_toNat (aw off len : UInt256) :
    (M aw off len).toNat = MachineState.M aw.toNat off.toNat len.toNat :=
  UInt256.toNat_ofNat_of_lt
    (MachineState.M_lt_uint256_size aw.val.isLt off.val.isLt len.val.isLt)

theorem memoryWords_ge (aw off len : UInt256) : aw.toNat ≤ (M aw off len).toNat := by
  rw [memoryWords_toNat]
  exact MachineState.M_ge_active _ _ _

theorem memoryWords_covers (aw off len : UInt256) (hlen : len.toNat ≠ 0) :
    off.toNat + len.toNat ≤ 32 * (M aw off len).toNat := by
  rw [memoryWords_toNat]
  unfold MachineState.M
  split
  · contradiction
  · omega

def MemoryCovered (mem : ByteArray) (aw : UInt256) : Prop := mem.size ≤ 32 * aw.toNat

theorem MemoryCovered.expand {mem : ByteArray} {aw : UInt256} (off len : UInt256)
    (h : MemoryCovered mem aw) : MemoryCovered mem (M aw off len) := by
  have hm := memoryWords_ge aw off len
  unfold MemoryCovered at *
  omega

theorem MemoryCovered.write {mem : ByteArray} {aw : UInt256} (src : ByteArray)
    (start : Nat) (off len : UInt256) (h : MemoryCovered mem aw) :
    MemoryCovered (src.write start mem off.toNat len.toNat) (M aw off len) := by
  by_cases hz : len.toNat = 0
  · simpa only [hz, ByteArray.write] using h.expand off len
  · have hs := byteArray_write_size_le src mem start off.toNat len.toNat
    have hm := memoryWords_ge aw off len
    have hc := memoryWords_covers aw off len hz
    unfold MemoryCovered at *
    omega

theorem MemoryCovered.write32 {mem : ByteArray} {aw : UInt256} (src : ByteArray)
    (start : Nat) (off : UInt256) (h : MemoryCovered mem aw) :
    MemoryCovered (src.write start mem off.toNat 32) (M aw off ⟨32⟩) :=
  h.write src start off ⟨32⟩

theorem copyMemoryWords_toNat (aw dst src len : UInt256) :
    (Mmcopy aw dst src len).toNat =
      MachineState.M aw.toNat (max dst.toNat src.toNat) len.toNat :=
  UInt256.toNat_ofNat_of_lt (MachineState.M_lt_uint256_size aw.val.isLt
    (max_lt dst.val.isLt src.val.isLt) len.val.isLt)

theorem MemoryCovered.copyExpand {mem : ByteArray} {aw : UInt256} (dst src len : UInt256)
    (h : MemoryCovered mem aw) : MemoryCovered mem (Mmcopy aw dst src len) := by
  have hm := MachineState.M_ge_active aw.toNat (max dst.toNat src.toNat) len.toNat
  unfold MemoryCovered at *
  rw [copyMemoryWords_toNat]
  omega

theorem MemoryCovered.copy {mem : ByteArray} {aw : UInt256} (bytes : ByteArray)
    (start : Nat) (dst src len : UInt256) (h : MemoryCovered mem aw) :
    MemoryCovered (bytes.write start mem dst.toNat len.toNat) (Mmcopy aw dst src len) := by
  by_cases hz : len.toNat = 0
  · simpa only [hz, ByteArray.write] using h.copyExpand dst src len
  · have hs := byteArray_write_size_le bytes mem start dst.toNat len.toNat
    have hm := MachineState.M_ge_active aw.toNat (max dst.toNat src.toNat) len.toNat
    unfold MemoryCovered at *
    rw [copyMemoryWords_toNat]
    unfold MachineState.M at *
    split <;> omega

structure MemoryAccounting (mem : ByteArray) (aw : UInt256) (spent : Nat) : Prop where
  paid : MemoryPaid 79 aw spent
  covered : MemoryCovered mem aw

theorem memoryAccountingAt {code I g s0 pc stk mem aw rdata σ k C}
    (_rd : RD fork code I g s0 pc stk mem aw rdata σ k C)
    (h : MemoryAccounting mem aw C) : MemoryAccounting mem aw C := h

theorem memoryAccounting_headroom {code I g s0 pc stk mem aw rdata σ k C}
    (rd : RD fork code I g s0 pc stk mem aw rdata σ k C) (ha : MemoryAccounting mem aw C)
    (hgas : midnightGasBound g.toUInt256) :
    X fork (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨ mem.size + 2^62 < 2^64 := by
  rcases midnightMemoryPaid_bound rd ha.paid hgas with hoog | hb
  · exact Or.inl hoog
  · have hs := ha.covered
    unfold MemoryCovered at hs
    exact Or.inr (by omega)

syntax "memory_covered" : tactic
macro_rules
| `(tactic| memory_covered) => `(tactic|
  first
  | with_reducible assumption
  | with_reducible apply MemoryCovered.write32; memory_covered
  | with_reducible apply MemoryCovered.write; memory_covered
  | with_reducible apply MemoryCovered.copy; memory_covered
  | with_reducible apply MemoryCovered.copyExpand; memory_covered
  | with_reducible apply MemoryCovered.expand; memory_covered)

macro "memory_account" h:ident : tactic => `(tactic|
  (constructor
   · have hp := MemoryAccounting.paid $h
     simp only [MemoryPaid, memExpansionCost, mcopyExpansionCost] at hp ⊢
     omega
   · have hc := MemoryAccounting.covered $h
     memory_covered))

end Benchmarks.Midnight
