import Benchmarks.EAS.Attester.PairHeap

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

def AttestCellAt (mem : ByteArray) (lo hi ptr : Nat) (input : UInt256) : Prop :=
  lo ≤ ptr ∧ ptr + 192 ≤ hi ∧ ∃ data, lo ≤ data ∧ data + 64 ≤ hi ∧
    memLoad (UInt256.ofNat ptr) mem = ⟨0⟩ ∧
    memLoad (UInt256.ofNat (ptr + 32)) mem = ⟨0⟩ ∧
    memLoad (UInt256.ofNat (ptr + 64)) mem = ⟨1⟩ ∧
    memLoad (UInt256.ofNat (ptr + 96)) mem = ⟨0⟩ ∧
    memLoad (UInt256.ofNat (ptr + 128)) mem = UInt256.ofNat data ∧
    memLoad (UInt256.ofNat (ptr + 160)) mem = ⟨0⟩ ∧
    memLoad (UInt256.ofNat data) mem = ⟨32⟩ ∧
    memLoad (UInt256.ofNat (data + 32)) mem = input

theorem AttestCellAt.congr {mem mem' : ByteArray} {lo hi ptr input}
    (h : AttestCellAt mem lo hi ptr input)
    (heq : ∀ off, lo ≤ off → off + 32 ≤ hi →
      memLoad (UInt256.ofNat off) mem' = memLoad (UInt256.ofNat off) mem) :
    AttestCellAt mem' lo hi ptr input := by
  obtain ⟨hlo, hhi, data, hdlo, hdhi, hf⟩ := h
  refine ⟨hlo, hhi, data, hdlo, hdhi, ?_⟩
  simpa (disch := omega) only [heq] using hf

theorem AttestCellAt.mono {mem : ByteArray} {lo hi lo' hi' ptr input}
    (h : AttestCellAt mem lo hi ptr input) (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    AttestCellAt mem lo' hi' ptr input := by
  obtain ⟨hlo, hhi, data, hdlo, hdhi, hf⟩ := h
  exact ⟨by omega, by omega, data, by omega, by omega, hf⟩

structure AttestArrayAt (mem : ByteArray) (lo hi base n : Nat) (values : Nat → UInt256) : Prop where
  lower : lo ≤ base
  upper : base + 32 + 32 * n ≤ hi
  length : memLoad (UInt256.ofNat base) mem = UInt256.ofNat n
  cells : ∀ j < n, ∃ ptr,
    memLoad (UInt256.ofNat (base + 32 + 32 * j)) mem = UInt256.ofNat ptr ∧
    AttestCellAt mem lo hi ptr (values j)

theorem AttestArrayAt.congr {mem mem' : ByteArray} {lo hi base n values}
    (h : AttestArrayAt mem lo hi base n values)
    (heq : ∀ off, lo ≤ off → off + 32 ≤ hi →
      memLoad (UInt256.ofNat off) mem' = memLoad (UInt256.ofNat off) mem) :
    AttestArrayAt mem' lo hi base n values := by
  refine ⟨h.lower, h.upper, ?_, ?_⟩
  · rw [heq _ h.lower (by have := h.upper; omega)]; exact h.length
  · intro j hj
    obtain ⟨ptr, hp, hc⟩ := h.cells j hj
    refine ⟨ptr, ?_, hc.congr heq⟩
    rw [heq _ (by have := h.lower; omega) (by have := h.upper; omega)]; exact hp

theorem AttestArrayAt.mono {mem : ByteArray} {lo hi lo' hi' base n values}
    (h : AttestArrayAt mem lo hi base n values) (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    AttestArrayAt mem lo' hi' base n values := by
  refine ⟨by have := h.lower; omega, by have := h.upper; omega, h.length, ?_⟩
  intro j hj
  obtain ⟨ptr, hp, hc⟩ := h.cells j hj
  exact ⟨ptr, hp, hc.mono hl hh⟩

structure AttestRequestAt (mem : ByteArray) (lo hi ptr : Nat) (schema : UInt256)
    (n : Nat) (values : Nat → UInt256) : Prop where
  lower : lo ≤ ptr
  upper : ptr + 64 ≤ hi
  first : memLoad (UInt256.ofNat ptr) mem = schema
  data : ∃ base, memLoad (UInt256.ofNat (ptr + 32)) mem = UInt256.ofNat base ∧
    AttestArrayAt mem lo hi base n values

theorem AttestRequestAt.congr {mem mem' : ByteArray} {lo hi ptr schema n values}
    (h : AttestRequestAt mem lo hi ptr schema n values)
    (heq : ∀ off, lo ≤ off → off + 32 ≤ hi →
      memLoad (UInt256.ofNat off) mem' = memLoad (UInt256.ofNat off) mem) :
    AttestRequestAt mem' lo hi ptr schema n values := by
  refine ⟨h.lower, h.upper, ?_, ?_⟩
  · rw [heq _ h.lower (by have := h.upper; omega)]; exact h.first
  · obtain ⟨base, hb, ha⟩ := h.data
    refine ⟨base, ?_, ha.congr heq⟩
    rw [heq _ (by have := h.lower; omega) (by have := h.upper; omega)]; exact hb

theorem AttestRequestAt.mono {mem : ByteArray} {lo hi lo' hi' ptr schema n values}
    (h : AttestRequestAt mem lo hi ptr schema n values) (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    AttestRequestAt mem lo' hi' ptr schema n values := by
  obtain ⟨base, hb, ha⟩ := h.data
  exact ⟨by have := h.lower; omega, by have := h.upper; omega, h.first,
    base, hb, ha.mono hl hh⟩

structure AttestRequestsAt (mem : ByteArray) (lo hi base n : Nat) (schemas : Nat → UInt256)
    (counts : Nat → Nat) (values : Nat → Nat → UInt256) : Prop where
  lower : lo ≤ base
  upper : base + 32 + 32 * n ≤ hi
  length : memLoad (UInt256.ofNat base) mem = UInt256.ofNat n
  cells : ∀ j < n, ∃ ptr,
    memLoad (UInt256.ofNat (base + 32 + 32 * j)) mem = UInt256.ofNat ptr ∧
    AttestRequestAt mem lo hi ptr (schemas j) (counts j) (values j)

theorem AttestRequestsAt.congr {mem mem' : ByteArray} {lo hi base n schemas counts values}
    (h : AttestRequestsAt mem lo hi base n schemas counts values)
    (heq : ∀ off, lo ≤ off → off + 32 ≤ hi →
      memLoad (UInt256.ofNat off) mem' = memLoad (UInt256.ofNat off) mem) :
    AttestRequestsAt mem' lo hi base n schemas counts values := by
  refine ⟨h.lower, h.upper, ?_, ?_⟩
  · rw [heq _ h.lower (by have := h.upper; omega)]; exact h.length
  · intro j hj
    obtain ⟨ptr, hp, hr⟩ := h.cells j hj
    refine ⟨ptr, ?_, hr.congr heq⟩
    rw [heq _ (by have := h.lower; omega) (by have := h.upper; omega)]; exact hp

end Benchmarks.EAS.Attester
