import Benchmarks.EAS.Attester.Memory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: bounded pointer graphs for arrays of two-word structs.
structure PairArrayAt (mem : ByteArray) (lo hi base n : Nat)
    (values : Nat → UInt256 × UInt256) : Prop where
  lower : lo ≤ base
  upper : base + 32 + 32 * n ≤ hi
  length : memLoad (UInt256.ofNat base) mem = UInt256.ofNat n
  cells : ∀ j < n, ∃ ptr, lo ≤ ptr ∧ ptr + 64 ≤ hi ∧
    memLoad (UInt256.ofNat (base + 32 + 32 * j)) mem = UInt256.ofNat ptr ∧
    memLoad (UInt256.ofNat ptr) mem = (values j).1 ∧
    memLoad (UInt256.ofNat (ptr + 32)) mem = (values j).2

theorem PairArrayAt.congr {mem mem' : ByteArray} {lo hi base n values}
    (h : PairArrayAt mem lo hi base n values)
    (heq : ∀ off, lo ≤ off → off + 32 ≤ hi →
      memLoad (UInt256.ofNat off) mem' = memLoad (UInt256.ofNat off) mem) :
    PairArrayAt mem' lo hi base n values := by
  refine ⟨h.lower, h.upper, ?_, ?_⟩
  · rw [heq _ h.lower (by have := h.upper; omega)]; exact h.length
  · intro j hj
    obtain ⟨ptr, hlo, hhi, hslot, hfirst, hsecond⟩ := h.cells j hj
    refine ⟨ptr, hlo, hhi, ?_, ?_, ?_⟩
    · rw [heq _ (by have := h.lower; omega) (by have := h.upper; omega)]; exact hslot
    · rw [heq _ hlo (by omega)]; exact hfirst
    · rw [heq _ (by omega) (by omega)]; exact hsecond

theorem PairArrayAt.mono {mem : ByteArray} {lo hi lo' hi' base n values}
    (h : PairArrayAt mem lo hi base n values) (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    PairArrayAt mem lo' hi' base n values := by
  refine ⟨by have := h.lower; omega, by have := h.upper; omega, h.length, ?_⟩
  intro j hj
  obtain ⟨ptr, hlo, hhi, hslot, hfirst, hsecond⟩ := h.cells j hj
  exact ⟨ptr, by omega, by omega, hslot, hfirst, hsecond⟩

-- LIBRARY CANDIDATE: a word and a pointer to an array of pairs.
structure PairRequestAt (mem : ByteArray) (lo hi ptr : Nat) (schema : UInt256)
    (n : Nat) (values : Nat → UInt256 × UInt256) : Prop where
  lower : lo ≤ ptr
  upper : ptr + 64 ≤ hi
  first : memLoad (UInt256.ofNat ptr) mem = schema
  data : ∃ base, memLoad (UInt256.ofNat (ptr + 32)) mem = UInt256.ofNat base ∧
    PairArrayAt mem lo hi base n values

theorem PairRequestAt.congr {mem mem' : ByteArray} {lo hi ptr schema n values}
    (h : PairRequestAt mem lo hi ptr schema n values)
    (heq : ∀ off, lo ≤ off → off + 32 ≤ hi →
      memLoad (UInt256.ofNat off) mem' = memLoad (UInt256.ofNat off) mem) :
    PairRequestAt mem' lo hi ptr schema n values := by
  refine ⟨h.lower, h.upper, ?_, ?_⟩
  · rw [heq _ h.lower (by have := h.upper; omega)]; exact h.first
  · obtain ⟨base, hb, ha⟩ := h.data
    refine ⟨base, ?_, ha.congr heq⟩
    rw [heq _ (by have := h.lower; omega) (by have := h.upper; omega)]; exact hb

theorem PairRequestAt.mono {mem : ByteArray} {lo hi lo' hi' ptr schema n values}
    (h : PairRequestAt mem lo hi ptr schema n values) (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    PairRequestAt mem lo' hi' ptr schema n values := by
  obtain ⟨base, hb, ha⟩ := h.data
  exact ⟨by have := h.lower; omega, by have := h.upper; omega, h.first,
    base, hb, ha.mono hl hh⟩

-- LIBRARY CANDIDATE: a pointer array of requests with nested pair arrays.
structure PairRequestsAt (mem : ByteArray) (lo hi base n : Nat) (schemas : Nat → UInt256)
    (counts : Nat → Nat) (values : Nat → Nat → UInt256 × UInt256) : Prop where
  lower : lo ≤ base
  upper : base + 32 + 32 * n ≤ hi
  length : memLoad (UInt256.ofNat base) mem = UInt256.ofNat n
  cells : ∀ j < n, ∃ ptr,
    memLoad (UInt256.ofNat (base + 32 + 32 * j)) mem = UInt256.ofNat ptr ∧
    PairRequestAt mem lo hi ptr (schemas j) (counts j) (values j)

theorem PairRequestsAt.congr {mem mem' : ByteArray} {lo hi base n schemas counts values}
    (h : PairRequestsAt mem lo hi base n schemas counts values)
    (heq : ∀ off, lo ≤ off → off + 32 ≤ hi →
      memLoad (UInt256.ofNat off) mem' = memLoad (UInt256.ofNat off) mem) :
    PairRequestsAt mem' lo hi base n schemas counts values := by
  refine ⟨h.lower, h.upper, ?_, ?_⟩
  · rw [heq _ h.lower (by have := h.upper; omega)]; exact h.length
  · intro j hj
    obtain ⟨ptr, hp, hr⟩ := h.cells j hj
    refine ⟨ptr, ?_, hr.congr heq⟩
    rw [heq _ (by have := h.lower; omega) (by have := h.upper; omega)]; exact hp

end Reasoning.Theory
