import Benchmarks.UniswapV3.Pool.DynamicWordArray

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

structure OracleObserveLayout (free agoPtr ticksPtr secondsPtr : UInt256) (n : Nat) : Prop where
  ago_lower : 96 ≤ agoPtr.toNat
  ago_end : agoPtr.toNat + 32 * (n + 1) ≤ ticksPtr.toNat
  ticks_end : ticksPtr.toNat + 32 * (n + 1) ≤ secondsPtr.toNat
  seconds_end : secondsPtr.toNat + 32 * (n + 1) ≤ free.toNat

theorem OracleObserveLayout.mono {free free' a t s : UInt256} {n : Nat}
    (h : OracleObserveLayout free a t s n) (hm : free.toNat ≤ free'.toNat) :
    OracleObserveLayout free' a t s n :=
  ⟨h.ago_lower, h.ago_end, h.ticks_end, h.seconds_end.trans hm⟩

structure OracleObserveArrays (mem : ByteArray) (agoPtr ticksPtr secondsPtr : UInt256)
    (rawAgos : List UInt256) (ticks seconds : List Int) : Prop where
  agos_mem : DynamicWordArrayMemory mem agoPtr rawAgos
  ticks_mem : DynamicWordArrayMemory mem ticksPtr (ticks.map EVM.wordOfInt)
  seconds_mem : DynamicWordArrayMemory mem secondsPtr (seconds.map EVM.wordOfInt)
  ticks_length : ticks.length = rawAgos.length
  seconds_length : seconds.length = rawAgos.length
  ticks_range : ∀ t ∈ ticks, -(2 ^ 55 : Int) ≤ t ∧ t < 2 ^ 55
  seconds_range : ∀ s ∈ seconds, 0 ≤ s ∧ s < 2 ^ 160

theorem OracleObserveArrays.prefix {mem mem' : ByteArray} {free a t s : UInt256}
    {rawAgos : List UInt256} {ticks seconds : List Int}
    (h : OracleObserveArrays mem a t s rawAgos ticks seconds)
    (hl : OracleObserveLayout free a t s rawAgos.length)
    (hp : MemoryPrefix mem mem' free.toNat) :
    OracleObserveArrays mem' a t s rawAgos ticks seconds := by
  rcases hl with ⟨hal, hae, hte, hse⟩
  refine ⟨MemoryPrefix.wordArray hp h.agos_mem hal (by simpa [dynamicWordArrayWords] using (by omega :
    a.toNat + 32 * (rawAgos.length + 1) ≤ free.toNat)),
    MemoryPrefix.wordArray hp h.ticks_mem (by omega) ?_, MemoryPrefix.wordArray hp h.seconds_mem (by omega) ?_,
    h.ticks_length, h.seconds_length, h.ticks_range, h.seconds_range⟩
  · simpa only [dynamicWordArrayWords, List.length_cons, List.length_map, h.ticks_length] using
      (show t.toNat + 32 * (rawAgos.length + 1) ≤ free.toNat by omega)
  · simpa only [dynamicWordArrayWords, List.length_cons, List.length_map, h.seconds_length] using hse

def oracleObserveUpdateMem (mem : ByteArray) (ticksPtr secondsPtr : UInt256)
    (i : Nat) (tickValue secondsValue : Int) : ByteArray :=
  writeWord (writeWord mem (secondsPtr.toNat + 32 * (i + 1)) (EVM.wordOfInt secondsValue))
    (ticksPtr.toNat + 32 * (i + 1)) (EVM.wordOfInt tickValue)

theorem OracleObserveArrays.update {mem : ByteArray} {free a t s : UInt256}
    {rawAgos : List UInt256} {ticks seconds : List Int} {i : Nat} {tv sv : Int}
    (h : OracleObserveArrays mem a t s rawAgos ticks seconds)
    (hl : OracleObserveLayout free a t s rawAgos.length) (hi : i < rawAgos.length)
    (htv : -(2 ^ 55 : Int) ≤ tv ∧ tv < 2 ^ 55) (hsv : 0 ≤ sv ∧ sv < 2 ^ 160) :
    OracleObserveArrays (oracleObserveUpdateMem mem t s i tv sv) a t s rawAgos
      (ticks.set i tv) (seconds.set i sv) := by
  rcases hl with ⟨hal, hae, hte, hse⟩
  have htl := h.ticks_length
  have hsl := h.seconds_length
  have ha1 := h.agos_mem.write_disjoint (s.toNat + 32 * (i + 1)) (EVM.wordOfInt sv)
    (Or.inr (by simp only [dynamicWordArrayWords, List.length_cons]; omega))
  have ha2 := ha1.write_disjoint (t.toNat + 32 * (i + 1)) (EVM.wordOfInt tv)
    (Or.inr (by simp only [dynamicWordArrayWords, List.length_cons]; omega))
  have ht1 := h.ticks_mem.write_disjoint (s.toNat + 32 * (i + 1)) (EVM.wordOfInt sv)
    (Or.inr (by simp only [dynamicWordArrayWords, List.length_cons, List.length_map]; omega))
  have ht2 := DynamicWordArrayMemory.update ht1 i (EVM.wordOfInt tv)
  have hs1 := h.seconds_mem.update i (EVM.wordOfInt sv)
  have hs2 := hs1.write_disjoint (t.toNat + 32 * (i + 1)) (EVM.wordOfInt tv)
    (Or.inl (by omega))
  refine ⟨ha2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.map_set] using ht2
  · simpa only [List.map_set] using hs2
  · simpa only [List.length_set] using htl
  · simpa only [List.length_set] using hsl
  · intro x hx
    rcases List.mem_or_eq_of_mem_set hx with hm | rfl
    · exact h.ticks_range x hm
    · exact htv
  · intro x hx
    rcases List.mem_or_eq_of_mem_set hx with hm | rfl
    · exact h.seconds_range x hm
    · exact hsv

theorem oracleObserveUpdateHeap {mem : ByteArray} {free aw a t s : UInt256}
    {rawAgos : List UInt256} {ticks seconds : List Int} {i : Nat} (tv sv : Int)
    (hm : HeapMemory mem aw free) (ha : OracleObserveArrays mem a t s rawAgos ticks seconds)
    (hl : OracleObserveLayout free a t s rawAgos.length) (hi : i < rawAgos.length) :
    HeapMemory (oracleObserveUpdateMem mem t s i tv sv) aw free := by
  rcases hl with ⟨hal, hae, hte, hse⟩
  have hts := ha.ticks_mem.size
  have hss := ha.seconds_mem.size
  simp only [dynamicWordArrayWords, List.length_cons, List.length_map,
    ha.ticks_length, ha.seconds_length] at hts hss
  have hm1 := HeapMemory.writeWithin hm (s.toNat + 32 * (i + 1))
    (EVM.wordOfInt sv) (by omega) (by omega)
  exact HeapMemory.writeWithin hm1 _ _ (by omega)
    (by rw [writeWord_sparse_size]; omega)

theorem oracleObserveUpdatePrefix (mem : ByteArray) (t s : UInt256) (i : Nat) (tv sv : Int)
    (h : t.toNat ≤ s.toNat) : MemoryPrefix mem (oracleObserveUpdateMem mem t s i tv sv) t.toNat :=
  (memoryPrefix_sparse_writeWord mem _ t.toNat _ (Or.inl (by omega))).trans
    (memoryPrefix_sparse_writeWord _ _ t.toNat _ (Or.inl (by omega)))

end Benchmarks.UniswapV3.Pool
