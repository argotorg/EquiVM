import Benchmarks.UniswapV3.Pool.WordArrayPrefix
import Benchmarks.UniswapV3.Pool.OracleObserveArrays

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

structure OracleObservePartialArrays (mem : ByteArray) (agoPtr ticksPtr secondsPtr : UInt256)
    (rawAgos : List UInt256) (ticks seconds : List Int) (i : Nat) : Prop where
  agos_mem : DynamicWordArrayMemory mem agoPtr rawAgos
  ticks_mem : PartialWordArrayMemory mem ticksPtr (ticks.map EVM.wordOfInt) i
  seconds_mem : PartialWordArrayMemory mem secondsPtr (seconds.map EVM.wordOfInt) i
  ticks_length : ticks.length = rawAgos.length
  seconds_length : seconds.length = rawAgos.length
  ticks_range : ∀ t ∈ ticks, -(2 ^ 55 : Int) ≤ t ∧ t < 2 ^ 55
  seconds_range : ∀ s ∈ seconds, 0 ≤ s ∧ s < 2 ^ 160

theorem OracleObserveArrays.partial {mem : ByteArray} {a t s : UInt256}
    {rawAgos : List UInt256} {ticks seconds : List Int}
    (h : OracleObserveArrays mem a t s rawAgos ticks seconds) (i : Nat) :
    OracleObservePartialArrays mem a t s rawAgos ticks seconds i :=
  ⟨h.agos_mem, h.ticks_mem.partial i, h.seconds_mem.partial i,
    h.ticks_length, h.seconds_length, h.ticks_range, h.seconds_range⟩

theorem OracleObservePartialArrays.complete {mem : ByteArray} {a t s : UInt256}
    {rawAgos : List UInt256} {ticks seconds : List Int} {i : Nat}
    (h : OracleObservePartialArrays mem a t s rawAgos ticks seconds i) (hi : rawAgos.length ≤ i) :
    OracleObserveArrays mem a t s rawAgos ticks seconds :=
  ⟨h.agos_mem, h.ticks_mem.complete (by simpa only [List.length_map, h.ticks_length] using hi),
    h.seconds_mem.complete (by simpa only [List.length_map, h.seconds_length] using hi),
    h.ticks_length, h.seconds_length, h.ticks_range, h.seconds_range⟩

theorem OracleObservePartialArrays.prefix {mem mem' : ByteArray} {free a t s : UInt256}
    {rawAgos : List UInt256} {ticks seconds : List Int} {i : Nat}
    (h : OracleObservePartialArrays mem a t s rawAgos ticks seconds i)
    (hl : OracleObserveLayout free a t s rawAgos.length) (hp : MemoryPrefix mem mem' free.toNat) :
    OracleObservePartialArrays mem' a t s rawAgos ticks seconds i := by
  rcases hl with ⟨hal, hae, hte, hse⟩
  refine ⟨MemoryPrefix.wordArray hp h.agos_mem hal ?_,
    MemoryPrefix.wordArray hp h.ticks_mem (by omega) ?_,
    MemoryPrefix.wordArray hp h.seconds_mem (by omega) ?_,
    h.ticks_length, h.seconds_length, h.ticks_range, h.seconds_range⟩
  · simp only [dynamicWordArrayWords, List.length_cons]; omega
  · simp only [List.length_cons, List.length_take, List.length_map, h.ticks_length]; omega
  · simp only [List.length_cons, List.length_take, List.length_map, h.seconds_length]; omega

theorem OracleObservePartialArrays.update {mem : ByteArray} {free a t s : UInt256}
    {rawAgos : List UInt256} {ticks seconds : List Int} {i : Nat} {tv sv : Int}
    (h : OracleObservePartialArrays mem a t s rawAgos ticks seconds i)
    (hl : OracleObserveLayout free a t s rawAgos.length) (hi : i < rawAgos.length)
    (htv : -(2 ^ 55 : Int) ≤ tv ∧ tv < 2 ^ 55) (hsv : 0 ≤ sv ∧ sv < 2 ^ 160) :
    OracleObservePartialArrays (oracleObserveUpdateMem mem t s i tv sv) a t s rawAgos
      (ticks.set i tv) (seconds.set i sv) (i + 1) := by
  rcases hl with ⟨hal, hae, hte, hse⟩
  have htl := h.ticks_length
  have hsl := h.seconds_length
  have ha1 := h.agos_mem.write_disjoint (s.toNat + 32 * (i + 1)) (EVM.wordOfInt sv)
    (Or.inr (by simp only [dynamicWordArrayWords, List.length_cons]; omega))
  have ha2 := ha1.write_disjoint (t.toNat + 32 * (i + 1)) (EVM.wordOfInt tv)
    (Or.inr (by simp only [dynamicWordArrayWords, List.length_cons]; omega))
  have ht1 := h.ticks_mem.write_disjoint (s.toNat + 32 * (i + 1)) (EVM.wordOfInt sv)
    (Or.inr (by simp only [List.length_cons, List.length_take, List.length_map]; omega))
  have ht2 := PartialWordArrayMemory.push ht1 (EVM.wordOfInt tv)
    (by simpa only [List.length_map, htl] using hi)
  have hs1 := PartialWordArrayMemory.push h.seconds_mem (EVM.wordOfInt sv)
    (by simpa only [List.length_map, hsl] using hi)
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

theorem oracleObserveUpdateCursor {mem : ByteArray} {free aw a t s : UInt256} {n : Nat}
    (i : Nat) (tv sv : Int) (hm : MemoryCursor mem aw free)
    (hl : OracleObserveLayout free a t s n) :
    MemoryCursor (oracleObserveUpdateMem mem t s i tv sv) aw free := by
  rcases hl with ⟨hal, hae, hte, hse⟩
  exact MemoryCursor.writeWord (MemoryCursor.writeWord hm _ _ (by omega)) _ _ (by omega)

end Benchmarks.UniswapV3.Pool
