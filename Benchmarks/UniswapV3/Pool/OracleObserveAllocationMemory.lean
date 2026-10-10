import Benchmarks.UniswapV3.Pool.ArrayReserve
import Benchmarks.UniswapV3.Pool.OracleObservePartialArrays

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def oracleObserveOutputMem (src mem : ByteArray) (p : UInt256) (n : Nat) : ByteArray :=
  arrayReserveMem src (arrayReserveMem src mem p n) (wordArrayElement p n) n

def oracleObserveOutputAw (aw p : UInt256) (n : Nat) : UInt256 :=
  arrayReserveAw (arrayReserveAw aw p n) (wordArrayElement p n) n

def oracleObserveOutputFree (p : UInt256) (n : Nat) : UInt256 :=
  wordArrayElement (wordArrayElement p n) n

theorem oracleObserveAllocationMemory {mem : ByteArray} {aw p agoPtr : UInt256}
    (src : ByteArray) (rawAgos : List UInt256) (hm : MemoryCursor mem aw p)
    (ha : DynamicWordArrayMemory mem agoPtr rawAgos) (halo : 96 ≤ agoPtr.toNat)
    (haend : agoPtr.toNat + 32 * (rawAgos.length + 1) ≤ p.toNat)
    (hb : p.toNat + 64 * (rawAgos.length + 1) ≤ 2 ^ 200) :
    let n := rawAgos.length
    let mem' := oracleObserveOutputMem src mem p n
    let aw' := oracleObserveOutputAw aw p n
    let free := oracleObserveOutputFree p n
    MemoryCursor mem' aw' free ∧ OracleObserveLayout free agoPtr p (wordArrayElement p n) n ∧
      OracleObservePartialArrays mem' agoPtr p (wordArrayElement p n) rawAgos
        (List.replicate n 0) (List.replicate n 0) 0 ∧
      MemoryPrefix mem mem' p.toNat ∧ free.toNat ≤ aw'.toNat * 32 + 32 := by
  dsimp only
  have h1 := wordArrayElement_toNat p rawAgos.length (by change _ < 2 ^ 256; omega)
  have h2 := wordArrayElement_toNat (wordArrayElement p rawAgos.length) rawAgos.length
    (by rw [h1]; change _ < 2 ^ 256; omega)
  have hbound1 : p.toNat + 32 * (rawAgos.length + 1) ≤ 2 ^ 200 := by omega
  have hbound2 : (wordArrayElement p rawAgos.length).toNat + 32 * (rawAgos.length + 1) ≤ 2 ^ 200 := by
    rw [h1]; omega
  obtain ⟨ha1, _⟩ := arrayReserveAw_properties hm.active hbound1
  obtain ⟨hm1, ht1, hp1⟩ := arrayReserveMemory src rawAgos.length hm hbound1 ha1
  obtain ⟨ha2, hc2⟩ := arrayReserveAw_properties ha1 hbound2
  obtain ⟨hm2, hs2, hp2⟩ := arrayReserveMemory src rawAgos.length hm1 hbound2 ha2
  have hp := hp1.trans (hp2.mono (by rw [h1]; omega))
  have ht2 := MemoryPrefix.wordArray hp2 ht1 (by have h := hm.lower; omega)
    (by rw [h1]; simp)
  refine ⟨hm2, ⟨halo, haend, by rw [h1], by exact Nat.le_of_eq h2.symm⟩,
    ⟨MemoryPrefix.wordArray hp ha halo haend, ?_, ?_, by simp, by simp, ?_, ?_⟩, hp, hc2⟩
  · simpa only [PartialWordArrayMemory, List.length_map, List.length_replicate, List.take_zero] using ht2
  · simpa only [PartialWordArrayMemory, List.length_map, List.length_replicate, List.take_zero] using hs2
  · intro t ht
    have he : t = 0 := (List.mem_replicate.mp ht).2
    subst t
    decide
  · intro s hs
    have he : s = 0 := (List.mem_replicate.mp hs).2
    subst s
    decide

end Benchmarks.UniswapV3.Pool
