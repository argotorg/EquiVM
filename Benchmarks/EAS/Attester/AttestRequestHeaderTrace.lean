import Benchmarks.EAS.Attester.AttestArrayEncodeTrace
import Benchmarks.EAS.Attester.AttestRequestsEncodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem attestRequestHeader3353 {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {x0 x2 x5 schema : UInt256} {limit slot ptr origin table dst n : Nat}
    {values : Nat → UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3353⟩
      ([x0, UInt256.ofNat slot, x2, UInt256.ofNat table, UInt256.ofNat dst, x5,
        UInt256.ofNat origin] ++ R) mem aw out σ k C)
    (hstack : R.length + 12 ≤ 1024) (hslotlo : 96 ≤ slot) (hslotend : slot + 32 ≤ limit)
    (hslot : memLoad (UInt256.ofNat slot) mem = UInt256.ofNat ptr)
    (request : AttestRequestAt mem 96 limit ptr schema n values)
    (hsize : limit ≤ mem.size) (ht : limit ≤ table) (hd : limit ≤ dst)
    (htable : table + 32 ≤ dst) (horigin : origin + 64 ≤ dst)
    (hfit : dst + 96 + 32 * n < UInt256.size) :
    ∃ base, AttestArrayAt mem 96 limit base n values ∧ ∃ aw' k' C',
      RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3441⟩
        ([UInt256.ofNat 0, UInt256.ofNat n, UInt256.ofNat (dst + 96),
          UInt256.ofNat (dst + 96 + 32 * n), UInt256.ofNat (base + 32),
          x0, UInt256.ofNat slot, x2, UInt256.ofNat table, UInt256.ofNat dst, x5,
          UInt256.ofNat origin] ++ R)
        (pairRequestHeaderMemory mem origin table dst schema n) aw' out σ k' C' := by
  obtain ⟨base, hbase, ha⟩ := request.data
  let delta := UInt256.ofNat (dst - origin - 64)
  let pre0 := writeWord mem table delta
  let pre1 := writeWord pre0 dst schema
  let pre2 := writeWord pre1 (dst + 32) (UInt256.ofNat 64)
  have hp0 : MemoryPrefix mem pre0 limit :=
    memoryPrefix_sparse_writeWord _ _ _ _ (.inl ht)
  have hp1 : MemoryPrefix mem pre1 limit := hp0.trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (.inl hd))
  have hp2 : MemoryPrefix mem pre2 limit := hp1.trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (by omega)))
  have hs0 : memLoad (UInt256.ofNat slot) pre0 = UInt256.ofNat ptr :=
    (hp0.load_preserved hslotlo hslotend (by omega) (by omega)).trans hslot
  have hf0 : memLoad (UInt256.ofNat ptr) pre0 = schema :=
    (hp0.load_preserved request.lower (by have := request.upper; omega)
      (by have := request.upper; omega) (by have := request.upper; omega)).trans request.first
  have hb1 : memLoad (UInt256.ofNat (ptr + 32)) pre1 = UInt256.ofNat base :=
    (hp1.load_preserved (by have := request.lower; omega) (by have := request.upper; omega)
      (by have := request.upper; omega) (by have := request.upper; omega)).trans hbase
  have hl2 : memLoad (UInt256.ofNat base) pre2 = UInt256.ofNat n :=
    (hp2.load_preserved ha.lower (by have := ha.upper; omega)
      (by have := ha.upper; omega) (by have := ha.upper; omega)).trans ha.length
  dsimp only [pre0, pre1, pre2, Reasoning.Theory.writeWord] at hs0 hf0 hb1 hl2
  have hdelta : UInt256.sub (UInt256.ofNat dst) (UInt256.ofNat origin) +
      UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872 =
      delta := by
    rw [u256_add_comm, ofNat_sub_words (by omega) (by omega)]
    exact ofNat_size_sub_add (c := 64) (n := dst - origin) (by decide) (by omega) (by omega)
  have hdt : table < UInt256.size := by omega
  have hdd : dst < UInt256.size := by omega
  have hdd32 : dst + 32 < UInt256.size := by omega
  have hdd64 : dst + 64 < UInt256.size := by omega
  have hm : attesterRuntime_block_3353_memory (mem := mem)
      (x1 := UInt256.ofNat slot) (x3 := UInt256.ofNat table)
      (x4 := UInt256.ofNat dst) (x6 := UInt256.ofNat origin) =
      pairRequestHeaderMemory mem origin table dst schema n := by
    simp only [attesterRuntime_block_3353_memory, hdelta, ofNat_add_words,
      ulit_toNat' _ hdt, ulit_toNat' _ hdd, ulit_toNat' _ hdd32, ulit_toNat' _ hdd64,
      hs0, hf0, show 32 + ptr = ptr + 32 by omega, hb1, hl2]
    rfl
  obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_3353_packed hstack h
  rw [hm] at h'
  have hshift : UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * n) := shiftLeft5_ofNat_eq (by omega)
  refine ⟨base, ha, aw', k', C', ?_⟩
  simpa only [attesterRuntime_block_3353_stack, hdelta, ofNat_add_words,
    ulit_toNat' _ hdt, ulit_toNat' _ hdd, ulit_toNat' _ hdd32,
    hs0, hf0, show 32 + ptr = ptr + 32 by omega, hb1, hl2,
    show 32 + base = base + 32 by omega, hshift,
    show 96 + (dst + 32 * n) = dst + 96 + 32 * n by omega] using h'

end Benchmarks.EAS.Attester
