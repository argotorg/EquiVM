import Benchmarks.Morpho.MorphoBlue.MarketParamsMemory
import Benchmarks.Morpho.MorphoBlue.MarketParamsDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

structure CreateMarketHeap (p : MarketParamsWords) (free : Nat) (mem : ByteArray) : Prop where
  size : mem.size = free
  freePtr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free
  params : p.InMemory (UInt256.ofNat 128) mem

def createMarketDecodedMem (p : MarketParamsWords) : ByteArray :=
  marketParamsMem p (UInt256.ofNat 128) (marketParamsAllocatedMem solcFreePtrMem)

theorem createMarketDecodedHeap (p : MarketParamsWords) :
    CreateMarketHeap p 288 (createMarketDecodedMem p) := by
  have hs : (marketParamsAllocatedMem solcFreePtrMem).size = 96 := by native_decide
  have hg : (UInt256.ofNat 128).toNat + 160 -
      (marketParamsAllocatedMem solcFreePtrMem).size < USize.size := by
    rw [hs]; exact lt_usize _ (by decide)
  constructor
  · rw [createMarketDecodedMem, marketParamsMem_size p _ _ (by decide) hg, hs]
    rfl
  · have hr := writeCascade_read_preserved
      (marketParamsAllocatedMem solcFreePtrMem) (returnWordWrites 128 p.toList) 64
    apply mloadWordValue_of_readWithPadding
    · rw [createMarketDecodedMem, marketParamsMem_size p _ _ (by decide) hg, hs]
      decide
    · rw [createMarketDecodedMem, marketParamsMem_asWordWrites p _ _ (by decide)]
      change (writeCascade (marketParamsAllocatedMem solcFreePtrMem)
        (returnWordWrites 128 p.toList)).readWithPadding 64 32 = _
      rw [hr]
      · native_decide
      · simp only [MarketParamsWords.toList, returnWordWrites, WindowDisjointFromWrites, hs]
        have huz : 32 < USize.size := lt_usize _ (by decide)
        norm_num
        omega
  · exact marketParamsMem_inMemory p _ _ (by decide) hg

theorem CreateMarketHeap.hash {p : MarketParamsWords} {free : Nat} {mem : ByteArray}
    (h : CreateMarketHeap p free mem) (hlo : 288 ≤ free) (key slot : UInt256) :
    CreateMarketHeap p free (twoWordHashMem key slot mem) := by
  constructor
  · rw [twoWordHashMem_size_of_ge_64' _ _ (by rw [h.size]; omega), h.size]
  · rw [twoWordHashMem_memLoad_above64 _ _ _ (by decide)
      (by rw [h.size]; change 96 ≤ free; omega), h.freePtr]
  · exact h.params.twoWordHashMem key slot (by decide) (by rw [h.size]; exact hlo) (by decide)

theorem CreateMarketHeap.message {p : MarketParamsWords} {free : Nat} {mem : ByteArray}
    (h : CreateMarketHeap p free mem) (hlo : 288 ≤ free) (hhi : free + 100 < 2 ^ 64)
    (length payload : UInt256) :
    CreateMarketHeap p (free + 64) (morphoErrorMem length payload mem) ∧
      morphoErrorLength (morphoErrorMem length payload mem) (UInt256.ofNat free) = length := by
  have hf : free < UInt256.size := by change free < 2 ^ 256; omega
  have hfn := UInt256.toNat_ofNat_of_lt hf
  have hp := morphoErrorMem_properties length payload (UInt256.ofNat free) mem
    (by rw [h.size, hfn]) h.freePtr (by rw [hfn]; omega)
    (by rw [hfn]; change free + 100 < 2 ^ 256; omega)
  have ha : UInt256.ofNat free + UInt256.ofNat 64 = UInt256.ofNat (free + 64) := by
    apply u256_inj
    rw [uadd_word_ofNat_toNat _ 64 (by rw [hfn]; change free + 64 < 2 ^ 256; omega), hfn,
      UInt256.toNat_ofNat_of_lt (by change free + 64 < 2 ^ 256; omega)]
  refine ⟨⟨by simpa only [hfn] using hp.1, by simpa only [ha] using hp.2.1, ?_⟩, hp.2.2⟩
  rw [morphoErrorMem_asCascade _ _ _ _ h.freePtr]
  let m1 := writeWord mem 64 (UInt256.ofNat free + UInt256.ofNat 64)
  let m2 := writeWord m1 free length
  have huz : 0 < USize.size := lt_usize _ (by decide)
  have hs1 : m1.size = free := by
    rw [writeWord_size _ _ _ (by rw [h.size]; omega), h.size]; omega
  have hs2 : m2.size = free + 32 := by
    rw [writeWord_size _ _ _ (by rw [hs1]; omega), hs1]; omega
  have hm1 := h.params.writeWord 64 (UInt256.ofNat free + UInt256.ofNat 64)
    (by decide) (by rw [h.size]; exact hlo) (by rw [h.size]; omega) (by right; decide)
  have hm2 := hm1.writeWord free length (by decide) (by change 288 ≤ m1.size; omega)
    (by change free - m1.size < USize.size; omega) (by left; exact hlo)
  have hm3 := hm2.writeWord (free + 32) payload (by decide) (by change 288 ≤ m2.size; omega)
    (by change free + 32 - m2.size < USize.size; omega) (by left; change 288 ≤ free + 32; omega)
  simpa only [writeCascade, hfn,
    uadd_word_ofNat_toNat _ 32 (by rw [hfn]; change free + 32 < 2 ^ 256; omega)] using hm3

end Benchmarks.Morpho.MorphoBlue
