import Benchmarks.CompoundIII.Comet.PriceMemory
import Benchmarks.CompoundIII.Comet.AssetMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem priceReturnMemory_prefix {mem out : ByteArray} {free : UInt256}
    (hout : 160 ≤ out.size) (hhi : out.size < UInt256.size) :
    MemoryPrefix mem (priceReturnMemory mem free out) free.toNat := by
  have hi := memoryPrefix_sparse_writeWord mem free.toNat free.toNat priceSelectorWord
    (Or.inl (le_refl _))
  have hc : MemoryPrefix (priceInputMemory mem free) (priceCopyMemory mem free out)
      free.toNat := by
    have hl : (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 160 :=
      umin_ofNat_right_toNat_of_ge (c := 160) (n := out.size) (by decide) hout hhi
    unfold priceCopyMemory callOutputMem
    rw [hl]
    exact copyWindow_prefix out _ 0 free.toNat 160 free.toNat (by decide) hout
      (by rw [priceInputMemory, writeWord_sparse_size]; omega) (Or.inl (le_refl _))
  exact (hi.trans hc).trans
    (memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide)))

theorem AssetMemory.afterPrice {mem assetOut priceOut : ByteArray} {ptr free : UInt256}
    (hm : AssetMemory mem ptr free assetOut) (hgap : free.toNat ≤ mem.size + 32)
    (hb : free.toNat + 416 < UInt256.size) (hout : 160 ≤ priceOut.size)
    (hhi : priceOut.size < UInt256.size) :
    AssetMemory (priceReturnMemory mem free priceOut) ptr (free + ⟨160⟩) assetOut := by
  have hlo : 96 ≤ free.toNat := le_trans hm.lower (by have hs := hm.separate; omega)
  have hfree : (free + (⟨160⟩ : UInt256)).toNat = free.toNat + 160 :=
    uadd_word_ofNat_toNat free 160 (by omega)
  have hs := priceReturnMemory_size hlo hgap hout hhi
  refine ⟨hm.lower, by rw [hs]; have hp := hm.present; omega,
    by rw [hfree]; have hp := hm.separate; omega, by rw [hfree]; omega,
    priceReturnMemory_free hlo hgap hout hhi, ?_⟩
  intro j hj
  have haddr : (ptr + UInt256.ofNat (32 * j)).toNat = ptr.toNat + 32 * j :=
    uadd_word_ofNat_toNat _ _ (by have hp := hm.separate; omega)
  rw [memoryPrefix_load (priceReturnMemory_prefix hout hhi)
    (by rw [haddr]; exact le_trans hm.lower (by omega))
    (by rw [haddr]; have hp := hm.separate; omega)
    (by rw [haddr]; have hp := hm.present; omega)]
  exact hm.words j hj

end Benchmarks.CompoundIII.Comet
