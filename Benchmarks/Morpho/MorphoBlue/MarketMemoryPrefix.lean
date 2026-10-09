import Benchmarks.Morpho.MorphoBlue.ReturnDataMemory
import Benchmarks.Morpho.MorphoBlue.MarketParamsMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue

-- LIBRARY CANDIDATE: a fixed-width tuple survives preservation of its allocated word window.
theorem MarketParamsWords.InMemory.ofPrefix {p : MarketParamsWords} {ptr : UInt256}
    {before after : ByteArray} {limit : Nat} (h : p.InMemory ptr before)
    (hp : MemoryPrefix before after limit) (hlo : 96 ≤ ptr.toNat)
    (hfit : ptr.toNat + 160 < UInt256.size) (hin : ptr.toNat + 160 ≤ before.size)
    (hlim : ptr.toNat + 160 ≤ limit) : p.InMemory ptr after := by
  intro i
  have hi := i.isLt
  have hadd := uadd_word_ofNat_toNat ptr (32 * i.val) (by omega)
  rw [memoryPrefix_memLoad hp _ (by omega) (by omega) (by omega)]
  exact h i

end Benchmarks.Morpho.MorphoBlue
