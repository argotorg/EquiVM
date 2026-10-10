import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsCalldataDecoder

/-! Heap invariants of the allocated calldata market-parameter struct. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

theorem marketParamsCalldataMemory_free (mem : ByteArray) (ptr : UInt256) (cd : ByteArray)
    (hlo : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (marketParamsCalldataMemory mem ptr cd) = nextCursor ptr ⟨160⟩ := by
  rw [marketParamsCalldataMemory, marketParamsCopyMem_free
    (by rw [writeWord_sparse_size]; omega) hlo]
  exact memLoad_write_same _ _ _ _ rfl

theorem marketParamsCalldataMemory_size (mem : ByteArray) (ptr : UInt256) (cd : ByteArray) :
    ptr.toNat + 160 ≤ (marketParamsCalldataMemory mem ptr cd).size := by
  rw [marketParamsCalldataMemory, marketParamsCopyMem_size]
  exact Nat.le_max_right _ _

theorem marketParamsCalldataMemory_loads (mem : ByteArray) (ptr : UInt256) (cd : ByteArray)
    (hc : MarketParamsCalldataChecks cd) (hfit : ptr.toNat + 160 < UInt256.size) :
    MarketParamsLoads (marketParamsCalldataMemory mem ptr cd) ptr
      (marketParamsData (marketParamsArgs cd)) := by
  apply marketParamsLoads_of_fields hc.2
  intro i hi
  have hadd : ptr + UInt256.ofNat (32 * i) = UInt256.ofNat (ptr.toNat + 32 * i) := by
    apply u256_inj
    rw [uadd_word_ofNat_toNat ptr (32 * i) (by omega),
      UInt256.toNat_ofNat_of_lt (by omega)]
  rw [hadd]
  exact marketParamsCopyMem_field _ _ _ i hi hfit

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
