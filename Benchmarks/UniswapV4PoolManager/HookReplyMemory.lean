import Benchmarks.UniswapV4PoolManager.ReturnDataMemory
import Benchmarks.UniswapV4PoolManager.SelectorMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem hookReplyMemory_selector {mem data out : ByteArray} {ptr free : UInt256}
    (hmem : 96 ≤ mem.size) (hdata : BytesObjectView mem ptr data)
    (hd : 32 ≤ data.size) (ho : 32 ≤ out.size) (hlo : 96 ≤ ptr.toNat+32)
    (hbefore : ptr.toNat+32+data.size ≤ free.toNat) (hfit : free.toNat+32 < UInt256.size) :
    UInt256.land bytes4Mask (memLoad (ptr+⟨32⟩) (solcReturnDataMem mem free out)) =
        UInt256.land bytes4Mask (memLoad (free+⟨32⟩) (solcReturnDataMem mem free out)) ↔
      data.extract 0 4 = out.extract 0 4 := by
  have hp : (ptr+⟨32⟩).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have hf : (free+⟨32⟩).toNat = free.toNat+32 := uadd_word_ofNat_toNat free 32 hfit
  have hs := returnDataMemory_size mem free out hmem hfit
  have hout := returnDataMemory_view mem free out hmem hfit
  have hi := hdata.inBounds
  rw [bytes4Mask_eq_iff, memLoad_prefix4 _ _ (by rw [hp, hs]; omega),
    memLoad_prefix4 _ _ (by rw [hf, hs]; omega), hp, hf,
    returnDataMemory_read_before _ _ _ _ _ (by omega) hlo (by omega) hfit]
  have hin := hdata.read 0 4 (by omega)
  have hret := hout.read 0 4 (by omega)
  simp only [Nat.add_zero, Nat.zero_add] at hin hret
  rw [hin, hret]

end Benchmarks.UniswapV4PoolManager
