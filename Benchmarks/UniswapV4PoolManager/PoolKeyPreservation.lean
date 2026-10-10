import Benchmarks.UniswapV4PoolManager.PoolKeyView
import Benchmarks.UniswapV4PoolManager.ReturnDataMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem PoolKeyView.twoWordHash {mem ptr key} (h : PoolKeyView mem ptr key)
    (a b : UInt256) (hlo : 64 ≤ ptr.toNat) : PoolKeyView (twoWordHashMem a b mem) ptr key :=
  (h.writeWord 0 a (.inr (by omega))).writeWord 32 b (.inr (by omega))

theorem PoolKeyView.returnData {mem ptr key} (h : PoolKeyView mem ptr key)
    (free : UInt256) (out : ByteArray) (hlo : 96 ≤ ptr.toNat)
    (hb : ptr.toNat+160 ≤ free.toNat) (hf : free.toNat+32 < UInt256.size) :
    PoolKeyView (solcReturnDataMem mem free out) ptr key := by
  refine ⟨h.slice.returnData free out hlo ?_ hf, h.fits⟩
  simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hb

-- LIBRARY CANDIDATE: mapping scratch stores preserve the free-pointer word.
theorem twoWordHashMem_free {mem : ByteArray} (a b : UInt256) (hm : 96 ≤ mem.size) :
    memLoad ⟨64⟩ (twoWordHashMem a b mem) = memLoad ⟨64⟩ mem := by
  rw [memLoad, memLoad, if_neg (by rw [twoWordHashMem_size_of_ge_64' a b (by omega)]; change ¬64 ≥ _; omega),
    if_neg (by change ¬64 ≥ _; omega)]
  change UInt256.ofNat (fromByteArrayBigEndian ((twoWordHashMem a b mem).readWithPadding 64 32)) = _
  rw [twoWordHashMem_read_above64 a b 64 (by omega) (by omega)]
  rfl

end Benchmarks.UniswapV4PoolManager
