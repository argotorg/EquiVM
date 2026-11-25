import Benchmarks.Midnight.TouchMarketLargeFunding

/-! The final hash allocation is at most eleven bytes beyond the initialized heap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem touchMarketHashFree_space (mem : ByteArray) (root : UInt256) (m : MarketData)
    (hb : root.toNat + 2 * m.encodingSize + 288 < 2^64) :
    (touchMarketHashFree root m).toNat ≤ (touchMarketHashMemory mem root m).size + 11 := by
  have hpre := (marketIdPointers m hb).2.2
  have hf : (touchMarketHashFree root m).toNat = (marketIdPreimagePtr root m).toNat + 128 :=
    uadd_word_ofNat_toNat _ _ (by rw [hpre]; change _ < 2^256; omega)
  have hsize : (marketIdPreimagePtr root m).toNat + 117 ≤
      (touchMarketHashMemory mem root m).size := by
    dsimp only [touchMarketHashMemory, marketIdWorkMemory, marketIdMemory]
    rw [twoWordHashMem_size_of_ge_64 _ _ (by rw [writeWord_sparse_size]; omega),
      writeWord_sparse_size, writeWord_sparse_size, marketIdPayload_size]
    omega
  omega

end Benchmarks.Midnight
