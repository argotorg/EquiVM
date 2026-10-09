import Benchmarks.Morpho.MorphoBlue.HeapAdvance
import Benchmarks.Morpho.MorphoBlue.AccrueMemoryPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue

theorem heapAdvance_hash (mem : ByteArray) (fp key slot : UInt256) :
    HeapAdvance mem fp (twoWordHashMem key slot mem) fp 0 :=
  ⟨twoWordHashMem_prefix _ _ _ _, by omega⟩

theorem MorphoHeap.narrowAdvance {mem fp spare} (hm : MorphoHeap mem fp spare) :
    HeapAdvance mem fp (uint128ErrorMem mem) (fp + UInt256.ofNat 64) 64 :=
  ⟨hm.narrowPrefix, uadd_word_ofNat_toNat fp 64 (by have hh := hm.space; change _ < 2 ^ 256; omega)⟩

theorem MorphoHeap.callDataAdvance {mem fp spare} (hm : MorphoHeap mem fp spare)
    (p : MarketParamsWords) (σ : AccountMap) (I : ExecutionEnv) :
    HeapAdvance mem fp (accrueCallDataMem p σ I mem fp) fp 0 :=
  ⟨hm.callDataPrefix p σ I, by omega⟩

theorem MorphoHeap.callReturnAdvance {mem fp spare} (hm : MorphoHeap mem fp spare)
    (out : ByteArray) (hb : out.size < UInt256.size) (hin : fp.toNat + 32 ≤ mem.size) :
    HeapAdvance mem fp (accrueCallMem mem out fp) (fp + UInt256.ofNat 32) 32 :=
  ⟨hm.callReturnPrefix out hb hin,
    uadd_word_ofNat_toNat fp 32 (by have hh := hm.space; change _ < 2 ^ 256; omega)⟩

theorem MorphoHeap.eventAdvance {mem fp spare} (hm : MorphoHeap mem fp spare)
    (rate interest shares : UInt256) :
    HeapAdvance mem fp (accrueEventMem mem rate interest shares) fp 0 :=
  ⟨hm.eventPrefix rate interest shares, by omega⟩

theorem MorphoHeap.feeMemAdvance {mem fp spare} (hm : MorphoHeap mem fp spare)
    (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) :
    HeapAdvance mem fp (accrueFeeMem σ I id mem) (fp + UInt256.ofNat 64) 64 :=
  ⟨hm.feeMemPrefix σ I id,
    uadd_word_ofNat_toNat fp 64 (by have hh := hm.space; change _ < 2 ^ 256; omega)⟩

end Benchmarks.Morpho.MorphoBlue
