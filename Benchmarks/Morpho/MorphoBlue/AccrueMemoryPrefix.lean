import Benchmarks.Morpho.MorphoBlue.AccrueFeeRefine
import Benchmarks.Morpho.MorphoBlue.SafeTransferCallMemory
import Benchmarks.Morpho.MorphoBlue.ReturnDataMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: mapping scratch writes preserve allocated memory above the scratch region.
theorem twoWordHashMem_prefix (key slot : UInt256) (mem : ByteArray) (limit : Nat) :
    MemoryPrefix mem (twoWordHashMem key slot mem) limit :=
  (memoryPrefix_sparse_writeWord mem 0 limit key (Or.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord _ 32 limit slot (Or.inr (by decide)))

theorem MorphoHeap.narrowPrefix {mem fp spare} (hm : MorphoHeap mem fp spare) :
    MemoryPrefix mem (uint128ErrorMem mem) fp.toNat :=
  morphoErrorMem_prefix _ _ hm.size hm.free (by have hh := hm.gap; omega)
    (by have hh := hm.space; change _ < 2 ^ 256; omega)

theorem MorphoHeap.callDataPrefix {mem fp spare} (hm : MorphoHeap mem fp spare)
    (p : MarketParamsWords) (σ : AccountMap) (I : ExecutionEnv) :
    MemoryPrefix mem (accrueCallDataMem p σ I mem fp) fp.toNat :=
  (twoWordHashMem_prefix p.id (UInt256.ofNat 3) mem fp.toNat).trans
    (staticWordCallMem_prefix _ _ _ fp.toNat fp.toNat le_rfl)

theorem MorphoHeap.callReturnPrefix {mem fp spare} (hm : MorphoHeap mem fp spare)
    (out : ByteArray) (hb : out.size < UInt256.size) (hin : fp.toNat + 32 ≤ mem.size) :
    MemoryPrefix mem (accrueCallMem mem out fp) fp.toNat :=
  (callOutput32_prefix mem out fp hb hin).trans
    (memoryPrefix_sparse_writeWord _ 64 fp.toNat (returnReservePtr fp 32) (Or.inr (by decide)))

theorem MorphoHeap.eventPrefix {mem fp spare} (hm : MorphoHeap mem fp spare)
    (rate interest shares : UInt256) : MemoryPrefix mem (accrueEventMem mem rate interest shares) fp.toNat := by
  have hb := hm.space
  rw [accrueEventMem, hm.free]
  rw [uadd_word_ofNat_toNat fp 32 (by change _ < 2 ^ 256; omega),
    uadd_word_ofNat_toNat fp 64 (by change _ < 2 ^ 256; omega)]
  exact (memoryPrefix_sparse_writeWord _ fp.toNat fp.toNat rate (Or.inl le_rfl)).trans
    ((memoryPrefix_sparse_writeWord _ (fp.toNat + 32) fp.toNat interest (Or.inl (by omega))).trans
      (memoryPrefix_sparse_writeWord _ (fp.toNat + 64) fp.toNat shares (Or.inl (by omega))))

theorem MorphoHeap.feePositionPrefix {mem fp spare} (hm : MorphoHeap mem fp spare)
    (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) :
    MemoryPrefix mem (accrueFeePositionMem σ I id mem) fp.toNat :=
  (twoWordHashMem_prefix id (UInt256.ofNat 2) mem fp.toNat).trans
    (twoWordHashMem_prefix _ _ _ fp.toNat)

theorem MorphoHeap.feeWritesPrefix {mem fp spare} (hm : MorphoHeap mem fp spare)
    (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) :
    MemoryPrefix mem (accrueFeeWritesMem σ I id mem) fp.toNat :=
  (hm.feePositionPrefix σ I id).trans (((hm.feePosition σ I id).narrowPrefix).trans
    (twoWordHashMem_prefix id (UInt256.ofNat 3) _ fp.toNat))

theorem MorphoHeap.feeMemPrefix {mem fp spare} (hm : MorphoHeap mem fp spare)
    (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) :
    MemoryPrefix mem (accrueFeeMem σ I id mem) fp.toNat :=
  (twoWordHashMem_prefix id (UInt256.ofNat 3) mem fp.toNat).trans
    ((twoWordHashMem_prefix id (UInt256.ofNat 3) _ fp.toNat).trans
      (((hm.hash id (UInt256.ofNat 3)).hash id (UInt256.ofNat 3)).feeWritesPrefix σ I id))

end Benchmarks.Morpho.MorphoBlue
