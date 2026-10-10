import Benchmarks.UniswapV4PoolManager.PoolModifyTrace
import Benchmarks.UniswapV4PoolManager.MemorySliceHash

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem MemorySlice.poolModifyTicks {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (ptr id : UInt256) (p : PoolModifyParams) (evm : State)
    (hb : 64 ≤ base) (hp : base+data.size ≤ ptr.toNat) (hf : ptr.toNat+128 < UInt256.size) :
    MemorySlice (poolModifyTicksMemory mem ptr id p evm) base data := by
  have h32 : (ptr+⟨32⟩).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have h64 : (ptr+⟨64⟩).toNat = ptr.toNat+64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have h96 : (ptr+⟨96⟩).toNat = ptr.toNat+96 := uadd_word_ofNat_toNat ptr 96 (by omega)
  have hlo : MemorySlice (poolModifyLowerMemory mem ptr id p evm) base data := by
    unfold poolModifyLowerMemory tickLowerResultMemory
    exact (((h.twoWordHash _ _ hb).writeWord _ _ (.inl (by omega))).writeWord _ _ (.inl hp)).twoWordHash _ _ hb
  have htwo : MemorySlice (poolModifyTwoTicksMemory mem ptr id p evm) base data := by
    unfold poolModifyTwoTicksMemory tickUpperResultMemory
    exact (hlo.writeWord _ _ (.inl (by omega))).writeWord _ _ (.inl (by omega))
  unfold poolModifyTicksMemory
  split_ifs
  · unfold poolModifyTicksActiveMemory poolModifyBitmapsMemory poolModifyFlipMemory
    exact (htwo.conditionalHash _ _ _ hb).conditionalHash _ _ _ hb
  · exact h

theorem MemorySlice.poolModifyAccounting {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (free id : UInt256) (p : PoolModifyParams) (fl fu : Bool)
    (hb : 64 ≤ base) (hp : base+data.size ≤ free.toNat) :
    MemorySlice (poolModifyAccountingMemory mem free id p fl fu) base data := by
  have hfees : MemorySlice (poolModifyFeesMemory mem free id p) base data := by
    unfold poolModifyFeesMemory positionGetMemory
    apply MemorySlice.twoWordHash _ _ _ hb
    unfold positionKeyCleanMemory positionKeyMemory
    have hi := (h.twoWordHash p.lower (poolSlot id+⟨4⟩) hb).twoWordHash p.upper (poolSlot id+⟨4⟩) hb
    exact ((((((hi.writeWord _ _ (.inl (by omega))).writeWord _ _ (.inl (by omega))).writeWord _ _
      (.inl (by omega))).writeWord _ _ (.inl hp)).writeWord _ _ (.inl (by omega))).writeWord _ _
      (.inl (by omega))).writeWord _ _ (.inl hp)
  unfold poolModifyAccountingMemory poolModifyClearsMemory
  split_ifs
  · exact (hfees.conditionalHash _ _ fl hb).conditionalHash _ _ fu hb
  · exact hfees

/-- The inlined pool function preserves the caller's allocated records. -/
theorem MemorySlice.poolModify {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (params ptr id : UInt256) (p : PoolModifyParams) (evm : State)
    (hb : 96 ≤ base) (hp : base+data.size ≤ params.toNat) (hpb : params.toNat+192 ≤ ptr.toNat)
    (hf : ptr.toNat+128 < UInt256.size) :
    MemorySlice (poolModifyMemory mem params ptr id p evm) base data := by
  have hparams : MemorySlice (poolModifyParamsMemory mem params ptr p) base data :=
    (h.writeWord 64 ptr (.inr hb)).wordSequence _ _ hp
  have halloc : MemorySlice
      (poolModifyAllocationMemory (poolModifyParamsMemory mem params ptr p) ptr) base data :=
    (hparams.writeWord 64 (ptr+UInt256.ofNat 128) (.inr hb)).wordSequence _ _ (by omega)
  have hticks := halloc.poolModifyTicks ptr id p evm (by omega) (by omega) hf
  exact hticks.poolModifyAccounting (ptr+UInt256.ofNat 128) id p _ _ (by omega)
    (by rw [uadd_word_ofNat_toNat ptr 128 hf]; omega)

theorem poolModifyMemory_free (mem : ByteArray) (params ptr id : UInt256) (p : PoolModifyParams)
    (evm : State) (hp : 160 ≤ params.toNat) (hpb : params.toNat+192 ≤ ptr.toNat)
    (hf : ptr.toNat+128 < UInt256.size) :
    memLoad (UInt256.ofNat 64) (poolModifyMemory mem params ptr id p evm) = ptr+UInt256.ofNat 128 := by
  have hs : 160 ≤ (poolModifyParamsMemory mem params ptr p).size := by
    rw [poolModifyParamsMemory_size]; omega
  have hsa : 160 ≤ (poolModifyAllocationMemory (poolModifyParamsMemory mem params ptr p) ptr).size := by
    rw [poolModifyAllocationMemory_size]; omega
  have hst := poolModifyTicksMemory_size_ge
    (poolModifyAllocationMemory (poolModifyParamsMemory mem params ptr p) ptr) ptr id p evm (by omega)
  have h128 := uadd_word_ofNat_toNat ptr 128 hf
  unfold poolModifyMemory poolModifyAllocatedMemory poolModifyAfterPreludeMemory poolModifyAccountingMemory
  rw [poolModifyClearsMemory_loadWord _ _ _ _ _ (UInt256.ofNat 64) (by decide)
      (by rw [poolModifyFeesMemory_size _ _ _ _ (by omega)]; change 96 ≤ _; omega),
    poolModifyFeesMemory_load_before _ _ _ _ (UInt256.ofNat 64) (by decide)
      (by change 96 ≤ _; omega) (by change 96 ≤ (ptr+UInt256.ofNat 128).toNat; omega),
    poolModifyTicksMemory_load_before _ _ _ _ _ (UInt256.ofNat 64) (by decide)
      (by change 96 ≤ _; omega) (by change 96 ≤ ptr.toNat; omega) hf,
    poolModifyAllocationMemory_free _ _ (by omega)]

end Benchmarks.UniswapV4PoolManager
