import Benchmarks.Midnight.MarketEncoder
import Benchmarks.Midnight.MarketBytesMemory
import Benchmarks.Midnight.RuntimeBlocks_081

variable {fork : Ethereum.Fork}

/-! Encode and emit MarketCreated, then return the market identifier. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def marketCreatedMemory (mem : ByteArray) (root : UInt256) (m : MarketData) : ByteArray :=
  marketEncodeMemory (writeWord mem root.toNat (UInt256.ofNat 32)) (root.toNat + 32) m

theorem marketCreatedMemory_prefix (mem : ByteArray) (root : UInt256) (m : MarketData) :
    MemoryPrefix mem (marketCreatedMemory mem root m) root.toNat :=
  (memoryPrefix_writeWord _ _ _ _ (Or.inl le_rfl)).trans
    (marketEncodeMemory_prefix _ _ _ m (by omega))

theorem marketCreatedMemory_free (mem : ByteArray) (root : UInt256) (m : MarketData)
    (hroot : 96 ≤ root.toNat) (hsize : 96 ≤ mem.size) :
    memLoad (UInt256.ofNat 64) (marketCreatedMemory mem root m) =
      memLoad (UInt256.ofNat 64) mem := by
  unfold marketCreatedMemory marketEncodeMemory marketEncodeHeadMemory
  rw [memLoad_writeWordArray_below, memLoad_writeWordArray_below,
    memLoad_writeWord_preserved, memLoad_writeWordArray_below, memLoad_writeWord_preserved]
  all_goals
    first
    | exact Or.inl (by change 64 + 32 ≤ _; omega)
    | (change 64 + 32 ≤ _; omega)
    | (apply le_trans (show 96 ≤ _ from ?_) (writeWordArray_size_ge _ _ _)
       simp only [writeWord_sparse_size]
       omega)
    | (simp only [writeWord_sparse_size]; change 64 + 32 ≤ _; omega)

set_option maxRecDepth 2000000 in
theorem midnightMarketCreated {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr limit root id ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 22 ≤ 1024) (hm : MarketStored mem ptr arrayPtr limit m)
    (hlimit : limit.toNat ≤ root.toNat) (hb : root.toNat + m.encodingSize < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root) (hperm : I.perm = true)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨21682⟩ (ptr :: id :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ret (id :: R)
      (marketCreatedMemory mem root m) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_21682
    (by simp only [List.length_cons]; omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_21682_stack,
    midnightBlocks.midnight_block_21682_memory, hfree] at rd1
  let mem1 := writeWord mem root.toNat (UInt256.ofNat 32)
  change RD fork _ _ _ _ _ _ mem1 _ _ _ _ _ at rd1
  have hp : MemoryPrefix mem mem1 limit.toNat :=
    memoryPrefix_writeWord _ _ _ _ (Or.inl hlimit)
  have hm1 := hm.preserve hp
  have ho : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by dsimp only [MarketData.encodingSize] at hb; omega)
  obtain ⟨aw2, k2, C2, rd2⟩ := midnightMarketEncoder m
    (by simp only [List.length_cons]; omega) hm1.words
    (hm1.header.load_word ⟨0, by simp⟩ (by simp)) (by simpa using hm1.header.size)
    hm1.collaterals (by have := hm.array; have := hm.extent; omega) hm.extent
    (by rw [ho]; omega) (by rw [ho]; dsimp only [MarketData.encodingSize] at hb; omega)
    (by jump_dest) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := midnightBlocks.midnight_block_21739_packed
    (by omega) hperm hret rd2
  exact ⟨aw3, k3, C3, by simpa only [midnightBlocks.midnight_block_21739_stack, ho] using rd3⟩

end Benchmarks.Midnight
