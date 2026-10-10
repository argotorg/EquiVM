import Benchmarks.UniswapV3.Pool.OracleReadCost
import Benchmarks.UniswapV3.Pool.MemoryGasBound

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleReadMemory_eq {mem : ByteArray} {aw p : UInt256}
    (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) (hm : HeapMemory mem aw p)
    (hb : p.toNat + 128 ≤ 2 ^ 200) :
    uniswapV3Pool_block_20474_memory (ee := I) (σ := σ) (mem := mem)
      (x0 := index) (x1 := UInt256.ofNat 8) =
      observationReadHeadMem mem p (oracleStoredObservation index σ I) := by
  rw [← observationReadHeadMem_eq index σ I hm hb]
  simp only [uniswapV3Pool_block_20474_memory, uniswapV3Pool_block_13226_memory,
    u256_add_comm (UInt256.ofNat 8) index, u256_land_comm]

theorem oracleReadHeadAw_active_cursor {mem : ByteArray} {aw p : UInt256}
    (hm : MemoryCursor mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) :
    ActiveWords (oracleReadHeadAw mem aw) := by
  have hp32 : (p + UInt256.ofNat 32).toNat = p.toNat + 32 :=
    uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hp64 : (p + UInt256.ofNat 64).toNat = p.toNat + 64 :=
    uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)
  have hload : loadedWord mem (UInt256.ofNat 64) = p := hm.load64
  have h64 : expandedWords aw (UInt256.ofNat 64) ⟨32⟩ = aw := expandedWords64_eq hm.active
  simp only [oracleReadHeadAw, hload, h64]
  exact activeWords_expand32
    (activeWords_expand32
      (activeWords_expand32 hm.active (show p.toNat + 32 ≤ 2 ^ 200 by omega))
      (show (p + UInt256.ofNat 32).toNat + 32 ≤ 2 ^ 200 by rw [hp32]; omega))
    (show (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 by rw [hp64]; omega)

theorem oracleReadHeadAw_active {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) :
    ActiveWords (oracleReadHeadAw mem aw) := by
  exact oracleReadHeadAw_active_cursor hm.cursor hb

theorem oracleReadHeadAtX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p index : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (start : Nat)
    (hstart : start = 20474 ∨ start = 20610 ∨ start = 18869)
    (rd : RD (deployedRuntime v) ee g s0 (UInt256.ofNat start)
      (index :: UInt256.ofNat 8 :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 6 ≤ 1024) :
    let last := oracleStoredObservation index σ ee
    ∃ k' C', C + 1 + (Cₘ (oracleReadHeadAw mem aw) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat (start + 86))
        (p :: UInt256.ofNat 96 :: (if last.initialized then ⟨1⟩ else ⟨0⟩) :: p :: R)
        (observationReadHeadMem mem p last) (oracleReadHeadAw mem aw) rdata σ k' C' := by
  dsimp only
  obtain ⟨k', C', hcost, hout⟩ := oracleReadHeadAtMonoX (v := v) start hstart rd hov
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hi := oracleStoredInitialized index σ ee
  rw [u256_land_comm] at hi
  dsimp only [solcSlotWordAt, observationSlot] at hi
  have hmem := oracleReadMemory_eq index σ ee hm hb
  refine ⟨k', C', hcost, ?_⟩
  simpa only [uniswapV3Pool_block_20474_stack, hload, ← hi, hmem] using hout

theorem oracleReadHeadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p index : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (oracleReadStart second))
      (index :: UInt256.ofNat 8 :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 6 ≤ 1024) :
    let last := oracleStoredObservation index σ ee
    ∃ k' C', C + 1 + (Cₘ (oracleReadHeadAw mem aw) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat (oracleReadStart second + 86))
        (p :: UInt256.ofNat 96 :: (if last.initialized then ⟨1⟩ else ⟨0⟩) :: p :: R)
        (observationReadHeadMem mem p last) (oracleReadHeadAw mem aw) rdata σ k' C' := by
  exact oracleReadHeadAtX (v := v) (oracleReadStart second)
    (by cases second <;> simp [oracleReadStart]) rd hm hb hov

theorem oracleReadCompletedMemory_cursor {mem : ByteArray} {aw p : UInt256}
    (last : OracleObservation) (hm : MemoryCursor mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) :
    let nextAw := M (oracleReadHeadAw mem aw) (p + UInt256.ofNat 96) ⟨32⟩
    HeapMemory (wordArrayAllocMem mem p last.words) nextAw (p + ⟨128⟩) ∧
      ObservationMemory (wordArrayAllocMem mem p last.words) p last ∧
      MemoryPrefix mem (wordArrayAllocMem mem p last.words) p.toNat ∧
      (p + ⟨128⟩).toNat ≤ nextAw.toNat * 32 + 32 := by
  dsimp only
  have hp96 : (p + UInt256.ofNat 96).toNat = p.toNat + 96 :=
    uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)
  have hp128 : (p + (⟨128⟩ : UInt256)).toNat = p.toNat + 128 :=
    uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
  have hactive := oracleReadHeadAw_active_cursor hm hb
  have hlast : (p + UInt256.ofNat 96).toNat + 32 ≤ 2 ^ 200 := by rw [hp96]; omega
  have ha := activeWords_expand32 hactive hlast
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact wordArrayAllocMem_heap mem p _ last.words hm.lower
      (by simp [OracleObservation.words]) hb ha
  · exact wordArrayAllocMem_region mem p last.words hm.lower (by simp [OracleObservation.words])
  · exact wordArrayAllocMem_prefix mem p last.words
  · change (p + (⟨128⟩ : UInt256)).toNat ≤
      (expandedWords (oracleReadHeadAw mem aw) (p + UInt256.ofNat 96) ⟨32⟩).toNat * 32 + 32
    have hc := expandedWords32_cover hactive hlast
    rw [hp96] at hc
    rw [hp128]
    omega

theorem oracleReadCompletedMemory {mem : ByteArray} {aw p : UInt256}
    (last : OracleObservation) (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) :
    let nextAw := M (oracleReadHeadAw mem aw) (p + UInt256.ofNat 96) ⟨32⟩
    HeapMemory (wordArrayAllocMem mem p last.words) nextAw (p + ⟨128⟩) ∧
      ObservationMemory (wordArrayAllocMem mem p last.words) p last ∧
      MemoryPrefix mem (wordArrayAllocMem mem p last.words) p.toNat ∧
      (p + ⟨128⟩).toNat ≤ nextAw.toNat * 32 + 32 := by
  exact oracleReadCompletedMemory_cursor last hm.cursor hb

end Benchmarks.UniswapV3.Pool
