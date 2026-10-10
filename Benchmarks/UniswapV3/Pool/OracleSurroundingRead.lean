import Benchmarks.UniswapV3.Pool.OracleSurroundingReadCost
import Benchmarks.UniswapV3.Pool.OracleSearchBefore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSurroundingHeadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p index : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18675⟩
      (index :: UInt256.ofNat 8 :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 8 ≤ 1024) :
    let last := oracleStoredObservation index σ ee
    ∃ k' C', C + 1 + (Cₘ (oracleReadHeadAw mem aw) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨18761⟩
        (p :: UInt256.ofNat 96 :: (if last.initialized then ⟨1⟩ else ⟨0⟩) ::
          p :: last.timestamp :: R)
        (observationReadHeadMem mem p last) (oracleReadHeadAw mem aw) rdata σ k' C' := by
  dsimp only
  obtain ⟨k', C', hcost, hout⟩ := oracleSurroundingHeadMonoX (v := v) rd hov
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hi := oracleStoredInitialized index σ ee
  have ht := oracleStoredTimestamp index σ ee
  have hslot : UInt256.ofNat 8 + index = observationSlot index := u256_add_comm _ _
  simp only [solcSlotWordAt] at ht hi
  have hmem : uniswapV3Pool_block_18675_memory (ee := ee) (σ := σ) (mem := mem)
      (x0 := index) (x1 := UInt256.ofNat 8) =
      observationReadHeadMem mem p (oracleStoredObservation index σ ee) :=
    observationReadHeadMem_eq index σ ee hm hb
  refine ⟨k', C', hcost, ?_⟩
  simpa only [uniswapV3Pool_block_18675_stack, hload, hslot, ← hi, ← ht, hmem] using hout

theorem oracleSurroundingFallbackMemory {mem : ByteArray} {aw p : UInt256}
    (σ : AccountMap) (I : ExecutionEnv) (hm : HeapMemory mem aw p)
    (hb : p.toNat + 128 ≤ 2 ^ 200) :
    uniswapV3Pool_block_18966_memory (ee := I) (σ := σ) (mem := mem)
      (x8 := UInt256.ofNat 8) =
      wordArrayAllocMem mem p (oracleStoredObservation ⟨0⟩ σ I).words := by
  rw [← observationReadHeadMem_write, ← observationReadHeadMem_eq ⟨0⟩ σ I hm hb]
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hp96 : (p + UInt256.ofNat 96).toNat = p.toNat + 96 :=
    uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)
  have hi := oracleStoredInitialized ⟨0⟩ σ I
  simp only [solcSlotWordAt, observationSlot, u256_zero_add] at hi
  simp only [uniswapV3Pool_block_18966_memory, uniswapV3Pool_block_13226_memory,
    show (UInt256.ofNat 8) + (⟨0⟩ : UInt256) = UInt256.ofNat 8 from u256_add_zero _,
    hload, hp96]
  rw [hi]
  rfl

theorem oracleSurroundingFallbackX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p afterPtr beforePtr cardRaw liquidity index : UInt256}
    {tickRaw targetRaw timeRaw ret : UInt256} {mem rdata : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18966⟩
      (afterPtr :: beforePtr :: cardRaw :: liquidity :: index :: tickRaw :: targetRaw ::
        timeRaw :: ⟨8⟩ :: ret :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', C + 1 + (Cₘ (oracleReadFullAw mem aw p) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨19052⟩
        (afterPtr :: p :: cardRaw :: liquidity :: index :: tickRaw :: targetRaw ::
          timeRaw :: ⟨8⟩ :: ret :: R)
        (wordArrayAllocMem mem p (oracleStoredObservation ⟨0⟩ σ ee).words)
        (oracleReadFullAw mem aw p) rdata σ k' C' := by
  obtain ⟨k', C', hcost, hout⟩ := oracleSurroundingFallbackMonoX (v := v) rd (by evm_ov)
  have hload : loadedWord mem (UInt256.ofNat 64) = p := hm.load64
  have hload' : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hmem := oracleSurroundingFallbackMemory σ ee hm hb
  change uniswapV3Pool_block_18966_memory (ee := ee) (σ := σ) (mem := mem)
    (x8 := ⟨8⟩) = _ at hmem
  refine ⟨k', C', ?_, ?_⟩
  · simpa only [hload] using hcost
  · simpa only [uniswapV3Pool_block_18966_stack, hload, hload',
      hmem] using hout

end Benchmarks.UniswapV3.Pool
