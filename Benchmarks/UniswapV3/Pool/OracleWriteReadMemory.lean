import Benchmarks.UniswapV3.Pool.OracleReadMemory
import Benchmarks.UniswapV3.Pool.OracleWriteModel
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_048

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleWriteReadMemory_eq {mem : ByteArray} {aw p : UInt256}
    (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) (hm : HeapMemory mem aw p)
    (hb : p.toNat + 128 ≤ 2 ^ 200) :
    uniswapV3Pool_block_14823_memory (ee := I) (σ := σ) (mem := mem)
      (x0 := index) (x1 := UInt256.ofNat 8) =
      observationReadHeadMem mem p (oracleStoredObservation index σ I) := by
  exact observationReadHeadMem_eq index σ I hm hb

theorem oracleWriteReadHeadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p index : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨14823⟩
      (index :: UInt256.ofNat 8 :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 9 ≤ 1024) :
    let last := oracleStoredObservation index σ ee
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14908⟩
      ((if last.initialized then ⟨1⟩ else ⟨0⟩) :: UInt256.ofNat 4294967295 :: p :: last.timestamp :: R)
      (observationReadHeadMem mem p last) (oracleReadHeadAw mem aw) rdata σ k' C' := by
  dsimp only
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hloaded : loadedWord mem (UInt256.ofNat 64) = p := hm.load64
  have hslot : UInt256.ofNat 8 + index = observationSlot index := u256_add_comm _ _
  have ht := oracleStoredTimestamp index σ ee
  have hi := oracleStoredInitialized index σ ee
  simp only [solcSlotWordAt] at ht hi
  have hmem := oracleWriteReadMemory_eq index σ ee hm hb
  obtain ⟨kr, Cr, rr⟩ := uniswapV3Pool_block_14823 (immWords := wordsOf (immStore v)) hov rd
  refine ⟨kr, Cr, ?_⟩
  simpa only [uniswapV3Pool_block_14823_stack, hload, hslot, ← ht, ← hi, hmem,
    oracleReadHeadAw, hloaded] using rr

def oracleWriteReadWords (a : OracleWriteArgs) (p : UInt256) : List UInt256 :=
  [p, ⟨0⟩, ⟨0⟩, a.cardinalityNext, a.cardinality, a.liquidity, EVM.wordOfInt a.tick,
    a.time, a.index, ⟨8⟩]

theorem oracleWriteReadFinishRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p timeRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14908⟩
      ((if (oracleStoredObservation a.index σ ee).initialized then ⟨1⟩ else ⟨0⟩) ::
        UInt256.ofNat 4294967295 :: p :: (oracleStoredObservation a.index σ ee).timestamp ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: a.cardinalityNext :: a.cardinality :: a.liquidity ::
        EVM.wordOfInt a.tick :: timeRaw :: a.index :: ⟨8⟩ :: R)
      (observationReadHeadMem mem p (oracleStoredObservation a.index σ ee))
      (oracleReadHeadAw mem aw) rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200)
    (ht : UInt256.land timeRaw (UInt256.ofNat 4294967295) = a.time) (hov : R.length + 16 ≤ 1024) :
    let last := oracleStoredObservation a.index σ ee
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0
      (if last.timestamp = a.time then ⟨14924⟩ else ⟨14935⟩)
      (oracleWriteReadWords {a with time := timeRaw} p ++ R) (wordArrayAllocMem mem p last.words) aw' rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p last.words) aw' (p + ⟨128⟩) ∧
      ObservationMemory (wordArrayAllocMem mem p last.words) p last := by
  dsimp only
  have hmask := ht
  have hp96 : (p + UInt256.ofNat 96).toNat = p.toNat + 96 :=
    uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)
  obtain ⟨hh, ho, _, _⟩ := oracleReadCompletedMemory (oracleStoredObservation a.index σ ee) hm hb
  by_cases heq : (oracleStoredObservation a.index σ ee).timestamp = a.time
  · have rr := uniswapV3Pool_block_14908_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hmask, heq, uInt256_eq_self]; decide) rd
    simp only [uniswapV3Pool_block_14908_fallthrough_stack,
      uniswapV3Pool_block_14908_fallthrough_memory, hp96] at rr
    change RD _ _ _ _ _ _
      (wordArrayAllocMem mem p (oracleStoredObservation a.index σ ee).words) _ _ _ _ _ at rr
    simp only [if_pos heq, oracleWriteReadWords, List.cons_append, List.nil_append]
    exact ⟨_, _, _, rr, hh, ho⟩
  · have hne : UInt256.eq a.time (oracleStoredObservation a.index σ ee).timestamp =
        UInt256.ofNat 0 := by
      apply uInt256_eq_zero_of_ne
      intro h
      exact heq (uInt256_eq_one_eq h).symm
    have rr := uniswapV3Pool_block_14908_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hmask, hne]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_14908_taken_stack,
      uniswapV3Pool_block_14908_taken_memory, hp96] at rr
    change RD _ _ _ _ _ _
      (wordArrayAllocMem mem p (oracleStoredObservation a.index σ ee).words) _ _ _ _ _ at rr
    simp only [if_neg heq, oracleWriteReadWords, List.cons_append, List.nil_append]
    exact ⟨_, _, _, rr, hh, ho⟩

theorem oracleWriteReadFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14908⟩
      ((if (oracleStoredObservation a.index σ ee).initialized then ⟨1⟩ else ⟨0⟩) ::
        UInt256.ofNat 4294967295 :: p :: (oracleStoredObservation a.index σ ee).timestamp ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: a.cardinalityNext :: a.cardinality :: a.liquidity ::
        EVM.wordOfInt a.tick :: a.time :: a.index :: ⟨8⟩ :: R)
      (observationReadHeadMem mem p (oracleStoredObservation a.index σ ee))
      (oracleReadHeadAw mem aw) rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200)
    (ht : a.time.toNat < 2 ^ 32) (hov : R.length + 16 ≤ 1024) :
    let last := oracleStoredObservation a.index σ ee
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0
      (if last.timestamp = a.time then ⟨14924⟩ else ⟨14935⟩)
      (oracleWriteReadWords a p ++ R) (wordArrayAllocMem mem p last.words) aw' rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p last.words) aw' (p + ⟨128⟩) ∧
      ObservationMemory (wordArrayAllocMem mem p last.words) p last := by
  exact oracleWriteReadFinishRawX (v := v) (timeRaw := a.time) a rd hm hb
    (u256LandMaskCleanOfToNat (bits := 32) _ _ (by decide) ht) hov

end Benchmarks.UniswapV3.Pool
