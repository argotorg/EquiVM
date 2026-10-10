import Benchmarks.UniswapV3.Pool.OracleObservationStorage
import Benchmarks.UniswapV3.Pool.ObservationMemory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_045

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleStoredTimestamp (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    (oracleStoredObservation index σ I).timestamp =
    UInt256.land (solcSlotWordAt (observationSlot index) σ I) (UInt256.ofNat 4294967295) := by
  simp only [oracleStoredObservation, observationFieldWord, Nat.pow_zero,
    show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl, word_div_one]
  rfl

theorem oracleStoredTick (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    EVM.wordOfInt (oracleStoredObservation index σ I).tickCumulative =
    UInt256.signextend (UInt256.ofNat 6)
      (UInt256.div (solcSlotWordAt (observationSlot index) σ I) (UInt256.ofNat 4294967296)) :=
  by
    have h := signextend_normalizeSint ⟨56, by decide⟩ (UInt256.ofNat 6)
      (UInt256.div (solcSlotWordAt (observationSlot index) σ I) (UInt256.ofNat 4294967296))
      (by decide) (by decide)
    simpa only [oracleStoredObservation, observationTickValue] using h.symm

theorem oracleStoredSeconds (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    (oracleStoredObservation index σ I).secondsPerLiquidity =
    UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (UInt256.div (solcSlotWordAt (observationSlot index) σ I)
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 88))) := by
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = UInt256.ofNat (256 ^ 20 - 1) := by native_decide
  have hshift : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 88) =
      UInt256.ofNat (256 ^ 11) := by native_decide
  rw [hmask, hshift, u256_land_comm]
  rfl

theorem oracleStoredInitialized (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    (if (oracleStoredObservation index σ I).initialized then (⟨1⟩ : UInt256) else ⟨0⟩) =
    UInt256.isZero (UInt256.isZero
      (UInt256.land (UInt256.ofNat 255)
        (UInt256.div (solcSlotWordAt (observationSlot index) σ I)
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248))))) := by
  have hshift : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248) =
      UInt256.ofNat (256 ^ 31) := by native_decide
  rw [hshift, u256_land_comm]
  change (if !decide (observationFieldWord index 31 1 σ I = ⟨0⟩) then ⟨1⟩ else ⟨0⟩) =
    UInt256.isZero (UInt256.isZero (observationFieldWord index 31 1 σ I))
  generalize observationFieldWord index 31 1 σ I = w
  by_cases hz : w = ⟨0⟩
  · subst w; rfl
  · simp only [hz, decide_false, Bool.not_false, ↓reduceIte, isZero_eq_zero_of_ne hz]
    rfl

def observationReadHeadMem (mem : ByteArray) (p : UInt256) (last : OracleObservation) : ByteArray :=
  writeWordArray (writeWord mem 64 (p + ⟨128⟩)) p.toNat
    [last.timestamp, EVM.wordOfInt last.tickCumulative, last.secondsPerLiquidity]

theorem observationReadHeadMem_eq_cursor {mem : ByteArray} {aw p : UInt256}
    (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) (hm : MemoryCursor mem aw p)
    (hb : p.toNat + 128 ≤ 2 ^ 200) :
    uniswapV3Pool_block_13226_memory (ee := I) (σ := σ) (mem := mem)
      (x0 := index) (x1 := UInt256.ofNat 8) =
    observationReadHeadMem mem p (oracleStoredObservation index σ I) := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hp32 : (p + UInt256.ofNat 32).toNat = p.toNat + 32 :=
    uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hp64 : (p + UInt256.ofNat 64).toNat = p.toNat + 64 :=
    uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)
  have hslot : UInt256.ofNat 8 + index = observationSlot index := u256_add_comm _ _
  simp only [uniswapV3Pool_block_13226_memory, hload, hp32, hp64, hslot,
    signextend_idem ⟨56, by decide⟩ (UInt256.ofNat 6) _ (by decide) (by decide)]
  change writeWord (writeWord (writeWord (writeWord mem 64 (p + ⟨128⟩)) p.toNat
    (UInt256.land (solcSlotWordAt (observationSlot index) σ I) (UInt256.ofNat 4294967295)))
    (p.toNat + 32) (UInt256.signextend (UInt256.ofNat 6)
      (UInt256.div (solcSlotWordAt (observationSlot index) σ I) (UInt256.ofNat 4294967296))))
    (p.toNat + 64) (UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (UInt256.div (solcSlotWordAt (observationSlot index) σ I)
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 88)))) = _
  rw [← oracleStoredTimestamp, ← oracleStoredTick, ← oracleStoredSeconds]
  rfl

theorem observationReadHeadMem_eq {mem : ByteArray} {aw p : UInt256}
    (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) (hm : HeapMemory mem aw p)
    (hb : p.toNat + 128 ≤ 2 ^ 200) :
    uniswapV3Pool_block_13226_memory (ee := I) (σ := σ) (mem := mem)
      (x0 := index) (x1 := UInt256.ofNat 8) =
    observationReadHeadMem mem p (oracleStoredObservation index σ I) := by
  exact observationReadHeadMem_eq_cursor index σ I hm.cursor hb

theorem observationReadHeadMem_write (mem : ByteArray) (p : UInt256) (last : OracleObservation) :
    writeWord (observationReadHeadMem mem p last) (p.toNat + 96)
      (if last.initialized then ⟨1⟩ else ⟨0⟩) = wordArrayAllocMem mem p last.words := rfl


theorem observationReadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p index : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13226⟩
      (index :: UInt256.ofNat 8 :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 9 ≤ 1024) :
    let last := oracleStoredObservation index σ ee
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨13311⟩
      ((if last.initialized then ⟨1⟩ else ⟨0⟩) :: UInt256.ofNat 4294967295 :: p :: last.timestamp :: R)
      (observationReadHeadMem mem p last) aw' rdata σ k' C' ∧ ActiveWords aw' := by
  dsimp only
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have h64 : M aw (UInt256.ofNat 64) ⟨32⟩ = aw := expandedWords64_eq hm.active
  have hp32 : (p + UInt256.ofNat 32).toNat = p.toNat + 32 :=
    uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hp64 : (p + UInt256.ofNat 64).toNat = p.toNat + 64 :=
    uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)
  have hslot : UInt256.ofNat 8 + index = observationSlot index := u256_add_comm _ _
  have ht := oracleStoredTimestamp index σ ee
  have hi := oracleStoredInitialized index σ ee
  simp only [solcSlotWordAt] at ht hi
  have hmem := observationReadHeadMem_eq index σ ee hm hb
  obtain ⟨kr, Cr, rdRead⟩ := uniswapV3Pool_block_13226 (immWords := wordsOf (immStore v)) hov rd
  simp only [uniswapV3Pool_block_13226_stack, hload, hslot, ← ht, ← hi, hmem, h64] at rdRead
  have ha := activeWords_expand32
    (activeWords_expand32
      (activeWords_expand32 hm.active (show p.toNat + 32 ≤ 2 ^ 200 by omega))
      (show (p + UInt256.ofNat 32).toNat + 32 ≤ 2 ^ 200 by rw [hp32]; omega))
    (show (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 by rw [hp64]; omega)
  exact ⟨_, kr, Cr, rdRead, ha⟩

end Benchmarks.UniswapV3.Pool

