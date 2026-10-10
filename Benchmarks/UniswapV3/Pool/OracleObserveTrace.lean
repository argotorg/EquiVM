import Benchmarks.UniswapV3.Pool.OracleObservationRead
import Benchmarks.UniswapV3.Pool.OracleObserveSource
import Benchmarks.UniswapV3.Pool.OracleTransform
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_044
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_046

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveZeroReturnX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret ptr cardinality liquidity index tickRaw timeRaw : UInt256}
    {last : OracleObservation} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13340⟩
      (ptr :: ⟨0⟩ :: ⟨0⟩ :: cardinality :: liquidity :: index :: tickRaw :: ⟨0⟩ :: timeRaw ::
        UInt256.ofNat 8 :: ret :: R) mem aw rdata σ k C)
    (hh : HeapMemory mem aw p) (hm : ObservationMemory mem ptr last)
    (hb : ptr.toNat + 128 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 14 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
      (last.secondsPerLiquidity :: EVM.wordOfInt last.tickCumulative :: R) mem aw' rdata σ k' C' ∧
      HeapMemory mem aw' p := by
  have hl := hm.load_tick (by change _ < 2 ^ 256; omega)
  have hs := hm.load_seconds (by change _ < 2 ^ 256; omega)
  have ht32 : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  have ht64 : (ptr + UInt256.ofNat 64).toNat = ptr.toNat + 64 :=
    uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)
  have rdLoad := uniswapV3Pool_block_13340 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_13340_stack, u256_add_comm (UInt256.ofNat 32) ptr,
    u256_add_comm (UInt256.ofNat 64) ptr, hl, hs] at rdLoad
  have rdReturn := uniswapV3Pool_block_13584 (immWords := wordsOf (immStore v)) (by evm_ov) hret rdLoad
  have ha := activeWords_expand32
    (activeWords_expand32 hh.active (show (ptr + UInt256.ofNat 32).toNat + 32 ≤ 2 ^ 200 by rw [ht32]; omega))
    (show (ptr + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 by rw [ht64]; omega)
  exact ⟨_, _, _, rdReturn, {hh with active := ha}⟩

theorem oracleObserveZeroFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret cardinality liquidity index tickRaw timeRaw time : UInt256}
    {tick : Int} {last : OracleObservation} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13311⟩
      ((if last.initialized then ⟨1⟩ else ⟨0⟩) :: UInt256.ofNat 4294967295 :: p ::
        last.timestamp :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: cardinality :: liquidity :: index :: tickRaw ::
        ⟨0⟩ :: timeRaw :: UInt256.ofNat 8 :: ret :: R)
      (observationReadHeadMem mem p last) aw rdata σ k C)
    (ha : ActiveWords aw) (hp : 128 ≤ p.toNat) (hb : p.toNat + 384 ≤ 2 ^ 200)
    (htime : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = time)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 30 ≤ 1024) :
    ∃ mem' aw' p' k' C', RD (deployedRuntime v) ee g s0 ret
      ((oracleObserveZeroResult last time tick liquidity).secondsPerLiquidity ::
        EVM.wordOfInt (oracleObserveZeroResult last time tick liquidity).tickCumulative :: R)
      mem' aw' rdata σ k' C' ∧ HeapMemory mem' aw' p' ∧
      p'.toNat ≤ p.toNat + 384 ∧ MemoryPrefix mem mem' p.toNat := by
  have hp96 : (p + UInt256.ofNat 96).toNat = p.toNat + 96 :=
    uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)
  have hpn : (p + (⟨128⟩ : UInt256)).toNat = p.toNat + 128 :=
    uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
  have hmem : uniswapV3Pool_block_13311_taken_memory (mem := observationReadHeadMem mem p last)
      (x0 := if last.initialized then ⟨1⟩ else ⟨0⟩) (x2 := p) =
      wordArrayAllocMem mem p last.words := by
    simp only [uniswapV3Pool_block_13311_taken_memory, hp96]
    exact observationReadHeadMem_write mem p last
  have hmemf : uniswapV3Pool_block_13311_fallthrough_memory (mem := observationReadHeadMem mem p last)
      (x0 := if last.initialized then ⟨1⟩ else ⟨0⟩) (x2 := p) =
      wordArrayAllocMem mem p last.words := hmem
  have haRead := activeWords_expand32 ha
    (show (p + UInt256.ofNat 96).toNat + 32 ≤ 2 ^ 200 by rw [hp96]; omega)
  have hhRead : HeapMemory (wordArrayAllocMem mem p last.words)
      (M aw (p + UInt256.ofNat 96) ⟨32⟩) (p + ⟨128⟩) :=
    wordArrayAllocMem_heap mem p _ _ hp (by simp [OracleObservation.words]) (by change p.toNat + 128 ≤ _; omega) haRead
  have hmRead : ObservationMemory (wordArrayAllocMem mem p last.words) p last :=
    wordArrayAllocMem_region mem p last.words hp (by simp [OracleObservation.words])
  have hpre := wordArrayAllocMem_prefix mem p last.words
  have ht : UInt256.land timeRaw (UInt256.ofNat 4294967295) = time := htime
  by_cases heq : last.timestamp = time
  · have rdReady := uniswapV3Pool_block_13311_taken (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [ht, heq, uInt256_eq_self]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_13311_taken_stack, hmem] at rdReady
    obtain ⟨ar, kr, Cr, rdReturn, hhReturn⟩ := oracleObserveZeroReturnX (v := v) rdReady hhRead hmRead
      (by omega) hret (by evm_ov)
    refine ⟨_, ar, _, kr, Cr, ?_, hhReturn, ?_, hpre⟩
    · simpa only [oracleObserveZeroResult, if_pos heq] using rdReturn
    · rw [hpn]; omega
  · have hne : UInt256.eq time last.timestamp = UInt256.ofNat 0 := by
      apply uInt256_eq_zero_of_ne
      intro h
      exact heq (uInt256_eq_one_eq h).symm
    have rdTransform := uniswapV3Pool_block_13311_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [ht]; exact hne) rd
    simp only [uniswapV3Pool_block_13311_fallthrough_stack, hmemf] at rdTransform
    have rdCall := uniswapV3Pool_block_13326 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdTransform
    simp only [uniswapV3Pool_block_13326_stack] at rdCall
    obtain ⟨atf, kt, Ct, rdUpdated, hhUpdated, hmUpdated, hpreUpdated⟩ := oracleTransformX (v := v)
      rdCall hhRead hmRead (by omega) (by rw [hpn]) (by rw [hpn]; omega) htime htick hliq
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
    have rdReady := uniswapV3Pool_block_13337 (immWords := wordsOf (immStore v)) (by evm_ov) rdUpdated
    simp only [uniswapV3Pool_block_13337_stack] at rdReady
    have hptr : ((p + (⟨128⟩ : UInt256)) + ⟨128⟩).toNat = p.toNat + 256 := by
      have hn : ((p + (⟨128⟩ : UInt256)) + ⟨128⟩).toNat = (p + (⟨128⟩ : UInt256)).toNat + 128 :=
        uadd_word_ofNat_toNat _ 128 (by rw [hpn]; change _ < 2 ^ 256; omega)
      rw [hn, hpn]
    have hfree : ((p + (⟨128⟩ : UInt256)) + ⟨256⟩).toNat = p.toNat + 384 := by
      have hn : ((p + (⟨128⟩ : UInt256)) + ⟨256⟩).toNat = (p + (⟨128⟩ : UInt256)).toNat + 256 :=
        uadd_word_ofNat_toNat _ 256 (by rw [hpn]; change _ < 2 ^ 256; omega)
      rw [hn, hpn]
    obtain ⟨ar, kr, Cr, rdReturn, hhReturn⟩ := oracleObserveZeroReturnX (v := v) rdReady hhUpdated hmUpdated
      (by rw [hptr]; omega) hret (by evm_ov)
    refine ⟨_, ar, _, kr, Cr, ?_, hhReturn, ?_, ?_⟩
    · simpa only [oracleObserveZeroResult, if_neg heq] using rdReturn
    · rw [hfree]
    · exact hpre.trans (hpreUpdated.mono (by rw [hpn]; omega))


theorem oracleObserveSingleZeroX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret cardinality liquidity index tickRaw timeRaw time : UInt256}
    {tick : Int} {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13193⟩
      (cardinality :: liquidity :: index :: tickRaw :: ⟨0⟩ :: timeRaw :: UInt256.ofNat 8 :: ret :: R)
      mem aw rdata σ k C)
    (hh : HeapMemory mem aw p) (hb : p.toNat + 384 ≤ 2 ^ 200) (hin : index.toNat < 65535)
    (htime : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = time)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 30 ≤ 1024) :
    let last := oracleObserveZeroResult (oracleStoredObservation index σ ee) time tick liquidity
    ∃ mem' aw' p' k' C', RD (deployedRuntime v) ee g s0 ret
      (last.secondsPerLiquidity :: EVM.wordOfInt last.tickCumulative :: R) mem' aw' rdata σ k' C' ∧
      HeapMemory mem' aw' p' ∧ p'.toNat ≤ p.toNat + 384 ∧ MemoryPrefix mem mem' p.toNat := by
  dsimp only
  have hindex : UInt256.land (UInt256.ofNat 65535) index = index := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) index _ (by decide) (by change _ < 65536; omega)
  have rdBounds := uniswapV3Pool_block_13193_fallthrough (immWords := wordsOf (immStore v))
    (by evm_ov) (by decide) rd
  simp only [uniswapV3Pool_block_13193_fallthrough_stack] at rdBounds
  have rdRead := uniswapV3Pool_block_13208_taken (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [hindex, ult_one (a := index) (b := UInt256.ofNat 65535) hin]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdBounds
  simp only [uniswapV3Pool_block_13208_taken_stack, hindex] at rdRead
  obtain ⟨ar, kr, Cr, rdFinish, haFinish⟩ := observationReadX (v := v) rdRead hh (by omega) (by evm_ov)
  exact oracleObserveZeroFinishX (v := v) rdFinish haFinish hh.lower hb htime htick hliq hret hov

theorem oracleObserveSingleZeroInvalidX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret cardinality liquidity index tickRaw timeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13193⟩
      (cardinality :: liquidity :: index :: tickRaw :: ⟨0⟩ :: timeRaw :: UInt256.ofNat 8 :: ret :: R)
      mem aw rdata σ k C)
    (hidx : index.toNat < 2 ^ 16) (hin : ¬ index.toNat < 65535) (hov : R.length + 15 ≤ 1024) :
    RDinvalid (deployedRuntime v) g s0 := by
  have hindex : UInt256.land (UInt256.ofNat 65535) index = index := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) index _ (by decide) hidx
  have rdBounds := uniswapV3Pool_block_13193_fallthrough (immWords := wordsOf (immStore v))
    (by evm_ov) (by decide) rd
  simp only [uniswapV3Pool_block_13193_fallthrough_stack] at rdBounds
  have rdFail := uniswapV3Pool_block_13208_fallthrough (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [hindex]; exact ult_zero (by change 65535 ≤ index.toNat; omega)) rdBounds
  exact uniswapV3Pool_block_13225 (immWords := wordsOf (immStore v)) rdFail

end Benchmarks.UniswapV3.Pool

