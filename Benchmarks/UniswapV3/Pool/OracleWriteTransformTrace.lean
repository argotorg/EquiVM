import Benchmarks.UniswapV3.Pool.OracleWriteCardinalityTrace
import Benchmarks.UniswapV3.Pool.OracleTransform

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleWriteIndexInvalidRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p timeRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14985⟩
      (oracleWriteCardinalityWords {a with time := timeRaw} p ++ R) mem aw rdata σ k C)
    (hz : (oracleWriteCardinality a).toNat = 0) (hov : R.length + 14 ≤ 1024) :
    RDinvalid (deployedRuntime v) g s0 := by
  have hw : oracleWriteCardinality a = UInt256.ofNat 0 := uint256_toNat_eq_zero hz
  simp only [oracleWriteCardinalityWords, oracleWriteCardinality_setTime,
    List.cons_append, List.nil_append] at rd
  have rr := uniswapV3Pool_block_14985_fallthrough (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [hw]; rfl) rd
  exact uniswapV3Pool_block_15004 (immWords := wordsOf (immStore v)) rr

theorem oracleWriteIndexInvalidX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14985⟩
      (oracleWriteCardinalityWords a p ++ R) mem aw rdata σ k C)
    (hz : (oracleWriteCardinality a).toNat = 0) (hov : R.length + 14 ≤ 1024) :
    RDinvalid (deployedRuntime v) g s0 := by
  exact oracleWriteIndexInvalidRawX (v := v) (timeRaw := a.time) a rd hz hov

def oracleWriteTransformedWords (a : OracleWriteArgs) (p q : UInt256) : List UInt256 :=
  [q, p, oracleWriteCardinality a, oracleWriteIndex a, a.cardinalityNext, a.cardinality,
    a.liquidity, EVM.wordOfInt a.tick, a.time, a.index, ⟨8⟩]

theorem oracleWriteTransformRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p free ret timeRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (last : OracleObservation)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14985⟩
      (oracleWriteCardinalityWords {a with time := timeRaw} p ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits)
    (htime : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = a.time) (hn : (oracleWriteCardinality a).toNat ≠ 0)
    (hh : HeapMemory mem aw free) (hm : ObservationMemory mem p last)
    (hp : 96 ≤ p.toNat) (hl : p.toNat + 128 ≤ free.toNat)
    (hb : free.toNat + 256 ≤ 2 ^ 200) (hov : R.length + 27 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨15020⟩
      (oracleWriteTransformedWords {a with time := timeRaw} p (free + ⟨128⟩) ++ ret :: R)
      (oracleTransformMem mem free last a.time a.tick a.liquidity) aw' rdata σ k' C' ∧
      HeapMemory (oracleTransformMem mem free last a.time a.tick a.liquidity) aw' (free + ⟨256⟩) ∧
      ObservationMemory (oracleTransformMem mem free last a.time a.tick a.liquidity)
        (free + ⟨128⟩) (oracleTransformed last a.time a.tick a.liquidity) := by
  have hc : UInt256.land (UInt256.ofNat 65535) (oracleWriteCardinality a) =
      oracleWriteCardinality a := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide) (oracleWriteCardinality_lt a hfit)
  have hnw : oracleWriteCardinality a ≠ UInt256.ofNat 0 := by
    intro hz
    apply hn
    rw [hz]
    rfl
  have ht := htime
  have hk : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt a.tick) =
      EVM.wordOfInt a.tick := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ hfit.2.2.1.1 hfit.2.2.1.2]
  simp only [oracleWriteCardinalityWords, oracleWriteCardinality_setTime,
    List.cons_append, List.nil_append] at rd
  have r1 := uniswapV3Pool_block_14985_taken (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [hc]; exact hnw)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  have r2 := uniswapV3Pool_block_15005 (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [uniswapV3Pool_block_15005_stack, uniswapV3Pool_block_14985_taken_stack,
    hc, u256_add_comm (UInt256.ofNat 1), u256_land_comm (UInt256.ofNat 65535)] at r2
  obtain ⟨ar, kr, Cr, rr, hhr, hor, _⟩ := oracleTransformX (v := v) (last := last)
    (time := a.time) (tick := a.tick) r2 hh hm hp hl hb ht hk hfit.2.2.2.1
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
  refine ⟨ar, kr, Cr, ?_, hhr, hor⟩
  simpa only [oracleWriteTransformedWords, oracleWriteCardinality_setTime, oracleWriteIndex_setTime,
    oracleWriteIndex, oracleSearchLeft,
    List.cons_append, List.nil_append] using rr

theorem oracleWriteTransformX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p free ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (last : OracleObservation)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14985⟩
      (oracleWriteCardinalityWords a p ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hn : (oracleWriteCardinality a).toNat ≠ 0)
    (hh : HeapMemory mem aw free) (hm : ObservationMemory mem p last)
    (hp : 96 ≤ p.toNat) (hl : p.toNat + 128 ≤ free.toNat)
    (hb : free.toNat + 256 ≤ 2 ^ 200) (hov : R.length + 27 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨15020⟩
      (oracleWriteTransformedWords a p (free + ⟨128⟩) ++ ret :: R)
      (oracleTransformMem mem free last a.time a.tick a.liquidity) aw' rdata σ k' C' ∧
      HeapMemory (oracleTransformMem mem free last a.time a.tick a.liquidity) aw' (free + ⟨256⟩) ∧
      ObservationMemory (oracleTransformMem mem free last a.time a.tick a.liquidity)
        (free + ⟨128⟩) (oracleTransformed last a.time a.tick a.liquidity) := by
  exact oracleWriteTransformRawX (v := v) (timeRaw := a.time) a last rd hfit
    (u256LandMaskCleanOfToNat (bits := 32) _ _ (by decide) hfit.2.1) hn hh hm hp hl hb hov

end Benchmarks.UniswapV3.Pool
