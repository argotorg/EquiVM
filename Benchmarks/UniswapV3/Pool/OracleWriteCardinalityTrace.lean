import Benchmarks.UniswapV3.Pool.OracleWriteReadMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleWriteGrows_setTime (a : OracleWriteArgs) (time : UInt256) :
    oracleWriteGrows {a with time := time} = oracleWriteGrows a := rfl

theorem oracleWriteCardinality_setTime (a : OracleWriteArgs) (time : UInt256) :
    oracleWriteCardinality {a with time := time} = oracleWriteCardinality a := rfl

theorem oracleWriteIndex_setTime (a : OracleWriteArgs) (time : UInt256) :
    oracleWriteIndex {a with time := time} = oracleWriteIndex a := rfl

theorem wordEq_decide (a b : UInt256) :
    UInt256.eq a b = (decide (a = b)).toUInt256 := by
  by_cases h : a = b
  · rw [h, uInt256_eq_self, decide_eq_true rfl]
    rfl
  · rw [decide_eq_false h]
    apply uInt256_eq_zero_of_ne
    exact fun he ↦ h (uInt256_eq_one_eq he)

theorem oracleWriteGrowsRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p timeRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14935⟩
      (oracleWriteReadWords {a with time := timeRaw} p ++ R) mem aw rdata σ k C)
    (hfit : a.Fits) (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14968⟩
      ((oracleWriteGrows a).toUInt256 :: oracleWriteReadWords {a with time := timeRaw} p ++ R) mem aw rdata σ k' C' := by
  have hc : UInt256.land (UInt256.ofNat 65535) a.cardinality = a.cardinality := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide) hfit.2.2.2.2.1
  have hn : UInt256.land (UInt256.ofNat 65535) a.cardinalityNext = a.cardinalityNext := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide) hfit.2.2.2.2.2
  have hi : UInt256.land (UInt256.ofNat 65535) a.index = a.index := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide) hfit.1
  simp only [oracleWriteReadWords, List.cons_append, List.nil_append] at rd ⊢
  by_cases hg : a.cardinality.toNat < a.cardinalityNext.toNat
  · have hgt : UInt256.gt a.cardinalityNext a.cardinality = UInt256.ofNat 1 := ugt_one hg
    have r1 := uniswapV3Pool_block_14935_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hn, hc, hgt]; rfl) rd
    have r2 := uniswapV3Pool_block_14953 (immWords := wordsOf (immStore v)) (by evm_ov) r1
    refine ⟨k + 12 + 10, C + 41 + 29, ?_⟩
    simpa only [uniswapV3Pool_block_14953_stack, uniswapV3Pool_block_14935_fallthrough_stack,
      hi, u256_land_comm (UInt256.ofNat 65535), wordEq_decide,
      oracleWriteGrows, decide_eq_true hg, Bool.true_and, oracleWriteCardinalityPred] using r2
  · have hgt : UInt256.gt a.cardinalityNext a.cardinality = UInt256.ofNat 0 :=
      ugt_zero (Nat.le_of_not_gt hg)
    have r1 := uniswapV3Pool_block_14935_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hn, hc, hgt]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨k + 12, C + 41, ?_⟩
    simpa only [uniswapV3Pool_block_14935_taken_stack, hn, hc, hgt,
      oracleWriteGrows, decide_eq_false hg, Bool.false_and] using r1

theorem oracleWriteGrowsX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14935⟩
      (oracleWriteReadWords a p ++ R) mem aw rdata σ k C)
    (hfit : a.Fits) (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14968⟩
      ((oracleWriteGrows a).toUInt256 :: oracleWriteReadWords a p ++ R) mem aw rdata σ k' C' := by
  exact oracleWriteGrowsRawX (v := v) (timeRaw := a.time) a rd hfit hov

def oracleWriteCardinalityWords (a : OracleWriteArgs) (p : UInt256) : List UInt256 :=
  [p, oracleWriteCardinality a, ⟨0⟩, a.cardinalityNext, a.cardinality, a.liquidity,
    EVM.wordOfInt a.tick, a.time, a.index, ⟨8⟩]

theorem oracleWriteCardinalityChoiceRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p timeRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14968⟩
      ((oracleWriteGrows a).toUInt256 :: oracleWriteReadWords {a with time := timeRaw} p ++ R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14985⟩
      (oracleWriteCardinalityWords {a with time := timeRaw} p ++ R) mem aw rdata σ k' C' := by
  simp only [oracleWriteReadWords, List.cons_append, List.nil_append] at rd
  cases hg : oracleWriteGrows a
  · rw [hg] at rd
    have r1 := uniswapV3Pool_block_14968_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r2 := uniswapV3Pool_block_14981 (immWords := wordsOf (immStore v)) (by evm_ov) r1
    refine ⟨k + 4 + 4, C + 17 + 9, ?_⟩
    simpa only [uniswapV3Pool_block_14981_stack, uniswapV3Pool_block_14968_taken_stack,
      oracleWriteCardinalityWords, oracleWriteCardinality, oracleWriteGrows_setTime,
      hg, Bool.false_eq_true, if_false,
      List.cons_append, List.nil_append] using r2
  · rw [hg] at rd
    have r1 := uniswapV3Pool_block_14968_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide) rd
    have r2 := uniswapV3Pool_block_14974 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    refine ⟨k + 4 + 5, C + 17 + 19, ?_⟩
    simpa only [uniswapV3Pool_block_14974_stack, uniswapV3Pool_block_14968_fallthrough_stack,
      oracleWriteCardinalityWords, oracleWriteCardinality, oracleWriteGrows_setTime, hg, if_true,
      List.cons_append, List.nil_append] using r2

theorem oracleWriteCardinalityChoiceX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14968⟩
      ((oracleWriteGrows a).toUInt256 :: oracleWriteReadWords a p ++ R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14985⟩
      (oracleWriteCardinalityWords a p ++ R) mem aw rdata σ k' C' := by
  exact oracleWriteCardinalityChoiceRawX (v := v) (timeRaw := a.time) a rd hov

theorem oracleWriteCardinalityRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p timeRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14935⟩
      (oracleWriteReadWords {a with time := timeRaw} p ++ R) mem aw rdata σ k C)
    (hfit : a.Fits) (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14985⟩
      (oracleWriteCardinalityWords {a with time := timeRaw} p ++ R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, rr⟩ := oracleWriteGrowsRawX (v := v) a rd hfit hov
  exact oracleWriteCardinalityChoiceRawX (v := v) a rr hov

theorem oracleWriteCardinalityX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14935⟩
      (oracleWriteReadWords a p ++ R) mem aw rdata σ k C)
    (hfit : a.Fits) (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14985⟩
      (oracleWriteCardinalityWords a p ++ R) mem aw rdata σ k' C' := by
  exact oracleWriteCardinalityRawX (v := v) (timeRaw := a.time) a rd hfit hov

end Benchmarks.UniswapV3.Pool
