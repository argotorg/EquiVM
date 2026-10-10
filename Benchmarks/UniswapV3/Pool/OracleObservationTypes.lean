import Benchmarks.UniswapV3.Pool.OracleObserveSingleSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure OracleObservation.Valid (obs : OracleObservation) : Prop where
  timestamp : obs.timestamp.toNat < 2 ^ 32
  tick : -(2 ^ 55 : Int) ≤ obs.tickCumulative ∧ obs.tickCumulative < 2 ^ 55
  seconds : obs.secondsPerLiquidity.toNat < 2 ^ 160

theorem oracleStoredValid (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    (oracleStoredObservation index σ I).Valid := by
  refine ⟨oracleStoredTimestamp_lt index σ I, ?_, ?_⟩
  · dsimp only [oracleStoredObservation, observationTickValue]
    exact normalizeSint_bounds ⟨56, by decide⟩ _
  · exact u256LandMaskToNatLtOfToNat (bits := 160) _ _ (by decide)

theorem oracleZeroValid : oracleZeroObservation.Valid := ⟨by decide, by decide, by decide⟩

theorem oracleTransformedValid (last : OracleObservation) (time : UInt256) (tick : Int)
    (liquidity : UInt256) (ht : time.toNat < 2 ^ 32) :
    (oracleTransformed last time tick liquidity).Valid :=
  ⟨ht, normalizeSint_bounds ⟨56, by decide⟩ _, u256LandMaskToNatLtOfToNat _ _ (by decide)⟩

theorem OracleSearchRun.valid {time target cardinality left right : UInt256}
    {σ : AccountMap} {I : ExecutionEnv} {before after : OracleObservation}
    (hrun : OracleSearchRun time target cardinality σ I left right before after) :
    before.Valid ∧ after.Valid := by
  induction hrun with
  | found => exact ⟨oracleStoredValid _ _ _, oracleStoredValid _ _ _⟩
  | uninitialized _ _ ih => exact ih
  | advance _ _ _ ih => exact ih

theorem OracleSurroundingRun.valid {time target index liquidity cardinality : UInt256}
    {tick : Int} {σ : AccountMap} {I : ExecutionEnv} {before after : OracleObservation}
    (hrun : OracleSurroundingRun time target tick index liquidity cardinality σ I before after)
    (ht : target.toNat < 2 ^ 32) : before.Valid ∧ after.Valid := by
  cases hrun with
  | latest =>
      refine ⟨oracleStoredValid _ _ _, ?_⟩
      unfold oracleSurroundingLatestAfter
      split
      · exact oracleZeroValid
      · exact oracleTransformedValid _ _ _ _ ht
  | search _ _ _ hs => exact hs.valid

theorem OracleObservation.Valid.cleanTick {obs : OracleObservation} (h : obs.Valid) :
    UInt256.signextend (UInt256.ofNat 6) (EVM.wordOfInt obs.tickCumulative) =
      EVM.wordOfInt obs.tickCumulative := by
  rw [signextend_wordOfInt ⟨56, by decide⟩ _ _ (by decide) (by decide),
    normalizeSint_eq_self ⟨56, by decide⟩ _ h.tick.1 h.tick.2]

theorem OracleObservation.Valid.cleanSeconds {obs : OracleObservation} (h : obs.Valid) :
    UInt256.land obs.secondsPerLiquidity (UInt256.ofNat (2 ^ 160 - 1)) =
      obs.secondsPerLiquidity := u256LandMaskCleanOfToNat _ _ (by decide) h.seconds

end Benchmarks.UniswapV3.Pool
