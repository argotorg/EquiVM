import Benchmarks.UniswapV3.Pool.OracleInterpolationModel
import Benchmarks.UniswapV3.Pool.SignedDivision
import Benchmarks.UniswapV3.Pool.SourceWordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def oracleInterpolationTickRaw (before after : OracleObservation) (target : UInt256) : UInt256 :=
  EVM.wordOfInt before.tickCumulative + UInt256.mul
    (UInt256.sdiv
      (UInt256.signextend (UInt256.ofNat 6)
        (UInt256.sub (EVM.wordOfInt after.tickCumulative) (EVM.wordOfInt before.tickCumulative)))
      (oracleDelta after.timestamp before.timestamp)) (oracleDelta target before.timestamp)

def oracleInterpolationSecondsRaw (before after : OracleObservation) (target : UInt256) : UInt256 :=
  before.secondsPerLiquidity + UInt256.div
    (UInt256.mul
      (UInt256.land (UInt256.sub after.secondsPerLiquidity before.secondsPerLiquidity)
        (UInt256.ofNat (2 ^ 160 - 1))) (oracleDelta target before.timestamp))
    (oracleDelta after.timestamp before.timestamp)

theorem oracleInterpolatedTick_word (before after : OracleObservation) (target : UInt256) :
    EVM.wordOfInt (oracleInterpolatedTick before after target) =
      UInt256.signextend (UInt256.ofNat 6) (oracleInterpolationTickRaw before after target) := by
  have hbounds := normalizeSint_bounds ⟨56, by decide⟩
    (after.tickCumulative - before.tickCumulative)
  change -(2 ^ 55 : Int) ≤ _ ∧ _ < (2 ^ 55 : Int) at hbounds
  have hd := oracleDelta_lt after.timestamp before.timestamp
  have hdiv := wordOfInt_sdiv_nat
    (normalizeInt (.sint ⟨56, by decide⟩) (after.tickCumulative - before.tickCumulative))
    (oracleDelta after.timestamp before.timestamp) (by omega) (by omega) (by omega)
  have hsign (i : Int) := signextend_wordOfInt ⟨56, by decide⟩ (UInt256.ofNat 6) i
    (by decide) (by decide)
  unfold oracleInterpolatedTick oracleInterpolationTickRaw
  rw [normalizeInt_add_right, ← hsign, wordOfInt_add, wordOfInt_mul,
    wordOfInt_ofNat_toNat, ← hdiv, ← hsign, wordOfInt_sub]
  rfl

theorem oracleInterpolatedSeconds_word (before after : OracleObservation) (target : UInt256) :
    EVM.wordOfInt (oracleInterpolatedSeconds before after target) =
      UInt256.land (oracleInterpolationSecondsRaw before after target)
        (UInt256.ofNat (2 ^ 160 - 1)) := by
  have hmask (i : Int) := normalizeUIntInt_mask ⟨160, by decide⟩ i
    (UInt256.ofNat (2 ^ 160 - 1)) (by decide)
  have hdiv (a b : UInt256) : Int.ofNat a.toNat / Int.ofNat b.toNat =
      Int.ofNat (UInt256.div a b).toNat := by rw [udiv_toNat]; rfl
  unfold oracleInterpolatedSeconds oracleInterpolationSecondsRaw
  rw [normalizeInt_add_right, normalizeUInt256_int, normalizeUInt256_int, hmask]
  simp only [wordOfInt_mul, wordOfInt_ofNat_toNat]
  rw [hdiv, hmask, wordOfInt_ofNat_toNat, wordOfInt_add,
    wordOfInt_ofNat_toNat, wordOfInt_ofNat_toNat]
  rw [wordOfInt_sub, wordOfInt_ofNat_toNat, wordOfInt_ofNat_toNat]
  rfl

end Benchmarks.UniswapV3.Pool
