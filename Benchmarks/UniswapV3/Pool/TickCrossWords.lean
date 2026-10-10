import Benchmarks.UniswapV3.Pool.TickCrossStorage
import Benchmarks.UniswapV3.Pool.TickHistoryWords
import Benchmarks.UniswapV3.Pool.SnapshotArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def tickCrossLiquidityRawWord (liquidity old : UInt256) : UInt256 :=
  let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
    (UInt256.ofNat 1)
  UInt256.lor
    (UInt256.land old (UInt256.ofNat
      115792089237210883131902427821989989825586314233321668944057106954252856590335))
    (UInt256.mul (UInt256.ofNat 72057594037927936)
      (UInt256.land (UInt256.sub liquidity
        (UInt256.land mask (UInt256.div old (UInt256.ofNat 72057594037927936)))) mask))

def tickCrossCumulativeRawWord (cumulative old : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot (UInt256.ofNat 72057594037927935)))
    (UInt256.land (UInt256.ofNat 72057594037927935)
      (UInt256.signextend (UInt256.ofNat 6)
        (UInt256.sub cumulative (UInt256.signextend (UInt256.ofNat 6) old))))

def tickCrossSecondsRawWord (time old : UInt256) : UInt256 :=
  let shift := UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216)
  let mask := UInt256.ofNat 4294967295
  UInt256.lor
    (UInt256.land old (UInt256.lnot (UInt256.shiftLeft mask (UInt256.ofNat 216))))
    (UInt256.mul (UInt256.land mask (UInt256.sub time (UInt256.land mask
      (UInt256.div old shift)))) shift)

theorem tickCrossLiquidityWord (a : TickCrossArgs) (old : UInt256) :
    tickCrossHistoryWord a .secondsPerLiquidity old =
      tickCrossLiquidityRawWord a.secondsPerLiquidity old := by
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 160 - 1) := by native_decide
  unfold tickCrossHistoryWord tickCrossHistoryValue TickCrossField.type TickCrossField.global
    TickCrossField.old TickCrossField.field
  rw [wordOfInt_normalizeUint ⟨160, by decide⟩ _ (UInt256.ofNat (2 ^ 160 - 1)) (by decide),
    wordOfInt_sub, wordOfInt_ofNat_toNat, wordOfInt_ofNat_toNat,
    tickHistorySecondsPerLiquidityWord, hm, maskTwice]
  rw [tickCrossLiquidityRawWord, hm]
  rw [u256_lor_comm, u256_land_comm _ old, u256_mul_comm]
  congr 4
  exact u256_land_comm _ _

theorem tickCrossCumulativeWord (a : TickCrossArgs) (old : UInt256) :
    tickCrossHistoryWord a .cumulative old =
      tickCrossCumulativeRawWord (EVM.wordOfInt a.cumulative) old := by
  unfold tickCrossHistoryWord tickCrossHistoryValue TickCrossField.type TickCrossField.global
    TickCrossField.old TickCrossField.field
  rw [← signextend_wordOfInt ⟨56, by decide⟩ (UInt256.ofNat 6) _ (by decide) (by decide),
    wordOfInt_sub, ← signextend_normalizeSint ⟨56, by decide⟩
      (UInt256.ofNat 6) old (by decide) (by decide),
    tickHistoryCumulativeWord, tickCrossCumulativeRawWord]
  rw [u256_lor_comm, u256_land_comm _ old, u256_land_comm _ (UInt256.ofNat 72057594037927935)]

theorem tickCrossSecondsWord (a : TickCrossArgs) (old : UInt256) :
    tickCrossHistoryWord a .seconds old = tickCrossSecondsRawWord a.time old := by
  have hs : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216) =
      UInt256.ofNat (2 ^ 216) := by native_decide
  unfold tickCrossHistoryWord tickCrossHistoryValue TickCrossField.type TickCrossField.global
    TickCrossField.old TickCrossField.field
  rw [wordOfInt_normalizeUint ⟨32, by decide⟩ _ (UInt256.ofNat 4294967295) (by decide),
    wordOfInt_sub, wordOfInt_ofNat_toNat, wordOfInt_ofNat_toNat, tickHistorySecondsWord]
  change UInt256.lor (UInt256.mul (UInt256.land (UInt256.land _ _) _)
    (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216))) _ = _
  rw [maskTwice, tickCrossSecondsRawWord, hs, u256_lor_comm, u256_land_comm _ old]
  congr 2
  rw [u256_land_comm _ (UInt256.ofNat 4294967295)]
  congr 2
  exact u256_land_comm _ _

end Benchmarks.UniswapV3.Pool
