import Benchmarks.UniswapV3.Pool.OracleObservationStore
import Benchmarks.UniswapV3.Pool.OracleObservationTypes

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem packedFieldValue_zero32 (word : UInt256) :
    packedFieldValue word 0 32 = UInt256.land word (UInt256.ofNat 4294967295) := by
  apply u256_inj
  rw [packedFieldValue_toNat _ _ _ (by decide) (by decide)]
  simp only [Nat.pow_zero, Nat.mul_one]
  symm
  rw [uland_toNat]
  exact nat_land_mask_eq_mod word.toNat 32

theorem packedFieldValue_bool248 (flag : Bool) :
    packedFieldValue flag.toUInt256 248 8 =
      UInt256.mul (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248))
        (UInt256.isZero (UInt256.isZero flag.toUInt256)) := by
  cases flag <;> decide

def oracleObservationPackedWord (obs : OracleObservation) (old : UInt256) : UInt256 :=
  let time := UInt256.lor (UInt256.land old (UInt256.lnot (UInt256.ofNat 4294967295)))
    (UInt256.land obs.timestamp (UInt256.ofNat 4294967295))
  let tick := UInt256.lor (UInt256.land time
    (UInt256.lnot (UInt256.ofNat 309485009821345064429813760)))
    (UInt256.mul (UInt256.ofNat 4294967296)
      (UInt256.land (UInt256.ofNat 72057594037927935) (EVM.wordOfInt obs.tickCumulative)))
  let seconds := UInt256.lor (UInt256.land tick
    (UInt256.ofNat 115339776388732929035197660848497720713218148788040715071188274165450943758335))
    (UInt256.mul (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 88))
      (UInt256.land obs.secondsPerLiquidity
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))
  UInt256.lor (UInt256.land seconds
    (UInt256.ofNat 452312848583266388373324160190187140051835877600158453279131187530910662655))
    (UInt256.mul (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248))
      (UInt256.isZero (UInt256.isZero obs.initialized.toUInt256)))

theorem oracleObservationPackedWord_eq (obs : OracleObservation) (old : UInt256) :
    oracleObservationPackedWord obs old = oracleObservationWord obs old := by
  have hm0 : packedFieldMask 0 32 = UInt256.lnot (UInt256.ofNat 4294967295) := by native_decide
  have hm1 : packedFieldMask 32 56 =
      UInt256.lnot (UInt256.ofNat 309485009821345064429813760) := by native_decide
  have hm2 : packedFieldMask 88 160 =
      UInt256.ofNat 115339776388732929035197660848497720713218148788040715071188274165450943758335 :=
    by native_decide
  have hm3 : packedFieldMask 248 8 =
      UInt256.ofNat 452312848583266388373324160190187140051835877600158453279131187530910662655 :=
    by native_decide
  have hv1 : packedFieldValue (EVM.wordOfInt obs.tickCumulative) 32 56 =
      UInt256.mul (UInt256.ofNat 4294967296)
        (UInt256.land (UInt256.ofNat 72057594037927935) (EVM.wordOfInt obs.tickCumulative)) := by
    dsimp only [packedFieldValue]
    rw [u256_mul_comm, u256_land_comm]
    rfl
  have hv2 : packedFieldValue obs.secondsPerLiquidity 88 160 =
      UInt256.mul (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 88))
        (UInt256.land obs.secondsPerLiquidity
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) := by
    dsimp only [packedFieldValue]
    rw [u256_mul_comm]
    rfl
  simp only [oracleObservationWord, packedFieldUpdate, hm0, hm1, hm2, hm3,
    packedFieldValue_zero32, hv1, hv2, packedFieldValue_bool248]
  rfl

end Benchmarks.UniswapV3.Pool
