import Benchmarks.UniswapV3.Pool.TickHistoryStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem tickHistorySecondsPerLiquidityWord (old value : UInt256) :
    tickHistoryUpdate .secondsPerLiquidity old value =
      UInt256.lor (UInt256.mul (UInt256.land value
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1))) (UInt256.ofNat 72057594037927936))
        (UInt256.land
          (UInt256.ofNat 115792089237210883131902427821989989825586314233321668944057106954252856590335)
          old) := by
  have hm : packedFieldMask 56 160 =
      UInt256.ofNat 115792089237210883131902427821989989825586314233321668944057106954252856590335 :=
    by native_decide
  have hf : UInt256.ofNat (2 ^ 160 - 1) =
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1) :=
    by native_decide
  change UInt256.lor (UInt256.land old (packedFieldMask 56 160))
    (UInt256.mul (UInt256.land value (UInt256.ofNat (2 ^ 160 - 1)))
      (UInt256.ofNat (2 ^ 56))) = _
  rw [hm, hf, u256_lor_comm, u256_land_comm old]
  rfl

theorem tickHistoryCumulativeWord (old value : UInt256) :
    tickHistoryUpdate .cumulative old value =
      UInt256.lor (UInt256.land value (UInt256.ofNat 72057594037927935))
        (UInt256.land (UInt256.lnot (UInt256.ofNat 72057594037927935)) old) := by
  have hm : packedFieldMask 0 56 = UInt256.lnot (UInt256.ofNat 72057594037927935) :=
    by native_decide
  change UInt256.lor (UInt256.land old (packedFieldMask 0 56))
    (UInt256.mul (UInt256.land value (UInt256.ofNat 72057594037927935)) ⟨1⟩) = _
  rw [hm, u256_lor_comm, u256_land_comm old]
  congr 1
  apply u256_inj
  rw [u256_mul_toNat]
  change (_ * 1) % UInt256.size = _
  rw [Nat.mul_one]
  exact Nat.mod_eq_of_lt (UInt256.land value (UInt256.ofNat 72057594037927935)).val.isLt

theorem tickHistorySecondsWord (old value : UInt256) :
    tickHistoryUpdate .seconds old value =
      UInt256.lor (UInt256.mul (UInt256.land value (UInt256.ofNat 4294967295))
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216)))
        (UInt256.land (UInt256.lnot
          (UInt256.shiftLeft (UInt256.ofNat 4294967295) (UInt256.ofNat 216))) old) := by
  have hm : packedFieldMask 216 32 =
      UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 4294967295) (UInt256.ofNat 216)) :=
    by native_decide
  have hf : UInt256.ofNat (2 ^ 216) =
      UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216) := by native_decide
  change UInt256.lor (UInt256.land old (packedFieldMask 216 32))
    (UInt256.mul (UInt256.land value (UInt256.ofNat 4294967295)) (UInt256.ofNat (2 ^ 216))) = _
  rw [hm, hf, u256_lor_comm, u256_land_comm old]

theorem tickHistoryInitializedWord (old : UInt256) :
    tickHistoryUpdate .initialized old ⟨1⟩ =
      UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248))
        (UInt256.land
          (UInt256.ofNat 452312848583266388373324160190187140051835877600158453279131187530910662655)
          old) := by
  have hm : packedFieldMask 248 8 =
      UInt256.ofNat 452312848583266388373324160190187140051835877600158453279131187530910662655 :=
    by native_decide
  have hf : packedFieldValue ⟨1⟩ 248 8 =
      UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248) := by native_decide
  change UInt256.lor (UInt256.land old (packedFieldMask 248 8)) (packedFieldValue ⟨1⟩ 248 8) = _
  rw [hm, hf, u256_lor_comm, u256_land_comm old]

end Benchmarks.UniswapV3.Pool
