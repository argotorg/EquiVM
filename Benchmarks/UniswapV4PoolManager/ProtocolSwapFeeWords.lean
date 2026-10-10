import Benchmarks.UniswapV4PoolManager.Slot0FeeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def protocolFeeZeroWord (fee : UInt256) : UInt256 := UInt256.land fee (UInt256.ofNat 4095)
def protocolFeeOneWord (fee : UInt256) : UInt256 := UInt256.shiftRight fee (UInt256.ofNat 12)

theorem protocolFeeZeroWord_bound (fee : UInt256) : (protocolFeeZeroWord fee).toNat < 2^12 := by
  rw [protocolFeeZeroWord, uland_toNat]
  exact lt_of_le_of_lt (nat_land_le_right _ _) (by decide)

theorem protocolFeeOneWord_bound {fee : UInt256} (hc : fee.toNat < 2^24) :
    (protocolFeeOneWord fee).toNat < 2^12 := by
  rw [protocolFeeOneWord, wordShiftRightNat _ (by decide)]
  omega

theorem protocolFeeZeroWord_packed (packed : UInt256) :
    protocolFeeZeroWord (slot0FeeField packed 184) =
      UInt256.land (UInt256.shiftRight packed (UInt256.ofNat 184)) (UInt256.ofNat 4095) := by
  apply u256_inj
  simp only [protocolFeeZeroWord, slot0FeeField, uland_toNat, Nat.and_assoc]
  rfl

theorem protocolFeeOneWord_packed (packed : UInt256) :
    protocolFeeOneWord (slot0FeeField packed 184) =
      UInt256.land (UInt256.shiftRight packed (UInt256.ofNat 196)) (UInt256.ofNat 4095) := by
  rw [protocolFeeOneWord, slot0FeeField, wordShiftRightAnd _ _ (by decide),
    wordShiftRightCompose _ (by decide : 184+12 < 256)]
  rfl

def protocolSwapFeeRaw (fee lpFee : UInt256) : UInt256 :=
  UInt256.sub (protocolFeeZeroWord fee + lpFee)
    (UInt256.div (UInt256.mul (protocolFeeZeroWord fee) lpFee) (UInt256.ofNat 1000000))
def protocolSwapFeeWord (fee lpFee : UInt256) : UInt256 :=
  UInt256.land (protocolSwapFeeRaw fee lpFee) (UInt256.ofNat 16777215)

theorem protocolSwapFee_add_bound (fee : UInt256) {lpFee : UInt256} (hl : lpFee.toNat < 2^24) :
    (protocolFeeZeroWord fee).toNat + lpFee.toNat < UInt256.size := by
  have hp := protocolFeeZeroWord_bound fee
  change _ < 2^256
  omega

theorem protocolSwapFee_mul_bound (fee : UInt256) {lpFee : UInt256} (hl : lpFee.toNat < 2^24) :
    (protocolFeeZeroWord fee).toNat * lpFee.toNat < UInt256.size := by
  have hb := Nat.mul_le_mul (Nat.le_of_lt (protocolFeeZeroWord_bound fee)) (Nat.le_of_lt hl)
  change _ < 2^256
  omega

theorem protocolSwapFeeRaw_nat (fee : UInt256) {lpFee : UInt256} (hl : lpFee.toNat < 2^24) :
    (protocolSwapFeeRaw fee lpFee).toNat =
      (protocolFeeZeroWord fee).toNat + lpFee.toNat - (protocolFeeZeroWord fee).toNat*lpFee.toNat/1000000 := by
  have hp := protocolFeeZeroWord_bound fee
  have hq : (protocolFeeZeroWord fee).toNat*lpFee.toNat/1000000 ≤ lpFee.toNat := by
    apply Nat.div_le_of_le_mul
    exact Nat.mul_le_mul_right _ (by omega)
  have hm : (UInt256.mul (protocolFeeZeroWord fee) lpFee).toNat =
      (protocolFeeZeroWord fee).toNat*lpFee.toNat := umul_toNat _ _ (protocolSwapFee_mul_bound fee hl)
  have ha : (protocolFeeZeroWord fee + lpFee).toNat = (protocolFeeZeroWord fee).toNat+lpFee.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (protocolSwapFee_add_bound fee hl)]
  rw [protocolSwapFeeRaw, usub_toNat (by rw [ha, udiv_toNat, hm]; change _/1000000 ≤ _; omega),
    ha, udiv_toNat, hm]
  rfl

theorem protocolSwapFeeRaw_bound (fee : UInt256) {lpFee : UInt256} (hl : lpFee.toNat < 2^24) :
    (protocolSwapFeeRaw fee lpFee).toNat < 2^24 := by
  rw [protocolSwapFeeRaw_nat fee hl]
  have hp := protocolFeeZeroWord_bound fee
  by_cases hb : lpFee.toNat ≤ 1000000
  · omega
  · have hq : (protocolFeeZeroWord fee).toNat ≤ (protocolFeeZeroWord fee).toNat*lpFee.toNat/1000000 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 1000000)).2
      exact Nat.mul_le_mul_left _ (by omega)
    omega

theorem protocolSwapFeeWord_eq_raw (fee : UInt256) {lpFee : UInt256} (hl : lpFee.toNat < 2^24) :
    protocolSwapFeeWord fee lpFee = protocolSwapFeeRaw fee lpFee :=
  u256LandMaskCleanOfToNat _ _ rfl (protocolSwapFeeRaw_bound fee hl)

theorem protocolSwapFeeWord_bound (fee lpFee : UInt256) : (protocolSwapFeeWord fee lpFee).toNat < 2^24 := by
  rw [protocolSwapFeeWord, uland_toNat]
  exact lt_of_le_of_lt (nat_land_le_right _ _) (by decide)

end Benchmarks.UniswapV4PoolManager
