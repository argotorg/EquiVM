import Benchmarks.UniswapV3.Pool.Calldata

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- GENERALIZES Reasoning.ABIViews.calldataPayloadStart_toNat to any offset word.
theorem bytesWindow_start_toNat {off : UInt256} (hoff : off.toNat ≤ solcMaxU64) :
    ((UInt256.ofNat 4 + off) + UInt256.ofNat 32).toNat = 4 + off.toNat + 32 := by
  have haddr : (UInt256.ofNat 4 + off).toNat = 4 + off.toNat := add4_word_toNat off hoff
  rw [uadd_word_ofNat_toNat _ 32 (by
    rw [haddr]; change _ < 2 ^ 256
    change off.toNat ≤ 2 ^ 64 - 1 at hoff; omega), haddr]

theorem bytesWindow_start_word {off : UInt256} (hoff : off.toNat ≤ solcMaxU64) :
    UInt256.ofNat 32 + (UInt256.ofNat 4 + off) = UInt256.ofNat (4 + off.toNat + 32) := by
  rw [u256_add_comm]
  exact (u256_ofNat_toNat _).symm.trans (congrArg UInt256.ofNat (bytesWindow_start_toNat hoff))

-- LIBRARY CANDIDATE: a bytes payload endpoint with bounded offset and length words.
theorem bytesWindow_end_toNat {off len : UInt256}
    (hoff : off.toNat ≤ solcMaxU64) (hlen : len.toNat ≤ solcMaxU64) :
    ((UInt256.ofNat 32 + (UInt256.ofNat 4 + off)) +
      UInt256.mul len (UInt256.ofNat 1)).toNat = 4 + off.toNat + 32 + len.toNat := by
  have hmul : (UInt256.mul len (UInt256.ofNat 1)).toNat = len.toNat := by
    rw [u256_mul_toNat]
    change (len.toNat * 1) % UInt256.size = _
    rw [Nat.mul_one, Nat.mod_eq_of_lt (show len.toNat < UInt256.size from len.val.isLt)]
  have hstart : (UInt256.ofNat 32 + (UInt256.ofNat 4 + off)).toNat = 4 + off.toNat + 32 := by
    rw [u256_add_comm]; exact bytesWindow_start_toNat hoff
  rw [uadd_toNat, hstart, hmul, Nat.mod_eq_of_lt (by
    change off.toNat ≤ 2 ^ 64 - 1 at hoff
    change len.toNat ≤ 2 ^ 64 - 1 at hlen
    change _ < 2 ^ 256; omega)]

end Benchmarks.UniswapV3.Pool
