import Benchmarks.Safe.CalldataDecodeArithmetic
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: the compiler's divide-and-multiply rounding of a byte length.
theorem roundedCalldataLength (len : Nat) (hb : len + 31 < UInt256.size) :
    UInt256.mul (UInt256.div (UInt256.ofNat 31 + UInt256.ofNat len) (UInt256.ofNat 32))
      (UInt256.ofNat 32) = UInt256.ofNat (ABI.paddedSize len) := by
  have hpad : ABI.paddedSize len ≤ len + 31 := by unfold ABI.paddedSize; omega
  apply u256_inj
  rw [wordOfNatAdd 31 len (by omega), u256_mul_toNat, udiv_toNat,
    ulit_toNat' (31 + len) (by omega), ulit_toNat' (ABI.paddedSize len) (by omega)]
  change ((31 + len) / 32 * 32) % UInt256.size = ABI.paddedSize len
  have he : (31 + len) / 32 * 32 = ABI.paddedSize len := by
    simp only [ABI.paddedSize, Nat.add_comm, Nat.mul_comm]
  rw [he, Nat.mod_eq_of_lt (by omega)]

-- LIBRARY CANDIDATE: the equivalent mask-based rounding of a byte length.
theorem roundedCalldataLengthMask (len : Nat) (hb : len + 31 < UInt256.size) :
    UInt256.land (UInt256.ofNat len + UInt256.ofNat 31)
      (UInt256.lnot (UInt256.ofNat 31)) = UInt256.ofNat (ABI.paddedSize len) := by
  rw [u256_land_comm]
  apply u256_inj
  change (returnReserveSize len).toNat = _
  rw [returnReserveSize_toNat hb, ulit_toNat' _ (by unfold ABI.paddedSize; omega)]
  unfold ABI.paddedSize
  omega

end Benchmarks.Safe
