import Benchmarks.CompoundIII.Comet.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: packed unsigned fields with byte offsets and widths.
def packedUint (w : UInt256) (offset size : Nat) : UInt256 :=
  UInt256.land (UInt256.div w (UInt256.ofNat (256 ^ offset)))
    (UInt256.ofNat (256 ^ size - 1))

theorem packedUint_lt (w : UInt256) (offset : Nat) {size : Nat} (hsize : size ≤ 32) :
    (packedUint w offset size).toNat < 2 ^ (8 * size) := by
  apply u256LandMaskToNatLtOfToNat
  have hp : 2 ^ (8 * size) ≤ UInt256.size := by
    change 2 ^ (8 * size) ≤ 2 ^ 256
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0 < 2 ^ (8 * size) := by positivity
  have heq : 256 ^ size = 2 ^ (8 * size) := by rw [Nat.pow_mul]
  rw [heq, UInt256.toNat_ofNat_of_lt (by omega)]

theorem packedUint_load (evm : EVM.State) (slot : UInt256)
    (offset : Fin 32) (size : Fin 33) (width : ABI.BitWidth)
    {hbound : offset.val + size.val - 1 < 32}
    (hwidth : width.val = 8 * size.val) :
    storageLocLoad evm
      { slot := slot, offset := offset, size := size, hbound := hbound, type := .int (.uint width) } =
      .int (packedUint (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) offset.val size.val).toNat :=
  storageLocLoad_uint_offset evm slot offset size width hwidth (by omega) (by omega)

theorem divBytePow_eq_shift (w : UInt256) (offset : Fin 32) :
    UInt256.div w (UInt256.ofNat (256 ^ offset.val)) =
      UInt256.shiftRight w (UInt256.ofNat (8 * offset.val)) := by
  have hbits : 8 * offset.val < 256 := by omega
  have hbitsSize : 8 * offset.val < UInt256.size := lt_trans hbits (by decide)
  have hpow : 256 ^ offset.val < UInt256.size := by
    change (2 ^ 8) ^ offset.val < 2 ^ 256
    rw [← Nat.pow_mul]
    exact Nat.pow_lt_pow_right (by decide) hbits
  apply u256_inj
  rw [udiv_toNat, UInt256.toNat_ofNat_of_lt hpow]
  unfold UInt256.shiftRight
  rw [if_neg (by change ¬ (UInt256.ofNat (8 * offset.val)).toNat ≥ 256
                 rw [UInt256.toNat_ofNat_of_lt hbitsSize]; omega)]
  simp only [UInt256.toNat, Fin.shiftRight_val]
  change w.toNat / 256 ^ offset.val = w.toNat >>> (UInt256.ofNat (8 * offset.val)).toNat
  rw [UInt256.toNat_ofNat_of_lt hbitsSize, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

end Benchmarks.CompoundIII.Comet
