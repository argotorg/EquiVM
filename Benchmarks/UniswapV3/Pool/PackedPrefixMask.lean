import Benchmarks.UniswapV3.Pool.PackedPrefixStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a masked write extends a previously written low prefix.
theorem packedPrefixWord_masked (old low next clearMask field : UInt256)
    (offset width value : Nat) (hb : offset + width ≤ 256)
    (hlow : low.toNat < 2 ^ offset)
    (hmask : clearMask.toNat = (2 ^ offset - 1) ||| (2 ^ 256 - 2 ^ (offset + width)))
    (hfield : field.toNat = value * 2 ^ offset) (hvalue : value < 2 ^ width)
    (hnext : next.toNat = low.toNat + 2 ^ offset * value) :
    UInt256.lor (UInt256.land (packedPrefixWord old low offset) clearMask) field =
      packedPrefixWord old next (offset + width) := by
  have hnextbound : next.toNat < 2 ^ (offset + width) := by
    rw [hnext, Nat.pow_add]
    calc
      low.toNat + 2 ^ offset * value < 2 ^ offset + 2 ^ offset * value :=
        Nat.add_lt_add_right hlow _
      _ = 2 ^ offset * (value + 1) := by ring
      _ ≤ 2 ^ offset * 2 ^ width := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hvalue)
  apply u256_inj
  rw [packedMaskedWord_toNat _ clearMask field offset width value hb hmask hfield hvalue,
    packedPrefixWord_mod old low offset (by omega) hlow,
    packedPrefixWord_div old low offset (offset + width) (by omega) hb hlow,
    packedPrefixWord_toNat old next (offset + width) hb hnextbound, hnext]
  ac_rfl

end Benchmarks.UniswapV3.Pool
