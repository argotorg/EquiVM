import Benchmarks.UniswapV3.Pool.BitmapPositionWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: signed normalization is idempotent at every ABI width.
theorem normalizeSint_idem (width : ABI.BitWidth) (i : Int) :
    normalizeInt (.sint width) (normalizeInt (.sint width) i) =
      normalizeInt (.sint width) i :=
  normalizeSint_eq_self width _ (normalizeSint_bounds width i).1
    (normalizeSint_bounds width i).2

theorem bitmapWordPos_normalize (tick : Int) :
    bitmapWordPos (normalizeInt (.sint ⟨24, by decide⟩) tick) = bitmapWordPos tick := by
  simp only [bitmapWordPos, normalizeSint_idem]

theorem bitmapBitPos_normalize (tick : Int) :
    bitmapBitPos (normalizeInt (.sint ⟨24, by decide⟩) tick) = bitmapBitPos tick :=
  normalizeUInt_sint_of_le ⟨8, by decide⟩ ⟨24, by decide⟩ tick (by decide)

theorem bitmapPositionBitRaw_normalize (tick : Int) :
    bitmapPositionBitRaw (normalizeInt (.sint ⟨24, by decide⟩) tick) =
      bitmapPositionBitRaw tick := by
  simp only [bitmapPositionBitRaw, normalizeSint_idem]

theorem bitmapWordPos_clean (tick : Int) :
    UInt256.signextend (UInt256.ofNat 1) (EVM.wordOfInt (bitmapWordPos tick)) =
      EVM.wordOfInt (bitmapWordPos tick) := by
  rw [signextend_wordOfInt ⟨16, by decide⟩ _ _ (by decide) (by decide),
    normalizeSint_eq_self ⟨16, by decide⟩ _
      (bitmapWordPos_bounds tick).1 (bitmapWordPos_bounds tick).2]

theorem bitmapPositionShift (tick : Int) :
    UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.land (bitmapPositionBitRaw tick) (UInt256.ofNat 255)) =
      UInt256.ofNat (2 ^ (bitmapBitPos tick).toNat) := by
  rw [u256_land_comm, bitmapPositionBitClean]
  have hb := bitmapBitPos_bounds tick
  have hw : (EVM.wordOfInt (bitmapBitPos tick)).toNat = (bitmapBitPos tick).toNat := by
    rw [wordOfInt_nonneg _ hb.1]
    exact ulit_toNat' _ (by change _ < 2 ^ 256; omega)
  apply u256_inj
  rw [wordShiftLeft_toNat _ _ (by rw [hw]; omega), hw]
  change (1 * 2 ^ (bitmapBitPos tick).toNat) % UInt256.size =
    (2 ^ (bitmapBitPos tick).toNat) % UInt256.size
  rw [Nat.one_mul]

end Benchmarks.UniswapV3.Pool
