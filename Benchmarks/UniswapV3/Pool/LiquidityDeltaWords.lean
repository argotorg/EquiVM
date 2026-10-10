import Benchmarks.UniswapV3.Pool.LiquidityDeltaModel
import Benchmarks.UniswapV3.Pool.SignedComparison

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000
open scoped Fin.CommRing

-- LIBRARY CANDIDATE: subtraction of a negated EVM word is addition in the word ring.
theorem word_sub_neg (a b : UInt256) : UInt256.sub a (UInt256.sub ⟨0⟩ b) = a + b := by
  apply u256_inj
  change (a.val - (0 - b.val)).val = (a.val + b.val).val
  rw [zero_sub, sub_neg_eq_add]

-- LIBRARY CANDIDATE: addition may consume unsigned and signed residues of the same width.
theorem normalizeUInt_add_uint_sint (width : ABI.BitWidth) (i j : Int) :
    normalizeInt (.uint width)
      (normalizeInt (.uint width) i + normalizeInt (.sint width) j) =
      normalizeInt (.uint width) (i + j) := by
  change (normalizeInt (.uint width) i + normalizeInt (.sint width) j) %
    Int.ofNat (EVM.twoPow width.val) = (i + j) % Int.ofNat (EVM.twoPow width.val)
  have hi := normalizeInt_residue (.uint width) i
  have hj := normalizeInt_residue (.sint width) j
  simp only [IntType.bitWidth] at hi hj
  rw [Int.add_emod, hi, hj, ← Int.add_emod]

theorem liquidityDeltaRawResult (xw yw : UInt256) (x y : Int)
    (hx : normalizeInt (.uint ⟨128, by decide⟩) (Int.ofNat xw.toNat) = x)
    (hy : normalizeInt (.sint ⟨128, by decide⟩) (Int.ofNat yw.toNat) = y) :
    Int.ofNat (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) (xw + yw)).toNat =
      liquidityDeltaResult x y := by
  have hr : normalizeInt (.uint ⟨128, by decide⟩) (Int.ofNat (xw + yw).toNat) =
      normalizeInt (.uint ⟨128, by decide⟩) (Int.ofNat xw.toNat + Int.ofNat yw.toNat) := by
    simpa only [wordOfInt_add, wordOfInt_ofNat_toNat] using
      normalizeInt_wordOfInt (.uint ⟨128, by decide⟩)
        (Int.ofNat xw.toNat + Int.ofNat yw.toNat)
  rw [u256_land_comm, ← normalizeUIntWord_mask ⟨128, by decide⟩ _ _ (by decide), hr]
  unfold liquidityDeltaResult
  rw [← hx, ← hy, normalizeUInt_add_uint_sint]

theorem liquidityDeltaRawOutput (xw yw : UInt256) (x y : Int)
    (hx : normalizeInt (.uint ⟨128, by decide⟩) (Int.ofNat xw.toNat) = x)
    (hy : normalizeInt (.sint ⟨128, by decide⟩) (Int.ofNat yw.toNat) = y) :
    UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) (xw + yw) =
      EVM.wordOfInt (liquidityDeltaResult x y) := by
  rw [← liquidityDeltaRawResult xw yw x y hx hy, wordOfInt_ofNat_toNat]

theorem liquidityDeltaRawGuard (xw yw : UInt256) (x y : Int)
    (hx : normalizeInt (.uint ⟨128, by decide⟩) (Int.ofNat xw.toNat) = x)
    (hy : normalizeInt (.sint ⟨128, by decide⟩) (Int.ofNat yw.toNat) = y) :
    UInt256.lt (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) (xw + yw))
      (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) xw) =
      if liquidityDeltaResult x y < x then ⟨1⟩ else ⟨0⟩ := by
  have hr := liquidityDeltaRawResult xw yw x y hx hy
  have hxx : Int.ofNat (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) xw).toNat = x := by
    rw [u256_land_comm, ← normalizeUIntWord_mask ⟨128, by decide⟩ _ _ (by decide), hx]
  simp only [Int.ofNat_eq_natCast] at hr hxx
  by_cases h : liquidityDeltaResult x y < x
  · rw [if_pos h]
    apply ult_one
    omega
  · rw [if_neg h]
    apply ult_zero
    omega

theorem liquidityDeltaRawSign (yw : UInt256) (y : Int)
    (hy : normalizeInt (.sint ⟨128, by decide⟩) (Int.ofNat yw.toNat) = y) :
    UInt256.slt (UInt256.signextend (UInt256.ofNat 15) yw) (UInt256.ofNat 0) =
      if y < 0 then ⟨1⟩ else ⟨0⟩ := by
  rw [signextend_normalizeSint ⟨128, by decide⟩ _ yw (by decide) (by decide), hy]
  have hb := normalizeSint_bounds ⟨128, by decide⟩ (Int.ofNat yw.toNat)
  rw [hy] at hb
  change -(2 ^ 127 : Int) ≤ y ∧ y < 2 ^ 127 at hb
  change UInt256.slt (EVM.wordOfInt y) (EVM.wordOfInt 0) = _
  exact slt_wordOfInt y 0 (by omega) (by omega) (by decide) (by decide)

end Benchmarks.UniswapV3.Pool
