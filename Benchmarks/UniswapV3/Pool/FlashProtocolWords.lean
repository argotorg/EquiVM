import Benchmarks.UniswapV3.Pool.ProtocolFeeStorage
import Benchmarks.UniswapV3.Pool.SourceWordArithmetic
import Benchmarks.UniswapV3.Pool.Slot0Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: the natural value of a word right shift below the word width.
theorem wordShiftRight_toNat (w bits : UInt256) (h : bits.toNat < 256) :
    (UInt256.shiftRight w bits).toNat = w.toNat / 2 ^ bits.toNat := by
  unfold UInt256.shiftRight UInt256.toNat
  rw [if_neg (by exact Nat.not_le.mpr h)]
  change (w.val >>> bits.val).val = w.val.val / 2 ^ bits.val.val
  rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]

def poolProtocolDivisor (second : Bool) (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.ofNat 15)
    (if second then UInt256.shiftRight
      (UInt256.div (solcSlotWordAt ⟨0⟩ σ ee) (UInt256.shiftLeft (UInt256.ofNat 1) ⟨232⟩)) ⟨4⟩
    else UInt256.div (solcSlotWordAt ⟨0⟩ σ ee) (UInt256.shiftLeft (UInt256.ofNat 1) ⟨232⟩))

theorem poolProtocolDivisor_lt (second : Bool) (σ : AccountMap) (ee : ExecutionEnv) :
    (poolProtocolDivisor second σ ee).toNat < 16 := by
  unfold poolProtocolDivisor
  rw [u256_land_comm]
  exact u256LandMaskToNatLtOfToNat (bits := 4) _ _ (by decide)

theorem poolProtocolDivisor_clean (second : Bool) (σ : AccountMap) (ee : ExecutionEnv) :
    UInt256.land (UInt256.ofNat 255) (poolProtocolDivisor second σ ee) =
      poolProtocolDivisor second σ ee := by
  rw [u256_land_comm]
  exact u256LandMaskCleanOfToNat (bits := 8) _ _ (by decide)
    (lt_trans (poolProtocolDivisor_lt second σ ee) (by decide))

theorem poolProtocolDivisor_toNat (second : Bool) (σ : AccountMap) (ee : ExecutionEnv) :
    (poolProtocolDivisor second σ ee).toNat =
      if second then (slot0FieldWord 29 1 σ ee).toNat / 16
      else (slot0FieldWord 29 1 σ ee).toNat % 16 := by
  have hshift : UInt256.shiftLeft (UInt256.ofNat 1) (⟨232⟩ : UInt256) =
      UInt256.ofNat (256 ^ 29) := by native_decide
  have hfield : (slot0FieldWord 29 1 σ ee).toNat =
      (solcSlotWordAt ⟨0⟩ σ ee).toNat / 256 ^ 29 % 256 := by
    rw [slot0FieldWord, uland_toNat, udiv_toNat]
    rw [ulit_toNat' _ (by decide), ulit_toNat' _ (by decide)]
    change Nat.land _ (2 ^ 8 - 1) = _
    rw [nat_land_mask_eq_mod]
    rfl
  rw [hfield]
  cases second
  · simp only [poolProtocolDivisor, Bool.false_eq_true, ↓reduceIte, hshift]
    rw [u256_land_comm, uland_toNat, udiv_toNat,
      ulit_toNat' _ (by decide), ulit_toNat' _ (by decide)]
    change Nat.land _ (2 ^ 4 - 1) = _
    rw [nat_land_mask_eq_mod]
    omega
  · simp only [poolProtocolDivisor, ↓reduceIte, hshift]
    rw [u256_land_comm, uland_toNat, wordShiftRight_toNat _ _ (by decide), udiv_toNat,
      ulit_toNat' _ (by decide), ulit_toNat' _ (by decide)]
    change Nat.land (_ / 2 ^ 4) (2 ^ 4 - 1) = _
    rw [nat_land_mask_eq_mod]
    omega

def poolProtocolFees (paid divisor : UInt256) : UInt256 :=
  if divisor = ⟨0⟩ then ⟨0⟩ else UInt256.div paid divisor

-- LIBRARY CANDIDATE: a uint128 cast after addition agrees with the masked word sum.
theorem uint128_add_cast (a b : UInt256) :
    normalizeInt (.uint ⟨128, by decide⟩) (Int.ofNat a.toNat + Int.ofNat b.toNat) =
      Int.ofNat (uint128Word (a + b)).toNat := by
  rw [normalizeUIntInt_mask ⟨128, by decide⟩ _ (UInt256.ofNat (2 ^ 128 - 1)) (by decide)]
  rw [wordOfInt_add, wordOfInt_ofNat_toNat, wordOfInt_ofNat_toNat, u256_land_comm]
  rfl

theorem evalExpr_uint128AddCast {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg frame evm
      (.cast (.binary .add lhs (.cast rhs (.elem (.int (.uint ⟨128, by decide⟩)))))
        (.elem (.int (.uint ⟨128, by decide⟩)))) =
      .ok (.int (Int.ofNat (uint128Word (a + b)).toNat)) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, EvalResult.ofOption, castValue?, evalBinaryOp?,
    normalizeInt_add_right, uint128_add_cast]

end Benchmarks.UniswapV3.Pool
