import Benchmarks.Morpho.MorphoBlue.Uint128Arithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: checked subtraction at uint128 width.
theorem evalCheckedUint128SubOk {cfg : Config} {frame : Frame} {evm : EVM.State}
    {ex ey : Expr} {x y : UInt256}
    (hx : evalExpr? cfg frame evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm ey = .ok (.int (Int.ofNat y.toNat)))
    (hb : x.toNat < 2 ^ 128) (hfit : y.toNat ≤ x.toNat) :
    evalExpr? cfg frame evm (.inRange (.uint ⟨128, by decide⟩) (.binary .sub ex ey)) =
      .ok (.int (Int.ofNat (UInt256.sub x y).toNat)) := by
  rw [evalExpr?, subSourceOk hx hy hfit]
  simp only [bind, EvalResult.bind, usub_toNat hfit]
  rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq, Int.ofNat_eq_natCast]; omega)]
  rfl

theorem evalCheckedUint128SubReverts {cfg : Config} {frame : Frame} {evm : EVM.State}
    {ex ey : Expr} {x y : UInt256}
    (hx : evalExpr? cfg frame evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm ey = .ok (.int (Int.ofNat y.toNat)))
    (hunder : x.toNat < y.toNat) :
    evalExpr? cfg frame evm (.inRange (.uint ⟨128, by decide⟩) (.binary .sub ex ey)) = .revert := by
  simp only [evalExpr?, hx, hy, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast]
  rw [if_pos (by simp only [Bool.or_eq_true, decide_eq_true_eq, Int.ofNat_eq_natCast]; omega)]

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {a b ret : UInt256} {R : List UInt256}

theorem morphoCheckedSub128Ok (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (ha : a.toNat < 2 ^ 128) (hb : b.toNat < 2 ^ 128) (hfit : b.toNat ≤ a.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12846) (a :: b :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.sub a b :: R) mem aw rdata σ k' C' := by
  have hma : UInt256.land uint128Mask a = a := by rw [u256_land_comm]; exact halfWord_low_clean a ha
  have hmb : UInt256.land uint128Mask b = b := by rw [u256_land_comm]; exact halfWord_low_clean b hb
  have rd1 := morphoBlocks.morpho_block_12846_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (by
      change UInt256.gt (UInt256.sub (UInt256.land uint128Mask a) (UInt256.land uint128Mask b)) uint128Mask = _
      rw [hma, hmb]
      apply ugt_zero
      rw [usub_toNat hfit]
      change a.toNat - b.toNat ≤ 2 ^ 128 - 1
      omega) h
  have rd2 := morphoBlocks.morpho_block_12879 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hvalid rd1
  simp only [morphoBlocks.morpho_block_12846_fallthrough_stack,
    show UInt256.ofNat 340282366920938463463374607431768211455 = uint128Mask from rfl,
    hma, hmb] at rd2
  exact ⟨_, _, rd2⟩

theorem morphoCheckedSub128Reverts (hstack : R.length + 6 ≤ 1024)
    (ha : a.toNat < 2 ^ 128) (hb : b.toNat < 2 ^ 128) (hunder : a.toNat < b.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12846) (a :: b :: ret :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hma : UInt256.land uint128Mask a = a := by rw [u256_land_comm]; exact halfWord_low_clean a ha
  have hmb : UInt256.land uint128Mask b = b := by rw [u256_land_comm]; exact halfWord_low_clean b hb
  have hc : UInt256.gt (UInt256.sub a b) uint128Mask = ⟨1⟩ := by
    apply ugt_one
    rw [usub_toNat_underflow hunder]
    change 2 ^ 128 - 1 < UInt256.size + a.toNat - b.toNat
    norm_num [UInt256.size] at hb ⊢
    omega
  have rd1 := morphoBlocks.morpho_block_12846_taken (immWords := wordsOf (immStore v))
    (by omega) (by
      change UInt256.gt (UInt256.sub (UInt256.land uint128Mask a) (UInt256.land uint128Mask b)) uint128Mask ≠ _
      rw [hma, hmb, hc]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_3277 (immWords := wordsOf (immStore v))
    (by simp only [morphoBlocks.morpho_block_12846_taken_stack, List.length_cons]; omega) rd1

end Routines
end Benchmarks.Morpho.MorphoBlue
