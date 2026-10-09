import Benchmarks.Morpho.MorphoBlue.ArithmeticRoutines
import Benchmarks.Morpho.MorphoBlue.NarrowingSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: checked uint128 arithmetic on canonical operands.
theorem uint128_add_fits_word (a b : UInt256) (ha : a.toNat < 2 ^ 128) (hb : b.toNat < 2 ^ 128) :
    a.toNat + b.toNat < UInt256.size := by
  change a.toNat + b.toNat < 2 ^ 256
  omega

theorem evalCheckedUint128AddOk {cfg : Config} {frame : Frame} {evm : EVM.State}
    {ex ey : Expr} {x y : UInt256}
    (hx : evalExpr? cfg frame evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm ey = .ok (.int (Int.ofNat y.toNat)))
    (hfit : x.toNat + y.toNat < 2 ^ 128) :
    evalExpr? cfg frame evm (.inRange (.uint ⟨128, by decide⟩) (.binary .add ex ey)) =
      .ok (.int (Int.ofNat (x + y).toNat)) := by
  have hw : (x + y).toNat = x.toNat + y.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (show x.toNat + y.toNat < UInt256.size by
      change x.toNat + y.toNat < 2 ^ 256; omega)]
  simp only [evalExpr?, hx, hy, bind, EvalResult.bind, evalBinaryOp?, hw, Int.ofNat_eq_natCast,
    Int.natCast_add]
  rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)]
  rfl

theorem evalCheckedUint128AddReverts {cfg : Config} {frame : Frame} {evm : EVM.State}
    {ex ey : Expr} {x y : UInt256}
    (hx : evalExpr? cfg frame evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm ey = .ok (.int (Int.ofNat y.toNat)))
    (hover : 2 ^ 128 ≤ x.toNat + y.toNat) :
    evalExpr? cfg frame evm (.inRange (.uint ⟨128, by decide⟩) (.binary .add ex ey)) = .revert := by
  simp only [evalExpr?, hx, hy, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast]
  rw [if_pos (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)]

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {a b ret : UInt256} {R : List UInt256}

theorem morphoCheckedAdd128Ok (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (ha : a.toNat < 2 ^ 128) (hb : b.toNat < 2 ^ 128)
    (hfit : a.toNat + b.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12664) (a :: b :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret ((a + b) :: R) mem aw rdata σ k' C' := by
  have hma : UInt256.land a uint128Mask = a := halfWord_low_clean a ha
  have hmb : UInt256.land b uint128Mask = b := halfWord_low_clean b hb
  have hw : (a + b).toNat = a.toNat + b.toNat :=
    addWord_toNat a b (uint128_add_fits_word a b ha hb)
  have rd1 := morphoBlocks.morpho_block_12664_fallthrough (immWords := wordsOf (immStore v))
    hstack (by change UInt256.gt (UInt256.land a uint128Mask + UInt256.land b uint128Mask) uint128Mask = _
               rw [hma, hmb]; apply ugt_zero; rw [hw]; change a.toNat + b.toNat ≤ 2 ^ 128 - 1; omega) h
  have rd2 := morphoBlocks.morpho_block_12699 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hvalid rd1
  simp only [morphoBlocks.morpho_block_12699_stack,
    show UInt256.ofNat 340282366920938463463374607431768211455 = uint128Mask from rfl,
    hma, hmb] at rd2
  exact ⟨_, _, rd2⟩

theorem morphoCheckedAdd128Reverts (hstack : R.length + 6 ≤ 1024)
    (ha : a.toNat < 2 ^ 128) (hb : b.toNat < 2 ^ 128)
    (hover : 2 ^ 128 ≤ a.toNat + b.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12664) (a :: b :: ret :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hma : UInt256.land a uint128Mask = a := halfWord_low_clean a ha
  have hmb : UInt256.land b uint128Mask = b := halfWord_low_clean b hb
  have hw : (a + b).toNat = a.toNat + b.toNat :=
    addWord_toNat a b (uint128_add_fits_word a b ha hb)
  have hc : UInt256.gt (a + b) uint128Mask = ⟨1⟩ :=
    ugt_one (by rw [hw]; change 2 ^ 128 - 1 < a.toNat + b.toNat; omega)
  have rd1 := morphoBlocks.morpho_block_12664_taken (immWords := wordsOf (immStore v))
    hstack (by change UInt256.gt (UInt256.land a uint128Mask + UInt256.land b uint128Mask) uint128Mask ≠ _
               rw [hma, hmb, hc]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_3277 (immWords := wordsOf (immStore v))
    (by simp only [morphoBlocks.morpho_block_12664_taken_stack, List.length_cons]; omega) rd1

end Routines
end Benchmarks.Morpho.MorphoBlue
