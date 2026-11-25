import Benchmarks.Midnight.Word128BitSource
import Benchmarks.Midnight.BitmapCountArithmetic
import Benchmarks.Midnight.PositionViewSourceBase

variable {fork : Ethereum.Fork}

/-! Once-for-all source proofs of the bitmap setter and count helper. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

abbrev bitmapSetFunction : FunctionDecl := contract.functions[16]!
abbrev bitmapCountFunction : FunctionDecl := contract.functions[17]!

theorem bitmapSetSource {cfg : Config} {frame : Frame} {evm : EVM.State}
    {bitmap bit : UInt256}
    (hb : frame.locals.get? "bitmap" = some (.int bitmap.toNat))
    (hi : frame.locals.get? "bit" = some (.int bit.toNat)) (hbit : bit.toNat < 256) :
    ExecFuncBody fork cfg frame evm bitmapSetFunction.body
      (.returned frame evm (some [.int (bitmapSet bitmap bit).toNat])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have he := evalCast128 (evalWordBitOr (cfg := cfg) (frame := frame) (evm := evm)
    (lhs := .var "bitmap") (a := bitmap)
    (by simp only [evalExpr?, hb, EvalResult.ofOption])
    (evalOneShiftLeft (expr := .var "bit") (bit := bit)
      (by simp only [evalExpr?, hi, EvalResult.ofOption]) hbit))
  simp only [packedUInt128Int] at he
  simp only [evalExprs?, he, bind, pure, EvalResult.bind, bitmapSet]

theorem bitmapCountSource {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x : UInt256} (hx : x.toNat < 2^128)
    (hget : frame.locals.get? "x" = some (.int x.toNat)) :
    ∃ frame', ExecFuncBody fork cfg frame evm bitmapCountFunction.body
      (.returned frame' evm (some [.int (bitmapCount x).toNat])) := by
  let x1 := bitmapCount1 x
  let x2 := bitmapCount2 x1
  let x4 := bitmapCount4 x2
  let f1 := wordLocal frame "x" x1
  let f2 := wordLocal f1 "x" x2
  let f4 := wordLocal f2 "x" x4
  have hx1 : x1.toNat < 2^128 := bitmapCount1_lt hx
  have hx2 : x2.toNat < 2^128 := bitmapCount2_lt x1
  have hx4 : x4.toNat < 2^128 := bitmapCount4_lt x2
  have he1 : evalExpr? cfg frame evm (.cast (.binary .sub (.var "x")
      (.binary (.bitAnd packedUInt128Int)
        (.binary (.shr packedUInt128Int) (.var "x") (.intLit 1))
        (.intLit 113427455640312821154458202477256070485)))
      (.elem (.int packedUInt128Int))) = .ok (.int x1.toNat) := by
    have hs : (UInt256.shiftRight x (UInt256.ofNat 1)).toNat < 2^128 := by
      rw [shiftRight_toNat _ _ (by decide)]
      exact (Nat.div_le_self _ _).trans_lt hx
    have he := evalCastSub128 (cfg := cfg) (frame := frame) (evm := evm)
      (lhs := .var "x") (rhs := .binary (.bitAnd packedUInt128Int)
        (.binary (.shr packedUInt128Int) (.var "x") (.intLit 1))
        (.intLit 113427455640312821154458202477256070485))
      (a := x) (by simp only [evalExpr?, hget, EvalResult.ofOption])
      (evalUint128BitAnd (b := countMask1)
        (evalUint128ShiftRight (shift := UInt256.ofNat 1)
          (by simp only [evalExpr?, hget, EvalResult.ofOption]) (by simp only [evalExpr?, pure]; rfl) hx (by decide))
        (by simp only [evalExpr?, pure]; rfl) hs (by decide)) (bitmapCount1_sub_le x)
    change _ = EvalResult.ok (Value.int (low128 x1).toNat) at he
    rw [show low128 x1 = x1 from uint128Mask_clean hx1] at he
    exact he
  have he2 : evalExpr? cfg f1 evm (.cast (.binary .add
      (.binary (.bitAnd packedUInt128Int) (.var "x")
        (.intLit 68056473384187692692674921486353642291))
      (.binary (.bitAnd packedUInt128Int)
        (.binary (.shr packedUInt128Int) (.var "x") (.intLit 2))
        (.intLit 68056473384187692692674921486353642291)))
      (.elem (.int packedUInt128Int))) = .ok (.int x2.toNat) := by
    have hs : (UInt256.shiftRight x1 (UInt256.ofNat 2)).toNat < 2^128 := by
      rw [shiftRight_toNat _ _ (by decide)]
      exact (Nat.div_le_self _ _).trans_lt hx1
    have he := evalWrappingAdd128 (cfg := cfg) (frame := f1) (evm := evm)
      (lhs := .binary (.bitAnd packedUInt128Int) (.var "x")
        (.intLit 68056473384187692692674921486353642291))
      (rhs := .binary (.bitAnd packedUInt128Int)
        (.binary (.shr packedUInt128Int) (.var "x") (.intLit 2))
        (.intLit 68056473384187692692674921486353642291))
      (evalUint128BitAnd (a := x1) (b := countMask2)
        (by simp only [evalExpr?, f1, wordLocal_get, EvalResult.ofOption]) (by simp only [evalExpr?, pure]; rfl) hx1 (by decide))
      (evalUint128BitAnd (b := countMask2)
        (evalUint128ShiftRight (shift := UInt256.ofNat 2)
          (by simp only [evalExpr?, f1, wordLocal_get, EvalResult.ofOption]) (by simp only [evalExpr?, pure]; rfl) hx1 (by decide))
        (by simp only [evalExpr?, pure]; rfl) hs (by decide))
    change _ = EvalResult.ok (Value.int (low128 x2).toNat) at he
    rw [show low128 x2 = x2 from uint128Mask_clean hx2] at he
    exact he
  have he4 : evalExpr? cfg f2 evm (.binary (.bitAnd packedUInt128Int)
      (.cast (.binary .add (.var "x")
        (.binary (.shr packedUInt128Int) (.var "x") (.intLit 4)))
        (.elem (.int packedUInt128Int)))
      (.intLit 20016609818878733144904388672456953615)) = .ok (.int x4.toNat) := by
    exact evalUint128BitAnd
      (evalWrappingAdd128 (a := x2)
        (by simp only [evalExpr?, f2, wordLocal_get, EvalResult.ofOption])
        (evalUint128ShiftRight (shift := UInt256.ofNat 4)
          (by simp only [evalExpr?, f2, wordLocal_get, EvalResult.ofOption]) (by simp only [evalExpr?, pure]; rfl) hx2 (by decide)))
      (b := countMask4) (by simp only [evalExpr?, pure]; rfl) (low128_lt _) (by decide)
  have her : evalExpr? cfg f4 evm (.binary (.shr packedUInt128Int)
      (.cast (.binary .mul (.var "x") (.intLit 1334440654591915542993625911497130241))
        (.elem (.int packedUInt128Int))) (.intLit 120)) =
      .ok (.int (bitmapCount x).toNat) := by
    exact evalUint128ShiftRight (shift := UInt256.ofNat 120)
      (evalWrappingMul128 (a := x4) (b := countMultiplier)
        (by simp only [evalExpr?, f4, wordLocal_get, EvalResult.ofOption]) (by simp only [evalExpr?, pure]; rfl))
      (by simp only [evalExpr?, pure]; rfl) (low128_lt _) (by decide)
  refine ⟨f4, ExecFuncBody.execBlockRet ?_⟩
  exact ExecBlock.consNormal (execLocalAssign hget he1)
    (ExecBlock.consNormal (execLocalAssign (wordLocal_get _ _ _) he2)
      (ExecBlock.consNormal (execLocalAssign (wordLocal_get _ _ _) he4)
        (ExecBlock.consReturn (ExecStmt.return (by
          change evalExprs? cfg f4 evm [.binary (.shr packedUInt128Int)
            (.cast (.binary .mul (.var "x") (.intLit 1334440654591915542993625911497130241))
              (.elem (.int packedUInt128Int))) (.intLit 120)] = _
          simp only [evalExprs?, her, bind, pure, EvalResult.bind])))))

end Benchmarks.Midnight
