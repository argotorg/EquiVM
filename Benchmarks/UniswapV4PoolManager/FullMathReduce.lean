import Benchmarks.UniswapV4PoolManager.FullMathPrelude
import Benchmarks.UniswapV4PoolManager.WordWrappingSource
import Benchmarks.UniswapV4PoolManager.FullMathGeneralWords
import Benchmarks.UniswapV4PoolManager.WordLowBit

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def fullMathReduceFrame (f : Frame) (a b d : UInt256) : Frame :=
  let f1 := wordLocal f "remainder" ⟨0⟩
  let f2 := wordLocal f1 "remainder" (fullMathRemainder a b d)
  let f3 := wordLocal f2 "prod1" (fullMathReducedHigh a b d)
  let f4 := wordLocal f3 "prod0" (fullMathReducedLow a b d)
  let f5 := wordLocal f4 "twos" (fullMathTwos d)
  let f6 := wordLocal f5 "denominator" (fullMathOdd d)
  let f7 := wordLocal f6 "prod0" (UInt256.div (fullMathReducedLow a b d) (fullMathTwos d))
  let f8 := wordLocal f7 "twos" (fullMathTwosInverse d)
  wordLocal f8 "prod0" (fullMathWide a b d)

theorem fullMathReduce {f : Frame} {evm : EVM.State} {a b d : UInt256}
    (hdnz : d ≠ ⟨0⟩)
    (ha : f.locals.get? "a" = some (.int (Int.ofNat a.toNat)))
    (hb : f.locals.get? "b" = some (.int (Int.ofNat b.toNat)))
    (hd : f.locals.get? "denominator" = some (.int (Int.ofNat d.toNat)))
    (hp0 : f.locals.get? "prod0" = some (.int (Int.ofNat (fullMathLow a b).toNat)))
    (hp1 : f.locals.get? "prod1" = some (.int (Int.ofNat (fullMathHigh a b).toNat))) :
    ExecBlock config f evm ((fullMathFunction.body.drop 7).take 9)
      (.ok (fullMathReduceFrame f a b d) evm) := by
  have htwos : fullMathTwos d ≠ ⟨0⟩ := wordLowBit_ne d hdnz
  let f1 := wordLocal f "remainder" ⟨0⟩
  let f2 := wordLocal f1 "remainder" (fullMathRemainder a b d)
  let f3 := wordLocal f2 "prod1" (fullMathReducedHigh a b d)
  let f4 := wordLocal f3 "prod0" (fullMathReducedLow a b d)
  let f5 := wordLocal f4 "twos" (fullMathTwos d)
  let f6 := wordLocal f5 "denominator" (fullMathOdd d)
  let f7 := wordLocal f6 "prod0" (UInt256.div (fullMathReducedLow a b d) (fullMathTwos d))
  let f8 := wordLocal f7 "twos" (fullMathTwosInverse d)
  have h7 : ExecStmt config f evm fullMathFunction.body[7]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have hd1 : f1.locals.get? "denominator" = some (.int (Int.ofNat d.toNat)) := by
    simp only [f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hd]
  have h8 : ExecStmt config f1 evm fullMathFunction.body[8]! (.ok f2 evm) :=
    ExecStmt.assign (evalWordMulMod (a := a) (b := b) (c := d)
      (evalLocalValue (by simp only [f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ha]))
      (evalLocalValue (by simp only [f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hb]))
      (evalLocalValue hd1) hdnz) (assignLocalValue (store_get_self _ _ _))
  have hp02 : f2.locals.get? "prod0" = some (.int (Int.ofNat (fullMathLow a b).toNat)) := by
    simp only [f2, f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hp0]
  have hp12 : f2.locals.get? "prod1" = some (.int (Int.ofNat (fullMathHigh a b).toNat)) := by
    simp only [f2, f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hp1]
  have h9 : ExecStmt config f2 evm fullMathFunction.body[9]! (.ok f3 evm) :=
    ExecStmt.assign (evalWordSub (evalLocalValue hp12)
      (evalBoolWord (evalWordGt (wordLocal_eval (w := fullMathRemainder a b d))
        (evalLocalValue hp02)))) (assignLocalValue hp12)
  have hp03 : f3.locals.get? "prod0" = some (.int (Int.ofNat (fullMathLow a b).toNat)) := by
    simp only [f3, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hp02]
  have h10 : ExecStmt config f3 evm fullMathFunction.body[10]! (.ok f4 evm) :=
    ExecStmt.assign (evalWordSub (evalLocalValue hp03)
      (evalLocalValue (show f3.locals.get? "remainder" = some (.int (Int.ofNat (fullMathRemainder a b d).toNat)) by
        simp only [f3, f2, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]))) (assignLocalValue hp03)
  have hd4 : f4.locals.get? "denominator" = some (.int (Int.ofNat d.toNat)) := by
    simp only [f4, f3, f2, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hd1]
  have he11 := evalWordAnd (evalWordSub (x := ⟨0⟩)
    (show evalExpr? config f4 evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by simp only [evalExpr?, pure]; rfl)
    (evalLocalValue hd4)) (evalLocalValue hd4)
  have h11 : ExecStmt config f4 evm fullMathFunction.body[11]! (.ok f5 evm) := ExecStmt.letDecl he11
  have hd5 : f5.locals.get? "denominator" = some (.int (Int.ofNat d.toNat)) := by
    simp only [f5, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hd4]
  have he12 := evalWordDiv (evalLocalValue (cfg := config) (f := f5) (evm := evm) hd5)
    (wordLocal_eval (w := fullMathTwos d)) htwos
  have h12 : ExecStmt config f5 evm fullMathFunction.body[12]! (.ok f6 evm) :=
    ExecStmt.assign he12 (assignLocalValue hd5)
  have hp06 : f6.locals.get? "prod0" = some (.int (Int.ofNat (fullMathReducedLow a b d).toNat)) := by
    simp only [f6, f5, f4, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]
  have ht6 : f6.locals.get? "twos" = some (.int (Int.ofNat (fullMathTwos d).toNat)) := by
    simp only [f6, f5, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]
  have h13 : ExecStmt config f6 evm fullMathFunction.body[13]! (.ok f7 evm) :=
    ExecStmt.assign (evalWordDiv (evalLocalValue hp06) (evalLocalValue ht6) htwos)
      (assignLocalValue hp06)
  have ht7 : f7.locals.get? "twos" = some (.int (Int.ofNat (fullMathTwos d).toNat)) := by
    simp only [f7, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ht6]
  have he14 := evalWordAdd
    (evalWordDiv (evalWordSub (x := ⟨0⟩)
      (show evalExpr? config f7 evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by simp only [evalExpr?, pure]; rfl)
      (evalLocalValue ht7)) (evalLocalValue ht7) htwos)
    (show evalExpr? config f7 evm (.intLit 1) = .ok (.int (Int.ofNat (⟨1⟩ : UInt256).toNat)) by simp only [evalExpr?, pure]; rfl)
  have h14 : ExecStmt config f7 evm fullMathFunction.body[14]! (.ok f8 evm) :=
    ExecStmt.assign he14 (assignLocalValue ht7)
  have hp08 : f8.locals.get? "prod0" =
      some (.int (Int.ofNat (UInt256.div (fullMathReducedLow a b d) (fullMathTwos d)).toNat)) := by
    simp only [f8, f7, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]
  have hp18 : f8.locals.get? "prod1" = some (.int (Int.ofNat (fullMathReducedHigh a b d).toNat)) := by
    simp only [f8, f7, f6, f5, f4, f3, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]
  have h15 : ExecStmt config f8 evm fullMathFunction.body[15]! (.ok (fullMathReduceFrame f a b d) evm) :=
    ExecStmt.assign (evalWordOr (evalLocalValue hp08)
      (evalWordMul (evalLocalValue hp18) (wordLocal_eval (w := fullMathTwosInverse d)))) (assignLocalValue hp08)
  exact ExecBlock.consNormal h7 (ExecBlock.consNormal h8 (ExecBlock.consNormal h9
    (ExecBlock.consNormal h10 (ExecBlock.consNormal h11 (ExecBlock.consNormal h12
    (ExecBlock.consNormal h13 (ExecBlock.consNormal h14 (execBlock_singleton h15))))))))

end Benchmarks.UniswapV4PoolManager
