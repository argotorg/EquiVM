import Benchmarks.UniswapV4PoolManager.FullMathWords
import Benchmarks.UniswapV4PoolManager.WordLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev fullMathFunction : FunctionDecl := contract.functions[91]!
theorem fullMath_lookup : lookupCallable? contract "FullMath_mulDiv" =
    some fullMathFunction.toCallable := rfl

def fullMathPreludeFrame (f : Frame) (a b : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal (wordLocal (wordLocal f "result" ⟨0⟩)
    "prod0" (fullMathLow a b)) "prod1" ⟨0⟩) "mm" (fullMathMM a b)) "prod1" (fullMathHigh a b)

theorem fullMathPrelude {f : Frame} {evm : EVM.State} {a b : UInt256}
    (ha : f.locals.get? "a" = some (.int (Int.ofNat a.toNat)))
    (hb : f.locals.get? "b" = some (.int (Int.ofNat b.toNat))) :
    ExecBlock config f evm (fullMathFunction.body.take 5) (.ok (fullMathPreludeFrame f a b) evm) := by
  let f1 := wordLocal f "result" ⟨0⟩
  let f2 := wordLocal f1 "prod0" (fullMathLow a b)
  let f3 := wordLocal f2 "prod1" ⟨0⟩
  let f4 := wordLocal f3 "mm" (fullMathMM a b)
  have h0 : ExecStmt config f evm fullMathFunction.body[0]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have h1 : ExecStmt config f1 evm fullMathFunction.body[1]! (.ok f2 evm) :=
    ExecStmt.letDecl (evalWordMul (x := a) (y := b)
      (evalLocalValue (by simp only [f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ha]))
      (evalLocalValue (by simp only [f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hb])))
  have h2 : ExecStmt config f2 evm fullMathFunction.body[2]! (.ok f3 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have h3 : ExecStmt config f3 evm fullMathFunction.body[3]! (.ok f4 evm) :=
    ExecStmt.letDecl (evalWordMulMod (a := a) (b := b) (c := fullMathMax)
      (evalLocalValue (by simp only [f3, f2, f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ha]))
      (evalLocalValue (by simp only [f3, f2, f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hb]))
      (by simp only [evalExpr?, pure]; rfl) fullMathMax_ne)
  have hmm : f4.locals.get? "mm" = some (.int (Int.ofNat (fullMathMM a b).toNat)) := store_get_self _ _ _
  have hp0 : f4.locals.get? "prod0" = some (.int (Int.ofNat (fullMathLow a b).toNat)) := by
    simp only [f4, f3, f2, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]
  have hp1 : f4.locals.get? "prod1" = some (.int 0) := by
    simp only [f4, f3, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]; rfl
  have he := evalWordSubSub (evalLocalValue (cfg := config) (f := f4) (evm := evm) hmm)
    (evalLocalValue hp0) (evalBoolWord (evalWordLt (evalLocalValue hmm) (evalLocalValue hp0)))
  have h4 : ExecStmt config f4 evm fullMathFunction.body[4]! (.ok (fullMathPreludeFrame f a b) evm) :=
    ExecStmt.assign he (assignLocalValue hp1)
  exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2
    (ExecBlock.consNormal h3 (execBlock_singleton h4))))

end Benchmarks.UniswapV4PoolManager
