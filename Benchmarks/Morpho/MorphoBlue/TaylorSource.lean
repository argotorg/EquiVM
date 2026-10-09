import Benchmarks.Morpho.MorphoBlue.MathSource
import Benchmarks.Morpho.MorphoBlue.MathValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: extend a source block with any statement preserving EVM state.
theorem advancePureBlock {cfg : Config} {evm : EVM.State} {start before after : Frame}
    {stmts rest : List Stmt} {stmt : Stmt}
    (pref : ABlock cfg evm start stmts before (stmt :: rest))
    (step : ExecStmt cfg before evm stmt (.ok after evm)) :
    ABlock cfg evm start stmts after rest :=
  ⟨fun tail ↦ pref.run (ExecBlock.consNormal step tail)⟩

abbrev taylorFunction : FunctionDecl := contract.functions[16]!

def taylorStart (x n : UInt256) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := ((∅ : Store).insert "n" (.int (Int.ofNat n.toNat))).insert "x" (.int (Int.ofNat x.toNat)) }

def taylorAfterFirst (x n : UInt256) (imms : Store) : Frame :=
  { taylorStart x n imms with locals :=
      (taylorStart x n imms).locals.insert "firstTerm" (.int (Int.ofNat (taylorTerm1 x n).toNat)) }

def taylorAfterSecond (x n : UInt256) (imms : Store) : Frame :=
  { taylorAfterFirst x n imms with locals :=
      (taylorAfterFirst x n imms).locals.insert "secondTerm" (.int (Int.ofNat (taylorTerm2 x n).toNat)) }

def taylorAfterThird (x n : UInt256) (imms : Store) : Frame :=
  { taylorAfterSecond x n imms with locals :=
      (taylorAfterSecond x n imms).locals.insert "thirdTerm" (.int (Int.ofNat (taylorTerm3 x n).toNat)) }

theorem taylor_eval_x (x n : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (taylorStart x n imms) evm (.var "x") = .ok (.int (Int.ofNat x.toNat)) := by
  simp only [evalExpr?, taylorStart, store_get_self, EvalResult.ofOption]

theorem taylor_eval_n (x n : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (taylorStart x n imms) evm (.var "n") = .ok (.int (Int.ofNat n.toNat)) := by
  simp only [evalExpr?, taylorStart, store_get_ne (k := "x") (a := "n") _ _ (by decide),
    store_get_self, EvalResult.ofOption]

theorem taylor_eval_first1 (x n : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (taylorAfterFirst x n imms) evm (.var "firstTerm") =
      .ok (.int (Int.ofNat (taylorTerm1 x n).toNat)) := by
  simp only [evalExpr?, taylorAfterFirst, store_get_self, EvalResult.ofOption]

theorem taylor_eval_first2 (x n : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (taylorAfterSecond x n imms) evm (.var "firstTerm") =
      .ok (.int (Int.ofNat (taylorTerm1 x n).toNat)) := by
  simp only [evalExpr?, taylorAfterSecond, taylorAfterFirst,
    store_get_ne (k := "secondTerm") (a := "firstTerm") _ _ (by decide),
    store_get_self, EvalResult.ofOption]

theorem taylor_eval_second2 (x n : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (taylorAfterSecond x n imms) evm (.var "secondTerm") =
      .ok (.int (Int.ofNat (taylorTerm2 x n).toNat)) := by
  simp only [evalExpr?, taylorAfterSecond, store_get_self, EvalResult.ofOption]

theorem taylor_eval_first3 (x n : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (taylorAfterThird x n imms) evm (.var "firstTerm") =
      .ok (.int (Int.ofNat (taylorTerm1 x n).toNat)) := by
  simp only [evalExpr?, taylorAfterThird, taylorAfterSecond, taylorAfterFirst,
    store_get_ne (k := "thirdTerm") (a := "firstTerm") _ _ (by decide),
    store_get_ne (k := "secondTerm") (a := "firstTerm") _ _ (by decide),
    store_get_self, EvalResult.ofOption]

theorem taylor_eval_second3 (x n : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (taylorAfterThird x n imms) evm (.var "secondTerm") =
      .ok (.int (Int.ofNat (taylorTerm2 x n).toNat)) := by
  simp only [evalExpr?, taylorAfterThird, taylorAfterSecond,
    store_get_ne (k := "thirdTerm") (a := "secondTerm") _ _ (by decide),
    store_get_self, EvalResult.ofOption]

theorem taylor_eval_third3 (x n : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (taylorAfterThird x n imms) evm (.var "thirdTerm") =
      .ok (.int (Int.ofNat (taylorTerm3 x n).toNat)) := by
  simp only [evalExpr?, taylorAfterThird, store_get_self, EvalResult.ofOption]

def taylorDenominator (n : Int) : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .mul (.intLit n) (.intLit 1000000000000000000))

theorem taylor_eval_denominator2 (frame : Frame) (evm : EVM.State) :
    evalExpr? config frame evm (taylorDenominator 2) =
      .ok (.int (Int.ofNat (UInt256.ofNat 2000000000000000000).toNat)) := by
  simp only [taylorDenominator, evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?]
  rfl

theorem taylor_eval_denominator3 (frame : Frame) (evm : EVM.State) :
    evalExpr? config frame evm (taylorDenominator 3) =
      .ok (.int (Int.ofNat (UInt256.ofNat 3000000000000000000).toNat)) := by
  simp only [taylorDenominator, evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?]
  rfl

theorem morphoTaylorFirst (x n : UInt256) (evm : EVM.State) (imms : Store)
    (h1 : x.toNat * n.toNat < UInt256.size) :
    ABlock config evm (taylorStart x n imms) taylorFunction.body
      (taylorAfterFirst x n imms) (taylorFunction.body.drop 1) := by
  exact ABlock.start.letStep (checkedMulSourceOk (taylor_eval_x x n imms evm)
    (taylor_eval_n x n imms evm) h1)

theorem morphoTaylorSecond (x n : UInt256) (evm : EVM.State) (imms : Store)
    (h1 : x.toNat * n.toNat < UInt256.size)
    (h2 : (taylorTerm1 x n).toNat * (taylorTerm1 x n).toNat < UInt256.size) :
    ABlock config evm (taylorStart x n imms) taylorFunction.body
      (taylorAfterSecond x n imms) (taylorFunction.body.drop 2) := by
  apply advancePureBlock (morphoTaylorFirst x n evm imms h1)
  exact morphoMulDivDownCallOk _ _ _ evm _ imms _ _ _ _
    (taylor_eval_first1 x n imms evm) (taylor_eval_first1 x n imms evm)
    (taylor_eval_denominator2 _ evm) h2 (by decide)

theorem morphoTaylorThird (x n : UInt256) (evm : EVM.State) (imms : Store)
    (h1 : x.toNat * n.toNat < UInt256.size)
    (h2 : (taylorTerm1 x n).toNat * (taylorTerm1 x n).toNat < UInt256.size)
    (h3 : (taylorTerm2 x n).toNat * (taylorTerm1 x n).toNat < UInt256.size) :
    ABlock config evm (taylorStart x n imms) taylorFunction.body
      (taylorAfterThird x n imms) (taylorFunction.body.drop 3) := by
  apply advancePureBlock (morphoTaylorSecond x n evm imms h1 h2)
  exact morphoMulDivDownCallOk _ _ _ evm _ imms _ _ _ _
    (taylor_eval_second2 x n imms evm) (taylor_eval_first2 x n imms evm)
    (taylor_eval_denominator3 _ evm) h3 (by decide)

theorem morphoTaylorBodyOk (x n : UInt256) (evm : EVM.State) (imms : Store) (hfit : TaylorFits x n) :
    ExecFuncBody config (taylorStart x n imms) evm taylorFunction.body
      (.returned (taylorAfterThird x n imms) evm (some [.int (Int.ofNat (taylorWord x n).toNat)])) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hfit
  apply ExecFuncBody.execBlockRet
  apply (morphoTaylorThird x n evm imms h1 h2 h3).returns
  exact checkedAddSourceOk
    (checkedAddSourceOk (taylor_eval_first3 x n imms evm) (taylor_eval_second3 x n imms evm) h4)
    (taylor_eval_third3 x n imms evm) h5

theorem morphoTaylorBodyReverts (x n : UInt256) (evm : EVM.State) (imms : Store)
    (hbad : ¬ TaylorFits x n) :
    ExecFuncBody config (taylorStart x n imms) evm taylorFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  by_cases h1 : x.toNat * n.toNat < UInt256.size
  · by_cases h2 : (taylorTerm1 x n).toNat * (taylorTerm1 x n).toNat < UInt256.size
    · by_cases h3 : (taylorTerm2 x n).toNat * (taylorTerm1 x n).toNat < UInt256.size
      · apply (morphoTaylorThird x n evm imms h1 h2 h3).run
        apply ExecBlock.consRevert
        apply ExecStmt.returnRevert
        by_cases h4 : (taylorTerm1 x n).toNat + (taylorTerm2 x n).toNat < UInt256.size
        · have h5 : UInt256.size ≤
              (taylorTerm1 x n + taylorTerm2 x n).toNat + (taylorTerm3 x n).toNat := by
            exact Nat.le_of_not_gt (fun h5 ↦ hbad ⟨h1, h2, h3, h4, h5⟩)
          have he := checkedAddSourceOverflow
            (checkedAddSourceOk (taylor_eval_first3 x n imms evm) (taylor_eval_second3 x n imms evm) h4)
            (taylor_eval_third3 x n imms evm) h5
          simp only [evalExprs?, he, bind, EvalResult.bind]
        · have he := checkedAddSourceOverflow
            (taylor_eval_first3 x n imms evm) (taylor_eval_second3 x n imms evm) (Nat.le_of_not_gt h4)
          simp only [evalExprs?, evalExpr?, he, bind, EvalResult.bind]
      · apply (morphoTaylorSecond x n evm imms h1 h2).run
        exact ExecBlock.consRevert (morphoMulDivDownCallReverts _ _ _ evm _ imms _ _ _ _
          (taylor_eval_second2 x n imms evm) (taylor_eval_first2 x n imms evm)
          (taylor_eval_denominator3 _ evm) (.inl (Nat.le_of_not_gt h3)))
    · apply (morphoTaylorFirst x n evm imms h1).run
      exact ExecBlock.consRevert (morphoMulDivDownCallReverts _ _ _ evm _ imms _ _ _ _
        (taylor_eval_first1 x n imms evm) (taylor_eval_first1 x n imms evm)
        (taylor_eval_denominator2 _ evm) (.inl (Nat.le_of_not_gt h2)))
  · exact ExecBlock.consRevert (ExecStmt.letDeclRevert (checkedMulSourceOverflow
      (taylor_eval_x x n imms evm) (taylor_eval_n x n imms evm) (Nat.le_of_not_gt h1)))

theorem morphoTaylorCallOk (x n : UInt256) (evm : EVM.State) (locals imms : Store)
    (ex en : Expr) (retVar : Ident)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ex =
      .ok (.int (Int.ofNat x.toNat)))
    (hn : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm en =
      .ok (.int (Int.ofNat n.toNat))) (hfit : TaylorFits x n) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_wTaylorCompounded" [ex, en] retVar)
      (.ok { contract := contract, locals := locals.insert retVar (.int (Int.ofNat (taylorWord x n).toNat)), immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := taylorFunction)
    (value := some [.int (Int.ofNat (taylorWord x n).toNat)])
    (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat n.toNat)])
    (by simp only [evalExprs?, hx, hn, bind, EvalResult.bind, pure]) rfl rfl
    (morphoTaylorBodyOk x n evm imms hfit)

theorem morphoTaylorCallReverts (x n : UInt256) (evm : EVM.State) (locals imms : Store)
    (ex en : Expr) (retVar : Ident)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ex =
      .ok (.int (Int.ofNat x.toNat)))
    (hn : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm en =
      .ok (.int (Int.ofNat n.toNat))) (hbad : ¬ TaylorFits x n) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_wTaylorCompounded" [ex, en] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := taylorFunction)
    (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat n.toNat)])
    (by simp only [evalExprs?, hx, hn, bind, EvalResult.bind, pure]) rfl rfl
    (morphoTaylorBodyReverts x n evm imms hbad)

end Benchmarks.Morpho.MorphoBlue
