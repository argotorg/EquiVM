import Benchmarks.Morpho.MorphoBlue.MathSource
import Benchmarks.Morpho.MorphoBlue.SharesMathCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev toSharesDownFunction : FunctionDecl := contract.functions[3]!

def sharesDownFrame (assets totalAssets totalShares : UInt256) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := (((∅ : Store).insert "totalShares" (.int (Int.ofNat totalShares.toNat))).insert
      "totalAssets" (.int (Int.ofNat totalAssets.toNat))).insert "assets" (.int (Int.ofNat assets.toNat)) }

def sharesDownResultFrame (assets totalAssets totalShares : UInt256) (imms : Store) : Frame :=
  { sharesDownFrame assets totalAssets totalShares imms with locals :=
      ((sharesDownFrame assets totalAssets totalShares imms).locals.insert "__c0"
        (.int (Int.ofNat (sharesDownWord assets totalAssets totalShares).toNat))) }

theorem sharesDown_eval_assets (a t s : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (sharesDownFrame a t s imms) evm (.var "assets") = .ok (.int (Int.ofNat a.toNat)) := by
  simp only [evalExpr?, sharesDownFrame, store_get_self, EvalResult.ofOption]

theorem sharesDown_eval_totalAssets (a t s : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (sharesDownFrame a t s imms) evm (.var "totalAssets") = .ok (.int (Int.ofNat t.toNat)) := by
  simp only [evalExpr?, sharesDownFrame, store_get_ne (k := "assets") (a := "totalAssets") _ _ (by decide),
    store_get_self, EvalResult.ofOption]

theorem sharesDown_eval_totalShares (a t s : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (sharesDownFrame a t s imms) evm (.var "totalShares") = .ok (.int (Int.ofNat s.toNat)) := by
  simp only [evalExpr?, sharesDownFrame, store_get_ne (k := "assets") (a := "totalShares") _ _ (by decide),
    store_get_ne (k := "totalAssets") (a := "totalShares") _ _ (by decide), store_get_self, EvalResult.ofOption]

theorem evalVirtualShares (frame : Frame) (evm : EVM.State) :
    evalExpr? config frame evm (.intLit 1000000) = .ok (.int (Int.ofNat virtualShares.toNat)) := by
  simp only [evalExpr?, pure]; rfl

theorem evalOne (frame : Frame) (evm : EVM.State) :
    evalExpr? config frame evm (.intLit 1) = .ok (.int (Int.ofNat (UInt256.ofNat 1).toNat)) := by
  simp only [evalExpr?, pure]; rfl

theorem morphoSharesDownBodyOk (a t s : UInt256) (evm : EVM.State) (imms : Store)
    (hfit : SharesDownFits a t s) :
    ExecFuncBody config (sharesDownFrame a t s imms) evm toSharesDownFunction.body
      (.returned (sharesDownResultFrame a t s imms) evm
        (some [.int (Int.ofNat (sharesDownWord a t s).toNat)])) := by
  obtain ⟨hs, ht, hp⟩ := hfit
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (morphoMulDivDownCallOk a (s + virtualShares) (t + UInt256.ofNat 1)
    evm _ imms _ _ _ _ (sharesDown_eval_assets a t s imms evm)
    (checkedAddSourceOk (sharesDown_eval_totalShares a t s imms evm) (evalVirtualShares _ evm) hs)
    (checkedAddSourceOk (sharesDown_eval_totalAssets a t s imms evm) (evalOne _ evm) ht)
    hp (sharesDownDenom_nonzero t ht))
  apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
  simp only [evalExpr?, store_get_self, EvalResult.ofOption]
  rfl

theorem morphoSharesDownBodyReverts (a t s : UInt256) (evm : EVM.State) (imms : Store)
    (hbad : ¬ SharesDownFits a t s) :
    ExecFuncBody config (sharesDownFrame a t s imms) evm toSharesDownFunction.body .reverted := by
  have ha := sharesDown_eval_assets a t s imms evm
  have hs := sharesDown_eval_totalShares a t s imms evm
  have ht := sharesDown_eval_totalAssets a t s imms evm
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  by_cases hsfit : s.toNat + virtualShares.toNat < UInt256.size
  · have hs' := checkedAddSourceOk hs (evalVirtualShares _ evm) hsfit
    by_cases htfit : t.toNat + 1 < UInt256.size
    · have ht' := checkedAddSourceOk ht (evalOne _ evm) htfit
      have hover : UInt256.size ≤ a.toNat * (s + virtualShares).toNat :=
        Nat.le_of_not_gt (fun hp ↦ hbad ⟨hsfit, htfit, hp⟩)
      exact morphoMulDivDownCallReverts _ _ _ evm _ imms _ _ _ _ ha hs' ht' (.inl hover)
    · have hr := checkedAddSourceOverflow ht (evalOne _ evm) (Nat.le_of_not_gt htfit)
      apply ExecStmt.internalCallArgsRevert
      simp only [evalExprs?, ha, hs', hr, bind, EvalResult.bind]
  · have hr := checkedAddSourceOverflow hs (evalVirtualShares _ evm) (Nat.le_of_not_gt hsfit)
    apply ExecStmt.internalCallArgsRevert
    simp only [evalExprs?, ha, hr, bind, EvalResult.bind]

theorem morphoSharesDownCallOk (a t s : UInt256) (evm : EVM.State) (locals imms : Store)
    (ea et es : Expr) (retVar : Ident)
    (ha : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ea =
      .ok (.int (Int.ofNat a.toNat)))
    (ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm et =
      .ok (.int (Int.ofNat t.toNat)))
    (hs : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm es =
      .ok (.int (Int.ofNat s.toNat))) (hfit : SharesDownFits a t s) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SharesMathLib_toSharesDown" [ea, et, es] retVar)
      (.ok { contract := contract, locals := locals.insert retVar (.int (Int.ofNat (sharesDownWord a t s).toNat)), immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := toSharesDownFunction)
    (value := some [.int (Int.ofNat (sharesDownWord a t s).toNat)])
    (argVals := [.int (Int.ofNat a.toNat), .int (Int.ofNat t.toNat), .int (Int.ofNat s.toNat)])
    (by simp only [evalExprs?, ha, ht, hs, bind, EvalResult.bind, pure]) rfl rfl
    (morphoSharesDownBodyOk a t s evm imms hfit)

theorem morphoSharesDownCallReverts (a t s : UInt256) (evm : EVM.State) (locals imms : Store)
    (ea et es : Expr) (retVar : Ident)
    (ha : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ea =
      .ok (.int (Int.ofNat a.toNat)))
    (ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm et =
      .ok (.int (Int.ofNat t.toNat)))
    (hs : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm es =
      .ok (.int (Int.ofNat s.toNat))) (hbad : ¬ SharesDownFits a t s) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SharesMathLib_toSharesDown" [ea, et, es] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := toSharesDownFunction)
    (argVals := [.int (Int.ofNat a.toNat), .int (Int.ofNat t.toNat), .int (Int.ofNat s.toNat)])
    (by simp only [evalExprs?, ha, ht, hs, bind, EvalResult.bind, pure]) rfl rfl
    (morphoSharesDownBodyReverts a t s evm imms hbad)

end Benchmarks.Morpho.MorphoBlue
