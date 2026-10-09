import Benchmarks.Morpho.MorphoBlue.MulDivUpSource
import Benchmarks.Morpho.MorphoBlue.SharesDownSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev toAssetsUpFunction : FunctionDecl := contract.functions[4]!

def AssetsUpFits (shares totalAssets totalShares : UInt256) : Prop :=
  totalAssets.toNat + 1 < UInt256.size ∧
  totalShares.toNat + virtualShares.toNat < UInt256.size ∧
  MulDivUpFits shares (totalAssets + UInt256.ofNat 1) (totalShares + virtualShares)

def assetsUpWord (shares totalAssets totalShares : UInt256) : UInt256 :=
  mulDivUpWord shares (totalAssets + UInt256.ofNat 1) (totalShares + virtualShares)

def assetsUpFrame (assets totalAssets totalShares : UInt256) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := (((∅ : Store).insert "totalShares" (.int (Int.ofNat totalShares.toNat))).insert
      "totalAssets" (.int (Int.ofNat totalAssets.toNat))).insert "shares" (.int (Int.ofNat assets.toNat)) }

def assetsUpResultFrame (assets totalAssets totalShares : UInt256) (imms : Store) : Frame :=
  { assetsUpFrame assets totalAssets totalShares imms with locals :=
      ((assetsUpFrame assets totalAssets totalShares imms).locals.insert "__c0"
        (.int (Int.ofNat (assetsUpWord assets totalAssets totalShares).toNat))) }

theorem assetsUp_eval_shares (a t s : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (assetsUpFrame a t s imms) evm (.var "shares") = .ok (.int (Int.ofNat a.toNat)) := by
  simp only [evalExpr?, assetsUpFrame, store_get_self, EvalResult.ofOption]

theorem assetsUp_eval_totalAssets (a t s : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (assetsUpFrame a t s imms) evm (.var "totalAssets") = .ok (.int (Int.ofNat t.toNat)) := by
  simp only [evalExpr?, assetsUpFrame, store_get_ne (k := "shares") (a := "totalAssets") _ _ (by decide),
    store_get_self, EvalResult.ofOption]

theorem assetsUp_eval_totalShares (a t s : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (assetsUpFrame a t s imms) evm (.var "totalShares") = .ok (.int (Int.ofNat s.toNat)) := by
  simp only [evalExpr?, assetsUpFrame, store_get_ne (k := "shares") (a := "totalShares") _ _ (by decide),
    store_get_ne (k := "totalAssets") (a := "totalShares") _ _ (by decide), store_get_self, EvalResult.ofOption]

theorem morphoAssetsUpBodyOk (a t s : UInt256) (evm : EVM.State) (imms : Store)
    (hfit : AssetsUpFits a t s) :
    ExecFuncBody config (assetsUpFrame a t s imms) evm toAssetsUpFunction.body
      (.returned (assetsUpResultFrame a t s imms) evm
        (some [.int (Int.ofNat (assetsUpWord a t s).toNat)])) := by
  obtain ⟨ht, hs, hp⟩ := hfit
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (morphoMulDivUpCallOk a (t + UInt256.ofNat 1) (s + virtualShares)
    evm _ imms _ _ _ _ (assetsUp_eval_shares a t s imms evm)
    (checkedAddSourceOk (assetsUp_eval_totalAssets a t s imms evm) (evalOne _ evm) ht)
    (checkedAddSourceOk (assetsUp_eval_totalShares a t s imms evm) (evalVirtualShares _ evm) hs) hp)
  apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
  simp only [evalExpr?, store_get_self, EvalResult.ofOption]
  rfl

theorem morphoAssetsUpBodyReverts (a t s : UInt256) (evm : EVM.State) (imms : Store)
    (hbad : ¬ AssetsUpFits a t s) :
    ExecFuncBody config (assetsUpFrame a t s imms) evm toAssetsUpFunction.body .reverted := by
  have ha := assetsUp_eval_shares a t s imms evm
  have hs := assetsUp_eval_totalShares a t s imms evm
  have ht := assetsUp_eval_totalAssets a t s imms evm
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  by_cases htfit : t.toNat + 1 < UInt256.size
  · have ht' := checkedAddSourceOk ht (evalOne _ evm) htfit
    by_cases hsfit : s.toNat + virtualShares.toNat < UInt256.size
    · have hs' := checkedAddSourceOk hs (evalVirtualShares _ evm) hsfit
      exact morphoMulDivUpCallReverts _ _ _ evm _ imms _ _ _ _ ha ht' hs'
        (fun hp ↦ hbad ⟨htfit, hsfit, hp⟩)
    · have hr := checkedAddSourceOverflow hs (evalVirtualShares _ evm) (Nat.le_of_not_gt hsfit)
      apply ExecStmt.internalCallArgsRevert
      simp only [evalExprs?, ha, ht', hr, bind, EvalResult.bind]
  · have hr := checkedAddSourceOverflow ht (evalOne _ evm) (Nat.le_of_not_gt htfit)
    apply ExecStmt.internalCallArgsRevert
    simp only [evalExprs?, ha, hr, bind, EvalResult.bind]

theorem morphoAssetsUpCallOk (a t s : UInt256) (evm : EVM.State) (locals imms : Store)
    (ea et es : Expr) (retVar : Ident)
    (ha : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ea =
      .ok (.int (Int.ofNat a.toNat)))
    (ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm et =
      .ok (.int (Int.ofNat t.toNat)))
    (hs : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm es =
      .ok (.int (Int.ofNat s.toNat))) (hfit : AssetsUpFits a t s) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SharesMathLib_toAssetsUp" [ea, et, es] retVar)
      (.ok { contract := contract, locals := locals.insert retVar (.int (Int.ofNat (assetsUpWord a t s).toNat)), immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := toAssetsUpFunction)
    (value := some [.int (Int.ofNat (assetsUpWord a t s).toNat)])
    (argVals := [.int (Int.ofNat a.toNat), .int (Int.ofNat t.toNat), .int (Int.ofNat s.toNat)])
    (by simp only [evalExprs?, ha, ht, hs, bind, EvalResult.bind, pure]) rfl rfl
    (morphoAssetsUpBodyOk a t s evm imms hfit)

theorem morphoAssetsUpCallReverts (a t s : UInt256) (evm : EVM.State) (locals imms : Store)
    (ea et es : Expr) (retVar : Ident)
    (ha : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ea =
      .ok (.int (Int.ofNat a.toNat)))
    (ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm et =
      .ok (.int (Int.ofNat t.toNat)))
    (hs : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm es =
      .ok (.int (Int.ofNat s.toNat))) (hbad : ¬ AssetsUpFits a t s) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SharesMathLib_toAssetsUp" [ea, et, es] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := toAssetsUpFunction)
    (argVals := [.int (Int.ofNat a.toNat), .int (Int.ofNat t.toNat), .int (Int.ofNat s.toNat)])
    (by simp only [evalExprs?, ha, ht, hs, bind, EvalResult.bind, pure]) rfl rfl
    (morphoAssetsUpBodyReverts a t s evm imms hbad)

end Benchmarks.Morpho.MorphoBlue
