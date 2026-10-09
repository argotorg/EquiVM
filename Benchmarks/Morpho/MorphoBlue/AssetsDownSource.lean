import Benchmarks.Morpho.MorphoBlue.AssetsUpSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev toAssetsDownFunction : FunctionDecl := contract.functions[8]!

def AssetsDownFits (shares totalAssets totalShares : UInt256) : Prop :=
  totalAssets.toNat + 1 < UInt256.size ∧
  totalShares.toNat + virtualShares.toNat < UInt256.size ∧
  shares.toNat * (totalAssets + UInt256.ofNat 1).toNat < UInt256.size

def assetsDownWord (shares totalAssets totalShares : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul shares (totalAssets + UInt256.ofNat 1)) (totalShares + virtualShares)

def assetsDownResultFrame (assets totalAssets totalShares : UInt256) (imms : Store) : Frame :=
  { assetsUpFrame assets totalAssets totalShares imms with locals :=
      ((assetsUpFrame assets totalAssets totalShares imms).locals.insert "__c0"
        (.int (Int.ofNat (assetsDownWord assets totalAssets totalShares).toNat))) }

theorem morphoAssetsDownBodyOk (a t s : UInt256) (evm : EVM.State) (imms : Store)
    (hfit : AssetsDownFits a t s) :
    ExecFuncBody config (assetsUpFrame a t s imms) evm toAssetsDownFunction.body
      (.returned (assetsDownResultFrame a t s imms) evm
        (some [.int (Int.ofNat (assetsDownWord a t s).toNat)])) := by
  obtain ⟨ht, hs, hp⟩ := hfit
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (morphoMulDivDownCallOk a (t + UInt256.ofNat 1) (s + virtualShares)
    evm _ imms _ _ _ _ (assetsUp_eval_shares a t s imms evm)
    (checkedAddSourceOk (assetsUp_eval_totalAssets a t s imms evm) (evalOne _ evm) ht)
    (checkedAddSourceOk (assetsUp_eval_totalShares a t s imms evm) (evalVirtualShares _ evm) hs) hp (u256_add_ne_zero_of_right_ne_zero (by decide) hs))
  apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
  simp only [evalExpr?, store_get_self, EvalResult.ofOption]
  rfl

theorem morphoAssetsDownBodyReverts (a t s : UInt256) (evm : EVM.State) (imms : Store)
    (hbad : ¬ AssetsDownFits a t s) :
    ExecFuncBody config (assetsUpFrame a t s imms) evm toAssetsDownFunction.body .reverted := by
  have ha := assetsUp_eval_shares a t s imms evm
  have hs := assetsUp_eval_totalShares a t s imms evm
  have ht := assetsUp_eval_totalAssets a t s imms evm
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  by_cases htfit : t.toNat + 1 < UInt256.size
  · have ht' := checkedAddSourceOk ht (evalOne _ evm) htfit
    by_cases hsfit : s.toNat + virtualShares.toNat < UInt256.size
    · have hs' := checkedAddSourceOk hs (evalVirtualShares _ evm) hsfit
      exact morphoMulDivDownCallReverts _ _ _ evm _ imms _ _ _ _ ha ht' hs'
        (.inl (Nat.le_of_not_gt (fun hp ↦ hbad ⟨htfit, hsfit, hp⟩)))
    · have hr := checkedAddSourceOverflow hs (evalVirtualShares _ evm) (Nat.le_of_not_gt hsfit)
      apply ExecStmt.internalCallArgsRevert
      simp only [evalExprs?, ha, ht', hr, bind, EvalResult.bind]
  · have hr := checkedAddSourceOverflow ht (evalOne _ evm) (Nat.le_of_not_gt htfit)
    apply ExecStmt.internalCallArgsRevert
    simp only [evalExprs?, ha, hr, bind, EvalResult.bind]

theorem morphoAssetsDownCallOk (a t s : UInt256) (evm : EVM.State) (locals imms : Store)
    (ea et es : Expr) (retVar : Ident)
    (ha : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ea =
      .ok (.int (Int.ofNat a.toNat)))
    (ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm et =
      .ok (.int (Int.ofNat t.toNat)))
    (hs : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm es =
      .ok (.int (Int.ofNat s.toNat))) (hfit : AssetsDownFits a t s) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SharesMathLib_toAssetsDown" [ea, et, es] retVar)
      (.ok { contract := contract, locals := locals.insert retVar (.int (Int.ofNat (assetsDownWord a t s).toNat)), immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := toAssetsDownFunction)
    (value := some [.int (Int.ofNat (assetsDownWord a t s).toNat)])
    (argVals := [.int (Int.ofNat a.toNat), .int (Int.ofNat t.toNat), .int (Int.ofNat s.toNat)])
    (by simp only [evalExprs?, ha, ht, hs, bind, EvalResult.bind, pure]) rfl rfl
    (morphoAssetsDownBodyOk a t s evm imms hfit)

theorem morphoAssetsDownCallReverts (a t s : UInt256) (evm : EVM.State) (locals imms : Store)
    (ea et es : Expr) (retVar : Ident)
    (ha : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ea =
      .ok (.int (Int.ofNat a.toNat)))
    (ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm et =
      .ok (.int (Int.ofNat t.toNat)))
    (hs : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm es =
      .ok (.int (Int.ofNat s.toNat))) (hbad : ¬ AssetsDownFits a t s) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SharesMathLib_toAssetsDown" [ea, et, es] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := toAssetsDownFunction)
    (argVals := [.int (Int.ofNat a.toNat), .int (Int.ofNat t.toNat), .int (Int.ofNat s.toNat)])
    (by simp only [evalExprs?, ha, ht, hs, bind, EvalResult.bind, pure]) rfl rfl
    (morphoAssetsDownBodyReverts a t s evm imms hbad)

end Benchmarks.Morpho.MorphoBlue
