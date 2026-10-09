import Benchmarks.Morpho.MorphoBlue.AssetsUpSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev toSharesUpFunction : FunctionDecl := contract.functions[7]!

def SharesUpFits (assets totalAssets totalShares : UInt256) : Prop :=
  totalShares.toNat + virtualShares.toNat < UInt256.size ∧
  totalAssets.toNat + 1 < UInt256.size ∧
  MulDivUpFits assets (totalShares + virtualShares) (totalAssets + UInt256.ofNat 1)

def sharesUpWord (assets totalAssets totalShares : UInt256) : UInt256 :=
  mulDivUpWord assets (totalShares + virtualShares) (totalAssets + UInt256.ofNat 1)

def sharesUpResultFrame (assets totalAssets totalShares : UInt256) (imms : Store) : Frame :=
  { sharesDownFrame assets totalAssets totalShares imms with locals :=
      ((sharesDownFrame assets totalAssets totalShares imms).locals.insert "__c0"
        (.int (Int.ofNat (sharesUpWord assets totalAssets totalShares).toNat))) }

theorem morphoSharesUpBodyOk (a t s : UInt256) (evm : EVM.State) (imms : Store)
    (hfit : SharesUpFits a t s) :
    ExecFuncBody config (sharesDownFrame a t s imms) evm toSharesUpFunction.body
      (.returned (sharesUpResultFrame a t s imms) evm
        (some [.int (Int.ofNat (sharesUpWord a t s).toNat)])) := by
  obtain ⟨hs, ht, hp⟩ := hfit
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (morphoMulDivUpCallOk a (s + virtualShares) (t + UInt256.ofNat 1)
    evm _ imms _ _ _ _ (sharesDown_eval_assets a t s imms evm)
    (checkedAddSourceOk (sharesDown_eval_totalShares a t s imms evm) (evalVirtualShares _ evm) hs)
    (checkedAddSourceOk (sharesDown_eval_totalAssets a t s imms evm) (evalOne _ evm) ht)
    hp)
  apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
  simp only [evalExpr?, store_get_self, EvalResult.ofOption]
  rfl

theorem morphoSharesUpBodyReverts (a t s : UInt256) (evm : EVM.State) (imms : Store)
    (hbad : ¬ SharesUpFits a t s) :
    ExecFuncBody config (sharesDownFrame a t s imms) evm toSharesUpFunction.body .reverted := by
  have ha := sharesDown_eval_assets a t s imms evm
  have hs := sharesDown_eval_totalShares a t s imms evm
  have ht := sharesDown_eval_totalAssets a t s imms evm
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  by_cases hsfit : s.toNat + virtualShares.toNat < UInt256.size
  · have hs' := checkedAddSourceOk hs (evalVirtualShares _ evm) hsfit
    by_cases htfit : t.toNat + 1 < UInt256.size
    · have ht' := checkedAddSourceOk ht (evalOne _ evm) htfit
      exact morphoMulDivUpCallReverts _ _ _ evm _ imms _ _ _ _ ha hs' ht'
        (fun hp ↦ hbad ⟨hsfit, htfit, hp⟩)
    · have hr := checkedAddSourceOverflow ht (evalOne _ evm) (Nat.le_of_not_gt htfit)
      apply ExecStmt.internalCallArgsRevert
      simp only [evalExprs?, ha, hs', hr, bind, EvalResult.bind]
  · have hr := checkedAddSourceOverflow hs (evalVirtualShares _ evm) (Nat.le_of_not_gt hsfit)
    apply ExecStmt.internalCallArgsRevert
    simp only [evalExprs?, ha, hr, bind, EvalResult.bind]

theorem morphoSharesUpCallOk (a t s : UInt256) (evm : EVM.State) (locals imms : Store)
    (ea et es : Expr) (retVar : Ident)
    (ha : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ea =
      .ok (.int (Int.ofNat a.toNat)))
    (ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm et =
      .ok (.int (Int.ofNat t.toNat)))
    (hs : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm es =
      .ok (.int (Int.ofNat s.toNat))) (hfit : SharesUpFits a t s) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SharesMathLib_toSharesUp" [ea, et, es] retVar)
      (.ok { contract := contract, locals := locals.insert retVar (.int (Int.ofNat (sharesUpWord a t s).toNat)), immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := toSharesUpFunction)
    (value := some [.int (Int.ofNat (sharesUpWord a t s).toNat)])
    (argVals := [.int (Int.ofNat a.toNat), .int (Int.ofNat t.toNat), .int (Int.ofNat s.toNat)])
    (by simp only [evalExprs?, ha, ht, hs, bind, EvalResult.bind, pure]) rfl rfl
    (morphoSharesUpBodyOk a t s evm imms hfit)

theorem morphoSharesUpCallReverts (a t s : UInt256) (evm : EVM.State) (locals imms : Store)
    (ea et es : Expr) (retVar : Ident)
    (ha : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ea =
      .ok (.int (Int.ofNat a.toNat)))
    (ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm et =
      .ok (.int (Int.ofNat t.toNat)))
    (hs : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm es =
      .ok (.int (Int.ofNat s.toNat))) (hbad : ¬ SharesUpFits a t s) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SharesMathLib_toSharesUp" [ea, et, es] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := toSharesUpFunction)
    (argVals := [.int (Int.ofNat a.toNat), .int (Int.ofNat t.toNat), .int (Int.ofNat s.toNat)])
    (by simp only [evalExprs?, ha, ht, hs, bind, EvalResult.bind, pure]) rfl rfl
    (morphoSharesUpBodyReverts a t s evm imms hbad)

end Benchmarks.Morpho.MorphoBlue
