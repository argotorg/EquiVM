import Benchmarks.Morpho.MetaMorphoV1_1.MulDiv

/-! Rounded-up conversion from Morpho shares to assets. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

def sharesToAssetsUpFunction : FunctionDecl := contract.functions[57]!

def assetsUpFrame (imms : Store) (shares assets totalShares : UInt256) : Frame :=
  { contract := contract
    locals := (((∅ : Store).insert "totalShares" (uint256Value totalShares)).insert
      "totalAssets" (uint256Value assets)).insert "shares" (uint256Value shares)
    immutables := imms }

def assetsUpFits (shares assets totalShares : UInt256) : Prop :=
  assets.toNat + 1 < UInt256.size ∧ totalShares.toNat + 1000000 < UInt256.size ∧
    mulDivUpFits shares (assets + ⟨1⟩) (totalShares + UInt256.ofNat 1000000)

def assetsUpWord (shares assets totalShares : UInt256) : UInt256 :=
  mulDivUpWord shares (assets + ⟨1⟩) (totalShares + UInt256.ofNat 1000000)

theorem assetsUpFrame_shares (evm : EVM.State) (imms : Store)
    (shares assets totalShares : UInt256) :
    evalExpr? config (assetsUpFrame imms shares assets totalShares) evm (.var "shares") =
      .ok (uint256Value shares) := by
  simp only [evalExpr?, assetsUpFrame, store_get_self, EvalResult.ofOption]

theorem assetsUpFrame_assets (evm : EVM.State) (imms : Store)
    (shares assets totalShares : UInt256) :
    evalExpr? config (assetsUpFrame imms shares assets totalShares) evm (.var "totalAssets") =
      .ok (uint256Value assets) := by
  simp only [evalExpr?, assetsUpFrame,
    store_get_ne _ _ (show ("shares" == "totalAssets") = false from by decide),
    store_get_self, EvalResult.ofOption]

theorem assetsUpFrame_totalShares (evm : EVM.State) (imms : Store)
    (shares assets totalShares : UInt256) :
    evalExpr? config (assetsUpFrame imms shares assets totalShares) evm (.var "totalShares") =
      .ok (uint256Value totalShares) := by
  simp only [evalExpr?, assetsUpFrame,
    store_get_ne _ _ (show ("shares" == "totalShares") = false from by decide),
    store_get_ne _ _ (show ("totalAssets" == "totalShares") = false from by decide),
    store_get_self, EvalResult.ofOption]

theorem assetsUpBody (evm : EVM.State) (imms : Store) (shares assets totalShares : UInt256)
    (hfit : assetsUpFits shares assets totalShares) :
    ExecFuncBody config (assetsUpFrame imms shares assets totalShares) evm
      sharesToAssetsUpFunction.body
      (.returned
        { assetsUpFrame imms shares assets totalShares with
          locals := (assetsUpFrame imms shares assets totalShares).locals.insert "__c0"
            (uint256Value (assetsUpWord shares assets totalShares)) }
        evm (some [uint256Value (assetsUpWord shares assets totalShares)])) := by
  rcases hfit with ⟨ha, hs, hm⟩
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal
    (mulDivUpCall evm _ imms shares (assets + ⟨1⟩) (totalShares + UInt256.ofNat 1000000)
      "__c0" _ _ _
      hm (assetsUpFrame_shares evm imms shares assets totalShares)
      (checkedAddSourceOk (assetsUpFrame_assets evm imms shares assets totalShares)
        (by simp only [evalExpr?, uint256Value, pure]; rfl) ha)
      (checkedAddSourceOk (assetsUpFrame_totalShares evm imms shares assets totalShares)
        (by simp only [evalExpr?, uint256Value, pure]; rfl) hs)) ?_
  exact ABlock.start.returns (by
    simp only [evalExpr?, store_get_self, EvalResult.ofOption, assetsUpWord])

theorem assetsUpBodyReverts (evm : EVM.State) (imms : Store) (shares assets totalShares : UInt256)
    (hfail : ¬ assetsUpFits shares assets totalShares) :
    ExecFuncBody config (assetsUpFrame imms shares assets totalShares) evm
      sharesToAssetsUpFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  by_cases ha : assets.toNat + 1 < UInt256.size
  · have hea := checkedAddSourceOk (assetsUpFrame_assets evm imms shares assets totalShares)
      (rhs := .intLit 1) (b := ⟨1⟩)
      (by simp only [evalExpr?, pure]; rfl) ha
    by_cases hs : totalShares.toNat + 1000000 < UInt256.size
    · exact mulDivUpCallReverts evm _ imms shares (assets + ⟨1⟩)
        (totalShares + UInt256.ofNat 1000000)
        "__c0" _ _ _ (fun h ↦ hfail ⟨ha, hs, h⟩)
        (assetsUpFrame_shares evm imms shares assets totalShares) hea
        (checkedAddSourceOk (assetsUpFrame_totalShares evm imms shares assets totalShares)
          (by simp only [evalExpr?, uint256Value, pure]; rfl) hs)
    · have hes := checkedAddSourceOverflow
        (assetsUpFrame_totalShares evm imms shares assets totalShares)
        (rhs := .intLit 1000000) (b := UInt256.ofNat 1000000)
        (by simp only [evalExpr?, pure]; rfl) (Nat.le_of_not_gt hs)
      apply ExecStmt.internalCallArgsRevert
      simp only [evalExprs?, assetsUpFrame_shares, hea, hes, EvalResult.bind, bind]
  · have hea := checkedAddSourceOverflow (assetsUpFrame_assets evm imms shares assets totalShares)
      (rhs := .intLit 1) (b := ⟨1⟩)
      (by simp only [evalExpr?, pure]; rfl) (Nat.le_of_not_gt ha)
    apply ExecStmt.internalCallArgsRevert
    simp only [evalExprs?, assetsUpFrame_shares, hea, EvalResult.bind, bind]

theorem assetsUpCall (evm : EVM.State) (locals imms : Store) (shares assets totalShares : UInt256)
    (retVar : Ident) (sharesExpr assetsExpr totalSharesExpr : Expr)
    (hfit : assetsUpFits shares assets totalShares)
    (hshares : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm sharesExpr = .ok (uint256Value shares))
    (hassets : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm assetsExpr = .ok (uint256Value assets))
    (htotal : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm totalSharesExpr = .ok (uint256Value totalShares)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SharesMathLib_toAssetsUp" [sharesExpr, assetsExpr, totalSharesExpr] retVar)
      (.ok
        { contract := contract
          locals := locals.insert retVar (uint256Value (assetsUpWord shares assets totalShares))
          immutables := imms } evm) := by
  exact internalCallFunctionReturn
    (caller := { contract := contract, locals := locals, immutables := imms })
    (callee := sharesToAssetsUpFunction)
    (value := some [uint256Value (assetsUpWord shares assets totalShares)])
    (argVals := [uint256Value shares, uint256Value assets, uint256Value totalShares])
    (by simp [evalExprs?, hshares, hassets, htotal, bind, EvalResult.bind, pure]) rfl rfl
    (assetsUpBody evm imms shares assets totalShares hfit)

theorem assetsUpCallReverts (evm : EVM.State) (locals imms : Store)
    (shares assets totalShares : UInt256) (retVar : Ident)
    (sharesExpr assetsExpr totalSharesExpr : Expr)
    (hfail : ¬ assetsUpFits shares assets totalShares)
    (hshares : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm sharesExpr = .ok (uint256Value shares))
    (hassets : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm assetsExpr = .ok (uint256Value assets))
    (htotal : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm totalSharesExpr = .ok (uint256Value totalShares)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SharesMathLib_toAssetsUp" [sharesExpr, assetsExpr, totalSharesExpr] retVar)
      .reverted := by
  exact internalCallFunctionRevert (callee := sharesToAssetsUpFunction)
    (argVals := [uint256Value shares, uint256Value assets, uint256Value totalShares])
    (by simp [evalExprs?, hshares, hassets, htotal, bind, EvalResult.bind, pure]) rfl rfl
    (assetsUpBodyReverts evm imms shares assets totalShares hfail)


end Benchmarks.Morpho.MetaMorphoV1_1
