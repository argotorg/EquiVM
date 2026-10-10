import Benchmarks.Morpho.MetaMorphoV1_1.MulDiv

/-! Rounded-down conversion from Morpho shares to assets. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

def sharesToAssetsDownFunction : FunctionDecl := contract.functions[53]!

def assetsDownFrame (imms : Store) (shares assets totalShares : UInt256) : Frame :=
  { contract := contract
    locals := (((∅ : Store).insert "totalShares" (uint256Value totalShares)).insert
      "totalAssets" (uint256Value assets)).insert "shares" (uint256Value shares)
    immutables := imms }

def assetsDownFits (shares assets totalShares : UInt256) : Prop :=
  assets.toNat + 1 < UInt256.size ∧ totalShares.toNat + 1000000 < UInt256.size ∧
    shares.toNat * (assets + ⟨1⟩).toNat < UInt256.size ∧
    totalShares + UInt256.ofNat 1000000 ≠ ⟨0⟩

def assetsDownWord (shares assets totalShares : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul shares (assets + ⟨1⟩)) (totalShares + UInt256.ofNat 1000000)

theorem assetsDownFrame_shares (evm : EVM.State) (imms : Store)
    (shares assets totalShares : UInt256) :
    evalExpr? config (assetsDownFrame imms shares assets totalShares) evm (.var "shares") =
      .ok (uint256Value shares) := by
  simp only [evalExpr?, assetsDownFrame, store_get_self, EvalResult.ofOption]

theorem assetsDownFrame_assets (evm : EVM.State) (imms : Store)
    (shares assets totalShares : UInt256) :
    evalExpr? config (assetsDownFrame imms shares assets totalShares) evm (.var "totalAssets") =
      .ok (uint256Value assets) := by
  simp only [evalExpr?, assetsDownFrame,
    store_get_ne _ _ (show ("shares" == "totalAssets") = false from by decide),
    store_get_self, EvalResult.ofOption]

theorem assetsDownFrame_totalShares (evm : EVM.State) (imms : Store)
    (shares assets totalShares : UInt256) :
    evalExpr? config (assetsDownFrame imms shares assets totalShares) evm (.var "totalShares") =
      .ok (uint256Value totalShares) := by
  simp only [evalExpr?, assetsDownFrame,
    store_get_ne _ _ (show ("shares" == "totalShares") = false from by decide),
    store_get_ne _ _ (show ("totalAssets" == "totalShares") = false from by decide),
    store_get_self, EvalResult.ofOption]

theorem assetsDownBody (evm : EVM.State) (imms : Store) (shares assets totalShares : UInt256)
    (hfit : assetsDownFits shares assets totalShares) :
    ExecFuncBody config (assetsDownFrame imms shares assets totalShares) evm
      sharesToAssetsDownFunction.body
      (.returned
        { assetsDownFrame imms shares assets totalShares with
          locals := (assetsDownFrame imms shares assets totalShares).locals.insert "__c0"
            (uint256Value (assetsDownWord shares assets totalShares)) }
        evm (some [uint256Value (assetsDownWord shares assets totalShares)])) := by
  rcases hfit with ⟨ha, hs, hm⟩
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal
    (mulDivDownCall evm _ imms shares (assets + ⟨1⟩) (totalShares + UInt256.ofNat 1000000)
      "__c0" _ _ _
      hm.1 hm.2 (assetsDownFrame_shares evm imms shares assets totalShares)
      (checkedAddSourceOk (assetsDownFrame_assets evm imms shares assets totalShares)
        (by simp only [evalExpr?, uint256Value, pure]; rfl) ha)
      (checkedAddSourceOk (assetsDownFrame_totalShares evm imms shares assets totalShares)
        (by simp only [evalExpr?, uint256Value, pure]; rfl) hs)) ?_
  exact ABlock.start.returns (by
    simp only [evalExpr?, store_get_self, EvalResult.ofOption, assetsDownWord])

theorem assetsDownBodyReverts (evm : EVM.State) (imms : Store) (shares assets totalShares : UInt256)
    (hfail : ¬ assetsDownFits shares assets totalShares) :
    ExecFuncBody config (assetsDownFrame imms shares assets totalShares) evm
      sharesToAssetsDownFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  by_cases ha : assets.toNat + 1 < UInt256.size
  · have hea := checkedAddSourceOk (assetsDownFrame_assets evm imms shares assets totalShares)
      (rhs := .intLit 1) (b := ⟨1⟩)
      (by simp only [evalExpr?, pure]; rfl) ha
    by_cases hs : totalShares.toNat + 1000000 < UInt256.size
    · exact mulDivDownCallReverts evm _ imms shares (assets + ⟨1⟩)
        (totalShares + UInt256.ofNat 1000000)
        "__c0" _ _ _ (fun h ↦ hfail ⟨ha, hs, h⟩)
        (assetsDownFrame_shares evm imms shares assets totalShares) hea
        (checkedAddSourceOk (assetsDownFrame_totalShares evm imms shares assets totalShares)
          (by simp only [evalExpr?, uint256Value, pure]; rfl) hs)
    · have hes := checkedAddSourceOverflow
        (assetsDownFrame_totalShares evm imms shares assets totalShares)
        (rhs := .intLit 1000000) (b := UInt256.ofNat 1000000)
        (by simp only [evalExpr?, pure]; rfl) (Nat.le_of_not_gt hs)
      apply ExecStmt.internalCallArgsRevert
      simp only [evalExprs?, assetsDownFrame_shares, hea, hes, EvalResult.bind, bind]
  · have hea := checkedAddSourceOverflow (assetsDownFrame_assets evm imms shares assets totalShares)
      (rhs := .intLit 1) (b := ⟨1⟩)
      (by simp only [evalExpr?, pure]; rfl) (Nat.le_of_not_gt ha)
    apply ExecStmt.internalCallArgsRevert
    simp only [evalExprs?, assetsDownFrame_shares, hea, EvalResult.bind, bind]

theorem assetsDownCall (evm : EVM.State) (locals imms : Store) (shares assets totalShares : UInt256)
    (retVar : Ident) (sharesExpr assetsExpr totalSharesExpr : Expr)
    (hfit : assetsDownFits shares assets totalShares)
    (hshares : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm sharesExpr = .ok (uint256Value shares))
    (hassets : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm assetsExpr = .ok (uint256Value assets))
    (htotal : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm totalSharesExpr = .ok (uint256Value totalShares)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SharesMathLib_toAssetsDown" [sharesExpr, assetsExpr, totalSharesExpr] retVar)
      (.ok
        { contract := contract
          locals := locals.insert retVar (uint256Value (assetsDownWord shares assets totalShares))
          immutables := imms } evm) := by
  exact internalCallFunctionReturn
    (caller := { contract := contract, locals := locals, immutables := imms })
    (callee := sharesToAssetsDownFunction)
    (value := some [uint256Value (assetsDownWord shares assets totalShares)])
    (argVals := [uint256Value shares, uint256Value assets, uint256Value totalShares])
    (by simp only [evalExprs?, hshares, hassets, htotal, bind, EvalResult.bind, pure]) rfl rfl
    (assetsDownBody evm imms shares assets totalShares hfit)

theorem assetsDownCallReverts (evm : EVM.State) (locals imms : Store)
    (shares assets totalShares : UInt256) (retVar : Ident)
    (sharesExpr assetsExpr totalSharesExpr : Expr)
    (hfail : ¬ assetsDownFits shares assets totalShares)
    (hshares : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm sharesExpr = .ok (uint256Value shares))
    (hassets : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm assetsExpr = .ok (uint256Value assets))
    (htotal : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm totalSharesExpr = .ok (uint256Value totalShares)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SharesMathLib_toAssetsDown" [sharesExpr, assetsExpr, totalSharesExpr] retVar)
      .reverted := by
  exact internalCallFunctionRevert (callee := sharesToAssetsDownFunction)
    (argVals := [uint256Value shares, uint256Value assets, uint256Value totalShares])
    (by simp only [evalExprs?, hshares, hassets, htotal, bind, EvalResult.bind, pure]) rfl rfl
    (assetsDownBodyReverts evm imms shares assets totalShares hfail)


end Benchmarks.Morpho.MetaMorphoV1_1
