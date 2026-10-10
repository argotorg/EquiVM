import Benchmarks.Morpho.MetaMorphoV1_1.MulDiv

/-! Rounded-down shares for canonical uint128 market totals, including product overflow. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def sharesDownFunction : FunctionDecl := contract.functions[81]!

def sharesDownFrame (imms : Store) (assets totalAssets totalShares : UInt256) : Frame :=
  { contract := contract
    locals := (((∅ : Store).insert "totalShares" (uint256Value totalShares)).insert
      "totalAssets" (uint256Value totalAssets)).insert "assets" (uint256Value assets)
    immutables := imms }

def sharesDownWord (assets totalAssets totalShares : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul assets (totalShares + UInt256.ofNat 1000000))
    (totalAssets + UInt256.ofNat 1)

def sharesDownFits (assets totalShares : UInt256) : Prop :=
  assets.toNat * (totalShares + UInt256.ofNat 1000000).toNat < UInt256.size

instance (assets totalShares : UInt256) : Decidable (sharesDownFits assets totalShares) :=
  inferInstanceAs (Decidable (_ < _))

theorem sharesDownFrame_values (evm : State) (imms : Store)
    (assets totalAssets totalShares : UInt256) :
    evalExpr? config (sharesDownFrame imms assets totalAssets totalShares) evm (.var "assets") =
      .ok (uint256Value assets) ∧
    evalExpr? config (sharesDownFrame imms assets totalAssets totalShares) evm
      (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "totalShares") (.intLit 1000000))) =
      (if totalShares.toNat + 1000000 < UInt256.size then
        .ok (uint256Value (totalShares + UInt256.ofNat 1000000)) else .revert) := by
  constructor
  · simp only [evalExpr?, sharesDownFrame, store_get_self, EvalResult.ofOption]
  · have he : evalExpr? config (sharesDownFrame imms assets totalAssets totalShares) evm
        (.var "totalShares") = .ok (uint256Value totalShares) := by
      simp only [evalExpr?, sharesDownFrame,
        store_get_ne _ _ (by decide : ("assets" == "totalShares") = false),
        store_get_ne _ _ (by decide : ("totalAssets" == "totalShares") = false),
        store_get_self, EvalResult.ofOption]
    by_cases hfit : totalShares.toNat + 1000000 < UInt256.size
    · rw [if_pos hfit]
      exact checkedAddSourceOk he (by simp only [evalExpr?, pure]; rfl) hfit
    · rw [if_neg hfit]
      exact checkedAddSourceOverflow (b := UInt256.ofNat 1000000) he
        (by simp only [evalExpr?, pure]; rfl)
        (Nat.le_of_not_lt hfit)

theorem sharesDownFrame_denominator (evm : State) (imms : Store)
    (assets totalAssets totalShares : UInt256) (ha : totalAssets.toNat < 2 ^ 128) :
    evalExpr? config (sharesDownFrame imms assets totalAssets totalShares) evm
      (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "totalAssets") (.intLit 1))) =
      .ok (uint256Value (totalAssets + UInt256.ofNat 1)) := by
  exact checkedAddSourceOk
    (show evalExpr? config (sharesDownFrame imms assets totalAssets totalShares) evm
      (.var "totalAssets") = .ok (uint256Value totalAssets) by
        simp only [evalExpr?, sharesDownFrame,
          store_get_ne _ _ (by decide : ("assets" == "totalAssets") = false),
          store_get_self, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]; rfl) (by change totalAssets.toNat + 1 < 2 ^ 256; omega)

theorem sharesDownDenominatorNonzero {totalAssets : UInt256}
    (ha : totalAssets.toNat < 2 ^ 128) : totalAssets + UInt256.ofNat 1 ≠ ⟨0⟩ := by
  intro hz
  have he := congrArg UInt256.toNat hz
  rw [uadd_toNat] at he
  have h1 : (UInt256.ofNat 1).toNat = 1 := rfl
  have h0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  rw [h1, h0, Nat.mod_eq_of_lt (show totalAssets.toNat + 1 < UInt256.size by
    change _ < 2 ^ 256; omega)] at he
  omega

theorem sharesDownBody (evm : State) (imms : Store) (assets totalAssets totalShares : UInt256)
    (ha : totalAssets.toNat < 2 ^ 128) (hs : totalShares.toNat < 2 ^ 128)
    (hfit : sharesDownFits assets totalShares) :
    ExecFuncBody config (sharesDownFrame imms assets totalAssets totalShares) evm
      sharesDownFunction.body
      (.returned { sharesDownFrame imms assets totalAssets totalShares with
        locals := (sharesDownFrame imms assets totalAssets totalShares).locals.insert "__c0"
          (uint256Value (sharesDownWord assets totalAssets totalShares)) } evm
        [uint256Value (sharesDownWord assets totalAssets totalShares)]) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (mulDivDownCall evm _ imms assets
    (totalShares + UInt256.ofNat 1000000) (totalAssets + UInt256.ofNat 1) "__c0" _ _ _
    hfit (sharesDownDenominatorNonzero ha)
    (sharesDownFrame_values evm imms assets totalAssets totalShares).1
    (by simpa only [if_pos (show totalShares.toNat + 1000000 < UInt256.size by
          change _ < 2 ^ 256; omega)] using
        (sharesDownFrame_values evm imms assets totalAssets totalShares).2)
    (sharesDownFrame_denominator evm imms assets totalAssets totalShares ha))
  exact ABlock.start.returns (by
    simp only [evalExpr?, store_get_self, EvalResult.ofOption, sharesDownWord])

theorem sharesDownBodyReverts (evm : State) (imms : Store)
    (assets totalAssets totalShares : UInt256)
    (ha : totalAssets.toNat < 2 ^ 128) (hs : totalShares.toNat < 2 ^ 128)
    (hbad : ¬ sharesDownFits assets totalShares) :
    ExecFuncBody config (sharesDownFrame imms assets totalAssets totalShares) evm
      sharesDownFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact ExecBlock.consRevert (mulDivDownCallReverts evm _ imms assets
    (totalShares + UInt256.ofNat 1000000) (totalAssets + UInt256.ofNat 1) "__c0" _ _ _
    (fun h ↦ hbad h.1) (sharesDownFrame_values evm imms assets totalAssets totalShares).1
    (by simpa only [if_pos (show totalShares.toNat + 1000000 < UInt256.size by
          change _ < 2 ^ 256; omega)] using
        (sharesDownFrame_values evm imms assets totalAssets totalShares).2)
    (sharesDownFrame_denominator evm imms assets totalAssets totalShares ha))

set_option maxRecDepth 2000 in
theorem sharesDownCall (evm : State) (locals imms : Store)
    (assets totalAssets totalShares : UInt256) (retVar : Ident)
    (assetsExpr totalAssetsExpr totalSharesExpr : Expr)
    (ha : totalAssets.toNat < 2 ^ 128) (hs : totalShares.toNat < 2 ^ 128)
    (hfit : sharesDownFits assets totalShares)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm assetsExpr = .ok (uint256Value assets))
    (hta : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm totalAssetsExpr = .ok (uint256Value totalAssets))
    (hts : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm totalSharesExpr = .ok (uint256Value totalShares)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SharesMathLib_toSharesDown" [assetsExpr, totalAssetsExpr, totalSharesExpr]
        retVar)
      (.ok
        { contract := contract
          locals := locals.insert retVar
            (uint256Value (sharesDownWord assets totalAssets totalShares))
          immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := sharesDownFunction)
    (caller := { contract := contract, locals := locals, immutables := imms })
    (value := some [uint256Value (sharesDownWord assets totalAssets totalShares)])
    (argVals := [uint256Value assets, uint256Value totalAssets, uint256Value totalShares])
    (by simp only [evalExprs?, hx, hta, hts, bind, EvalResult.bind, pure]) rfl rfl
    (sharesDownBody evm imms assets totalAssets totalShares ha hs hfit)

set_option maxRecDepth 2000 in
theorem sharesDownCallReverts (evm : State) (locals imms : Store)
    (assets totalAssets totalShares : UInt256) (retVar : Ident)
    (assetsExpr totalAssetsExpr totalSharesExpr : Expr)
    (ha : totalAssets.toNat < 2 ^ 128) (hs : totalShares.toNat < 2 ^ 128)
    (hbad : ¬ sharesDownFits assets totalShares)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm assetsExpr = .ok (uint256Value assets))
    (hta : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm totalAssetsExpr = .ok (uint256Value totalAssets))
    (hts : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm totalSharesExpr = .ok (uint256Value totalShares)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SharesMathLib_toSharesDown" [assetsExpr, totalAssetsExpr, totalSharesExpr]
        retVar) .reverted := by
  exact internalCallFunctionRevert (callee := sharesDownFunction)
    (argVals := [uint256Value assets, uint256Value totalAssets, uint256Value totalShares])
    (by simp only [evalExprs?, hx, hta, hts, bind, EvalResult.bind, pure]) rfl rfl
    (sharesDownBodyReverts evm imms assets totalAssets totalShares ha hs hbad)

end Benchmarks.Morpho.MetaMorphoV1_1
