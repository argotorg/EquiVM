import Benchmarks.Morpho.MorphoBlue.MarketTransferLocals
import Benchmarks.Morpho.MorphoBlue.SharesUpSource
import Benchmarks.Morpho.MorphoBlue.AssetsDownSource
import Benchmarks.Morpho.MorphoBlue.StateBlock

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def marketTransferMathStmt (a q : Fin 6) : Stmt :=
  .ite (.binary .gt (.var "assets") (.intLit 0))
    [.internalCall "SharesMathLib_toSharesUp"
      [.var "assets", .storage ⟨"market", [.mindex (.var "id"), .field (marketFieldName a)]⟩,
        .storage ⟨"market", [.mindex (.var "id"), .field (marketFieldName q)]⟩] "__c4",
      .assign .localVar ⟨"shares", []⟩ (.var "__c4")]
    [.internalCall "SharesMathLib_toAssetsDown"
      [.var "shares", .storage ⟨"market", [.mindex (.var "id"), .field (marketFieldName a)]⟩,
        .storage ⟨"market", [.mindex (.var "id"), .field (marketFieldName q)]⟩] "__c5",
      .assign .localVar ⟨"assets", []⟩ (.var "__c5")]

section Source
variable {p : MarketParamsWords} {assets shares account receiver : UInt256} {locals imms : Store}
  {evm : EVM.State} (a q : Fin 6)
  (hl : MarketTransferLocals p assets shares account receiver locals)
include hl

theorem marketTransferMath_assetsOk (hz : assets = ⟨0⟩)
    (hf : AssetsDownFits shares (marketFieldWord evm.accountMap evm.executionEnv p.id a)
      (marketFieldWord evm.accountMap evm.executionEnv p.id q)) :
    ∃ locals', ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (marketTransferMathStmt a q) (.ok { contract := contract, locals := locals', immutables := imms } evm) ∧
      MarketTransferLocals p (assetsDownWord shares (marketFieldWord evm.accountMap evm.executionEnv p.id a)
        (marketFieldWord evm.accountMap evm.executionEnv p.id q)) shares account receiver locals' ∧
      locals'.get? "__memory" = locals.get? "__memory" := by
  have hcond := evalExpr_uint256_var_positive (cfg := config)
    (frame := { contract := contract, locals := locals, immutables := imms }) evm "assets" assets hl.assets_eq
  have he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .gt (.var "assets") (.intLit 0)) = .ok (.bool false) := by
    simpa only [hz, Nat.lt_irrefl, decide_false] using hcond
  let value := assetsDownWord shares (marketFieldWord evm.accountMap evm.executionEnv p.id a)
    (marketFieldWord evm.accountMap evm.executionEnv p.id q)
  have hcall := morphoAssetsDownCallOk _ _ _ evm locals imms _ _ _ "__c5"
    (hl.evalShares imms evm) (hl.evalField imms evm a) (hl.evalField imms evm q) hf
  have hl1 := hl.insert "__c5" (.int (Int.ofNat value.toNat)) (by decide) (by decide)
  have hass : ExecStmt config
      { contract := contract, locals := locals.insert "__c5" (.int (Int.ofNat value.toNat)), immutables := imms }
      evm (.assign .localVar ⟨"assets", []⟩ (.var "__c5"))
      (.ok { contract := contract, immutables := imms,
                locals := (locals.insert "__c5" (.int (Int.ofNat value.toNat))).insert "assets" (.int (Int.ofNat value.toNat)) } evm) :=
    ExecStmt.assign (by simp only [evalExpr?, store_get_self, EvalResult.ofOption]) (assignLocalWord hl1.assets_eq)
  refine ⟨_, ExecStmt.iteFalse he (ExecBlock.consNormal hcall (ExecBlock.consNormal hass ExecBlock.nil)), hl1.setAssets value, ?_⟩
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]

theorem marketTransferMath_assetsReverts (hz : assets = ⟨0⟩)
    (hf : ¬ AssetsDownFits shares (marketFieldWord evm.accountMap evm.executionEnv p.id a)
      (marketFieldWord evm.accountMap evm.executionEnv p.id q)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (marketTransferMathStmt a q) .reverted := by
  have hcond := evalExpr_uint256_var_positive (cfg := config)
    (frame := { contract := contract, locals := locals, immutables := imms }) evm "assets" assets hl.assets_eq
  have he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .gt (.var "assets") (.intLit 0)) = .ok (.bool false) := by
    simpa only [hz, Nat.lt_irrefl, decide_false] using hcond
  exact ExecStmt.iteFalse he (ExecBlock.consRevert (morphoAssetsDownCallReverts _ _ _ evm locals imms _ _ _ "__c5"
    (hl.evalShares imms evm) (hl.evalField imms evm a) (hl.evalField imms evm q) hf))

theorem marketTransferMath_sharesOk (hn : assets ≠ ⟨0⟩)
    (hf : SharesUpFits assets (marketFieldWord evm.accountMap evm.executionEnv p.id a)
      (marketFieldWord evm.accountMap evm.executionEnv p.id q)) :
    ∃ locals', ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (marketTransferMathStmt a q) (.ok { contract := contract, locals := locals', immutables := imms } evm) ∧
      MarketTransferLocals p assets (sharesUpWord assets (marketFieldWord evm.accountMap evm.executionEnv p.id a)
        (marketFieldWord evm.accountMap evm.executionEnv p.id q)) account receiver locals' ∧
      locals'.get? "__memory" = locals.get? "__memory" := by
  have hcond := evalExpr_uint256_var_positive (cfg := config)
    (frame := { contract := contract, locals := locals, immutables := imms }) evm "assets" assets hl.assets_eq
  have hp : 0 < assets.toNat := Nat.pos_of_ne_zero (fun h ↦ hn (uint256_toNat_eq_zero h))
  have he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .gt (.var "assets") (.intLit 0)) = .ok (.bool true) := by
    simpa only [decide_eq_true hp] using hcond
  let value := sharesUpWord assets (marketFieldWord evm.accountMap evm.executionEnv p.id a)
    (marketFieldWord evm.accountMap evm.executionEnv p.id q)
  have hcall := morphoSharesUpCallOk _ _ _ evm locals imms _ _ _ "__c4"
    (hl.evalAssets imms evm) (hl.evalField imms evm a) (hl.evalField imms evm q) hf
  have hl1 := hl.insert "__c4" (.int (Int.ofNat value.toNat)) (by decide) (by decide)
  have hass : ExecStmt config
      { contract := contract, locals := locals.insert "__c4" (.int (Int.ofNat value.toNat)), immutables := imms }
      evm (.assign .localVar ⟨"shares", []⟩ (.var "__c4"))
      (.ok { contract := contract, immutables := imms,
                locals := (locals.insert "__c4" (.int (Int.ofNat value.toNat))).insert "shares" (.int (Int.ofNat value.toNat)) } evm) :=
    ExecStmt.assign (by simp only [evalExpr?, store_get_self, EvalResult.ofOption]) (assignLocalWord hl1.shares_eq)
  refine ⟨_, ExecStmt.iteTrue he (ExecBlock.consNormal hcall (ExecBlock.consNormal hass ExecBlock.nil)), hl1.setShares value, ?_⟩
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]

theorem marketTransferMath_sharesReverts (hn : assets ≠ ⟨0⟩)
    (hf : ¬ SharesUpFits assets (marketFieldWord evm.accountMap evm.executionEnv p.id a)
      (marketFieldWord evm.accountMap evm.executionEnv p.id q)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (marketTransferMathStmt a q) .reverted := by
  have hcond := evalExpr_uint256_var_positive (cfg := config)
    (frame := { contract := contract, locals := locals, immutables := imms }) evm "assets" assets hl.assets_eq
  have hp : 0 < assets.toNat := Nat.pos_of_ne_zero (fun h ↦ hn (uint256_toNat_eq_zero h))
  have he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .gt (.var "assets") (.intLit 0)) = .ok (.bool true) := by
    simpa only [decide_eq_true hp] using hcond
  exact ExecStmt.iteTrue he (ExecBlock.consRevert (morphoSharesUpCallReverts _ _ _ evm locals imms _ _ _ "__c4"
    (hl.evalAssets imms evm) (hl.evalField imms evm a) (hl.evalField imms evm q) hf))

end Source
end Benchmarks.Morpho.MorphoBlue
