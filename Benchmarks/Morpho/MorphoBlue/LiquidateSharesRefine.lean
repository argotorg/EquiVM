import Benchmarks.Morpho.MorphoBlue.LiquidateAmountRefines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoLiquidateSharesRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw account seized shares price srcOff len : UInt256} {out mem data : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 40 ≤ 1024) (hl : LiquidateLocals p account seized shares data locals)
    (hs : SourceState s0 ee σ evm) (hz : seized = ⟨0⟩)
    (hprice : locals.get? "collateralPrice" = some (.int (Int.ofNat price.toNat)))
    (hfactor : locals.get? "liquidationIncentiveFactor" = some (.int (Int.ofNat (liquidationFactor p.lltv).toNat)))
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1743)
      (liquidateMathStack p.id seized shares price (liquidationDenom p.lltv) srcOff len R) mem aw out σ k C) :
    LiquidateAmountRefines v ee g s0 p account srcOff len data locals imms evm σ mem R := by
  have hcond : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .gt (.var "seizedAssets") (.intLit 0)) = .ok (.bool false) := by
    simpa only [hz, Nat.lt_irrefl, decide_false] using evalExpr_uint256_var_positive (cfg := config)
      (frame := { contract := contract, locals := locals, immutables := imms }) evm "seizedAssets" seized hl.seized_eq
  have heassets := hl.evalField imms evm ⟨2, by decide⟩
  have heshares := hl.evalField imms evm ⟨3, by decide⟩
  rw [hs.env, ← hs.accounts] at heassets heshares
  obtain ⟨a1, k1, C1, rd1⟩ := morphoLiquidateReachDebt (v := v) (by omega) hz h
  by_cases hf1 : AssetsDownFits shares (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3)
  swap
  · exact .reverted (ExecBlock.consRevert (ExecStmt.iteFalse hcond (ExecBlock.consRevert
      (morphoAssetsDownCallReverts _ _ _ evm locals imms _ _ _ "debtAssets"
        (hl.evalShares imms evm) heassets heshares hf1))))
      (morphoAssetsDownReverts (v := v) (by change R.length + 10 + 12 ≤ 1024; omega) hf1 rd1)
  obtain ⟨k2, C2, rd2⟩ := morphoAssetsDownOk (v := v) (by change R.length + 10 + 12 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hf1 rd1
  have rd3 := morphoBlocks.morpho_block_3443 (immWords := wordsOf (immStore v))
    (by change R.length + 11 + 1 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  let debt := assetsDownWord shares (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3)
  let l1 := locals.insert "debtAssets" (.int (Int.ofNat debt.toNat))
  have hl1 : LiquidateLocals p account seized shares data l1 := hl.insert _ _ (by decide) (by decide)
  have ab1 : ABlock config evm { contract := contract, locals := locals, immutables := imms }
      liquidateSharesBody { contract := contract, locals := l1, immutables := imms } (liquidateSharesBody.drop 1) :=
    advancePureBlock ABlock.start (morphoAssetsDownCallOk _ _ _ evm locals imms _ _ _ "debtAssets"
      (hl.evalShares imms evm) heassets heshares hf1)
  have hedebt : evalExpr? config { contract := contract, locals := l1, immutables := imms } evm
      (.var "debtAssets") = .ok (.int (Int.ofNat debt.toNat)) := by
    simp only [evalExpr?, l1, store_get_self, EvalResult.ofOption]
  have hefactor : evalExpr? config { contract := contract, locals := l1, immutables := imms } evm
      (.var "liquidationIncentiveFactor") = .ok (.int (Int.ofNat (liquidationFactor p.lltv).toNat)) := by
    simp only [evalExpr?, l1, store_get_ne _ _ (show ("debtAssets" == "liquidationIncentiveFactor") = false by decide),
      hfactor, EvalResult.ofOption]
  by_cases hf2 : debt.toNat * (liquidationFactor p.lltv).toNat < UInt256.size
  swap
  · exact .reverted (ExecBlock.consRevert (ExecStmt.iteFalse hcond (ab1.run (ExecBlock.consRevert
      (morphoWMulDownCallReverts _ _ evm l1 imms _ _ "incentivized" hedebt hefactor (Nat.le_of_not_gt hf2))))))
      (morphoCheckedMulReverts (v := v) (by change R.length + 8 + 6 ≤ 1024; omega) (Nat.le_of_not_gt hf2) rd3)
  obtain ⟨k4, C4, rd4⟩ := morphoCheckedMulOk (v := v) (by change R.length + 8 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hf2 rd3
  let incentivized := wMulDownResult debt (liquidationFactor p.lltv)
  let l2 := l1.insert "incentivized" (.int (Int.ofNat incentivized.toNat))
  have hl2 : LiquidateLocals p account seized shares data l2 := hl1.insert _ _ (by decide) (by decide)
  have ab2 : ABlock config evm { contract := contract, locals := locals, immutables := imms }
      liquidateSharesBody { contract := contract, locals := l2, immutables := imms } (liquidateSharesBody.drop 2) :=
    advancePureBlock ab1 (morphoWMulDownCallOk _ _ evm l1 imms _ _ "incentivized" hedebt hefactor hf2)
  have hei : evalExpr? config { contract := contract, locals := l2, immutables := imms } evm
      (.var "incentivized") = .ok (.int (Int.ofNat incentivized.toNat)) := by
    simp only [evalExpr?, l2, store_get_self, EvalResult.ofOption]
  have heprice : evalExpr? config { contract := contract, locals := l2, immutables := imms } evm
      (.var "collateralPrice") = .ok (.int (Int.ofNat price.toNat)) := by
    simp only [evalExpr?, l2, l1, store_get_ne _ _ (show ("incentivized" == "collateralPrice") = false by decide),
      store_get_ne _ _ (show ("debtAssets" == "collateralPrice") = false by decide), hprice, EvalResult.ofOption]
  have hescale : evalExpr? config { contract := contract, locals := l2, immutables := imms } evm
      (.intLit 1000000000000000000000000000000000000) = .ok (.int (Int.ofNat oraclePriceScale.toNat)) := by
    simp only [evalExpr?, pure]; rfl
  by_cases hf3 : incentivized.toNat * oraclePriceScale.toNat < UInt256.size ∧ price ≠ ⟨0⟩
  swap
  · have hbad : UInt256.size ≤ incentivized.toNat * oraclePriceScale.toNat ∨ price = ⟨0⟩ := by
      by_cases hp : incentivized.toNat * oraclePriceScale.toNat < UInt256.size
      · exact .inr (Classical.not_not.mp (fun hn ↦ hf3 ⟨hp, hn⟩))
      · exact .inl (Nat.le_of_not_gt hp)
    exact .reverted (ExecBlock.consRevert (ExecStmt.iteFalse hcond (ab2.run (ExecBlock.consRevert
      (morphoMulDivDownCallReverts _ _ _ evm l2 imms _ _ _ "__c10" hei hescale heprice hbad)))))
      (morphoLiquidateScaleReverts (v := v) (by change R.length + 6 + 12 ≤ 1024; omega)
        (by change 3 ≤ R.length + 6; omega) hbad rd4)
  obtain ⟨k5, C5, rd5⟩ := morphoLiquidateScaleOk (v := v)
    (by change R.length + 6 + 12 ≤ 1024; omega) hf3.1 hf3.2 rd4
  have rd6 := morphoBlocks.morpho_block_3521 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 7 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd5
  let value := UInt256.div (UInt256.mul incentivized oraclePriceScale) price
  let l3 := l2.insert "__c10" (.int (Int.ofNat value.toNat))
  have hl3 : LiquidateLocals p account seized shares data l3 := hl2.insert _ _ (by decide) (by decide)
  have ab3 : ABlock config evm { contract := contract, locals := locals, immutables := imms }
      liquidateSharesBody { contract := contract, locals := l3, immutables := imms } (liquidateSharesBody.drop 3) :=
    advancePureBlock ab2 (morphoMulDivDownCallOk _ _ _ evm l2 imms _ _ _ "__c10" hei hescale heprice hf3.1 hf3.2)
  have hass : ExecStmt config { contract := contract, locals := l3, immutables := imms } evm
      liquidateSharesBody[3]!
      (.ok { contract := contract, locals := l3.insert "seizedAssets" (.int (Int.ofNat value.toNat)), immutables := imms } evm) :=
    ExecStmt.assign (by simp only [evalExpr?, l3, store_get_self, EvalResult.ofOption]) (assignLocalWord hl3.seized_eq)
  refine .ok ⟨fun tail ↦ ExecBlock.consNormal (ExecStmt.iteFalse hcond
    (ab3.run (ExecBlock.consNormal hass ExecBlock.nil))) tail⟩ (hl3.setSeized value) ?_ rd6
  simp only [l3, l2, l1, store_get_ne _ _ (show ("seizedAssets" == "__memory") = false by decide),
    store_get_ne _ _ (show ("__c10" == "__memory") = false by decide),
    store_get_ne _ _ (show ("incentivized" == "__memory") = false by decide),
    store_get_ne _ _ (show ("debtAssets" == "__memory") = false by decide)]

end Benchmarks.Morpho.MorphoBlue
