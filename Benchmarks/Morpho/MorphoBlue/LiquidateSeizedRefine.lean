import Benchmarks.Morpho.MorphoBlue.LiquidateAmountRefines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoLiquidateSeizedRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw account seized shares price srcOff len : UInt256} {out mem data : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 40 ≤ 1024) (hl : LiquidateLocals p account seized shares data locals)
    (hs : SourceState s0 ee σ evm) (hlltv : p.lltv.toNat ≤ wad.toNat) (hn : seized ≠ ⟨0⟩)
    (hprice : locals.get? "collateralPrice" = some (.int (Int.ofNat price.toNat)))
    (hfactor : locals.get? "liquidationIncentiveFactor" = some (.int (Int.ofNat (liquidationFactor p.lltv).toNat)))
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1743)
      (liquidateMathStack p.id seized shares price (liquidationDenom p.lltv) srcOff len R) mem aw out σ k C) :
    LiquidateAmountRefines v ee g s0 p account srcOff len data locals imms evm σ mem R := by
  have hcond : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .gt (.var "seizedAssets") (.intLit 0)) = .ok (.bool true) := by
    have hp : 0 < seized.toNat := Nat.pos_of_ne_zero (fun hz ↦ hn (uint256_toNat_eq_zero hz))
    simpa only [decide_eq_true hp] using evalExpr_uint256_var_positive (cfg := config)
      (frame := { contract := contract, locals := locals, immutables := imms }) evm "seizedAssets" seized hl.seized_eq
  have heprice : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "collateralPrice") = .ok (.int (Int.ofNat price.toNat)) := by
    simp only [evalExpr?, hprice, EvalResult.ofOption]
  have hescale : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.intLit 1000000000000000000000000000000000000) = .ok (.int (Int.ofNat oraclePriceScale.toNat)) := by
    simp only [evalExpr?, pure]; rfl
  by_cases hf1 : MulDivUpFits seized price oraclePriceScale
  swap
  · exact .reverted (ExecBlock.consRevert (ExecStmt.iteTrue hcond (ExecBlock.consRevert
      (morphoMulDivUpCallReverts _ _ _ evm locals imms _ _ _ "seizedAssetsQuoted"
        (hl.evalSeized imms evm) heprice hescale hf1))))
      (morphoLiquidateQuotedReverts (v := v) (by omega) hn hf1 h)
  obtain ⟨k1, C1, rd1⟩ := morphoLiquidateQuotedOk (v := v) (by omega) hn hf1 h
  let q := mulDivUpWord seized price oraclePriceScale
  let l1 := locals.insert "seizedAssetsQuoted" (.int (Int.ofNat q.toNat))
  have hl1 : LiquidateLocals p account seized shares data l1 := hl.insert _ _ (by decide) (by decide)
  have ab1 : ABlock config evm { contract := contract, locals := locals, immutables := imms }
      liquidateSeizedBody { contract := contract, locals := l1, immutables := imms } (liquidateSeizedBody.drop 1) :=
    advancePureBlock ABlock.start (morphoMulDivUpCallOk _ _ _ evm locals imms _ _ _ "seizedAssetsQuoted"
      (hl.evalSeized imms evm) heprice hescale hf1)
  have heq : evalExpr? config { contract := contract, locals := l1, immutables := imms } evm
      (.var "seizedAssetsQuoted") = .ok (.int (Int.ofNat q.toNat)) := by
    simp only [evalExpr?, l1, store_get_self, EvalResult.ofOption]
  have hefactor : evalExpr? config { contract := contract, locals := l1, immutables := imms } evm
      (.var "liquidationIncentiveFactor") = .ok (.int (Int.ofNat (liquidationFactor p.lltv).toNat)) := by
    simp only [evalExpr?, l1, store_get_ne _ _ (show ("seizedAssetsQuoted" == "liquidationIncentiveFactor") = false by decide),
      hfactor, EvalResult.ofOption]
  by_cases hf2 : MulDivUpFits q wad (liquidationFactor p.lltv)
  swap
  · exact .reverted (ExecBlock.consRevert (ExecStmt.iteTrue hcond (ab1.run (ExecBlock.consRevert
      (morphoWDivUpCallReverts _ _ evm l1 imms _ _ "quotedAssets" heq hefactor hf2)))))
      (morphoLiquidateWDivReverts (v := v) (by change R.length + 6 + 14 ≤ 1024; omega) hlltv hf2 rd1)
  obtain ⟨k2, C2, rd2⟩ := morphoLiquidateWDivOk (v := v)
    (by change R.length + 6 + 14 ≤ 1024; omega) hlltv hf2 rd1
  let quote := wDivUpResult q (liquidationFactor p.lltv)
  let l2 := l1.insert "quotedAssets" (.int (Int.ofNat quote.toNat))
  have hl2 : LiquidateLocals p account seized shares data l2 := hl1.insert _ _ (by decide) (by decide)
  have ab2 : ABlock config evm { contract := contract, locals := locals, immutables := imms }
      liquidateSeizedBody { contract := contract, locals := l2, immutables := imms } (liquidateSeizedBody.drop 2) :=
    advancePureBlock ab1 (morphoWDivUpCallOk _ _ evm l1 imms _ _ "quotedAssets" heq hefactor hf2)
  have hequote : evalExpr? config { contract := contract, locals := l2, immutables := imms } evm
      (.var "quotedAssets") = .ok (.int (Int.ofNat quote.toNat)) := by
    simp only [evalExpr?, l2, store_get_self, EvalResult.ofOption]
  have heassets := hl2.evalField imms evm ⟨2, by decide⟩
  have heshares := hl2.evalField imms evm ⟨3, by decide⟩
  rw [hs.env, ← hs.accounts] at heassets heshares
  obtain ⟨a3, k3, C3, rd3⟩ := morphoLiquidateReachShares (v := v) (by omega) rd2
  by_cases hf3 : SharesUpFits quote (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3)
  swap
  · exact .reverted (ExecBlock.consRevert (ExecStmt.iteTrue hcond (ab2.run (ExecBlock.consRevert
      (morphoSharesUpCallReverts _ _ _ evm l2 imms _ _ _ "__c9" hequote heassets heshares hf3)))))
      (morphoSharesUpReverts (v := v) (by change R.length + 6 + 14 ≤ 1024; omega) hf3 rd3)
  obtain ⟨k4, C4, rd4⟩ := morphoSharesUpOk (v := v) (by change R.length + 6 + 14 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hf3 rd3
  have rd5 := morphoBlocks.morpho_block_2055 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 5 ≤ 1024; omega) rd4
  let value := sharesUpWord quote (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3)
  let l3 := l2.insert "__c9" (.int (Int.ofNat value.toNat))
  have hl3 : LiquidateLocals p account seized shares data l3 := hl2.insert _ _ (by decide) (by decide)
  have ab3 : ABlock config evm { contract := contract, locals := locals, immutables := imms }
      liquidateSeizedBody { contract := contract, locals := l3, immutables := imms } (liquidateSeizedBody.drop 3) :=
    advancePureBlock ab2 (morphoSharesUpCallOk _ _ _ evm l2 imms _ _ _ "__c9" hequote heassets heshares hf3)
  have hass : ExecStmt config { contract := contract, locals := l3, immutables := imms } evm
      liquidateSeizedBody[3]!
      (.ok { contract := contract, locals := l3.insert "repaidShares" (.int (Int.ofNat value.toNat)), immutables := imms } evm) :=
    ExecStmt.assign (by simp only [evalExpr?, l3, store_get_self, EvalResult.ofOption]) (assignLocalWord hl3.shares_eq)
  refine .ok ⟨fun tail ↦ ExecBlock.consNormal (ExecStmt.iteTrue hcond
    (ab3.run (ExecBlock.consNormal hass ExecBlock.nil))) tail⟩ (hl3.setShares value) ?_ rd5
  simp only [l3, l2, l1, store_get_ne _ _ (show ("repaidShares" == "__memory") = false by decide),
    store_get_ne _ _ (show ("__c9" == "__memory") = false by decide),
    store_get_ne _ _ (show ("quotedAssets" == "__memory") = false by decide),
    store_get_ne _ _ (show ("seizedAssetsQuoted" == "__memory") = false by decide)]

end Benchmarks.Morpho.MorphoBlue
