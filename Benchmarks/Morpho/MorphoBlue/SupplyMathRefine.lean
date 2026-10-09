import Benchmarks.Morpho.MorphoBlue.SupplyMathReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem SupplyLocals.setShares {p assets shares account data locals}
    (hl : SupplyLocals p assets shares account data locals) (newShares : UInt256) :
    SupplyLocals p assets newShares account data (locals.insert "shares" (.int (Int.ofNat newShares.toNat))) :=
  ⟨hl.toSupplyCollateralLocals.insert _ _ (by decide) (by decide), store_get_self _ _ _⟩

theorem SupplyLocals.setAssets {p assets shares account data locals}
    (hl : SupplyLocals p assets shares account data locals) (newAssets : UInt256) :
    SupplyLocals p newAssets shares account data (locals.insert "assets" (.int (Int.ofNat newAssets.toNat))) := by
  refine ⟨⟨hl.toMarketLocals.insert _ _ (by decide), store_get_self _ _ _, ?_, ?_⟩, ?_⟩
  · rw [store_get_ne _ _ (by decide)]; exact hl.account_eq
  · rw [store_get_ne _ _ (by decide)]; exact hl.data_eq
  · rw [store_get_ne _ _ (by decide)]; exact hl.shares_eq

inductive SupplyMathRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (account srcOff len : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (σ : AccountMap) (mem : ByteArray) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (supplyTransition.body.drop 11) .reverted → RDrev (deployedRuntime v) g s0 →
      SupplyMathRefines v ee g s0 p account srcOff len data locals imms evm σ mem R
  | ok {assets' shares' locals' aw' k' C' out'} :
      ABlock config evm { contract := contract, locals := locals, immutables := imms }
        (supplyTransition.body.drop 11) { contract := contract, locals := locals', immutables := imms }
        (supplyTransition.body.drop 12) → SupplyLocals p assets' shares' account data locals' →
      locals'.get? "__memory" = locals.get? "__memory" →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3984)
        (supplyUpdateTail p.id assets' shares' account srcOff len R)
        (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' out' σ k' C' →
      SupplyMathRefines v ee g s0 p account srcOff len data locals imms evm σ mem R

theorem morphoSupplyMathRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw assets shares account srcOff len : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (data : ByteArray)
    (locals imms : Store) (hstack : R.length + 28 ≤ 1024)
    (hl : SupplyLocals p assets shares account data locals) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3948)
      (supplyAccrueTail p.id assets shares account srcOff len R) mem aw out σ k C) :
    SupplyMathRefines v ee g s0 p account srcOff len data locals imms evm σ mem R := by
  have hea := hl.evalAssets imms evm
  have hes := hl.evalShares imms evm
  have het : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"market", [.mindex (.var "id"), .field "totalSupplyAssets"]⟩) =
      .ok (.int (Int.ofNat (marketFieldWord σ ee p.id 0).toNat)) := by
    simpa only [hs.env, ← hs.accounts] using hl.evalField imms evm ⟨0, by decide⟩
  have heq : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"market", [.mindex (.var "id"), .field "totalSupplyShares"]⟩) =
      .ok (.int (Int.ofNat (marketFieldWord σ ee p.id 1).toNat)) := by
    simpa only [hs.env, ← hs.accounts] using hl.evalField imms evm ⟨1, by decide⟩
  have hcond := evalExpr_uint256_var_positive (cfg := config)
    (frame := { contract := contract, locals := locals, immutables := imms }) evm "assets" assets hl.assets_eq
  by_cases hz : assets = ⟨0⟩
  · have hfalse : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
        (.binary .gt (.var "assets") (.intLit 0)) = .ok (.bool false) := by simpa only [hz, Nat.lt_irrefl, decide_false] using hcond
    obtain ⟨a1, k1, C1, rd1⟩ := morphoSupplyReachAssets p hstack hz h
    by_cases hf : AssetsUpFits shares (marketFieldWord σ ee p.id 0) (marketFieldWord σ ee p.id 1)
    swap
    · exact .reverted (ExecBlock.consRevert (ExecStmt.iteFalse hfalse (ExecBlock.consRevert
        (morphoAssetsUpCallReverts _ _ _ evm locals imms _ _ _ "__c4" hes het heq hf))))
        (morphoAssetsUpReverts (v := v) (by change R.length + 10 + 14 ≤ 1024; omega) hf rd1)
    obtain ⟨k2, C2, rd2⟩ := morphoAssetsUpOk (v := v) (by change R.length + 10 + 14 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) hf rd1
    have rd3 := morphoBlocks.morpho_block_4360 (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 11 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    let value := assetsUpWord shares (marketFieldWord σ ee p.id 0) (marketFieldWord σ ee p.id 1)
    have hcall := morphoAssetsUpCallOk _ _ _ evm locals imms _ _ _ "__c4" hes het heq hf
    have hl1 := hl.insert "__c4" (.int (Int.ofNat value.toNat)) (by decide) (by decide)
    have hass : ExecStmt config
        { contract := contract, locals := locals.insert "__c4" (.int (Int.ofNat value.toNat)), immutables := imms }
        evm (.assign .localVar ⟨"assets", []⟩ (.var "__c4"))
        (.ok { contract := contract, immutables := imms,
                locals := (locals.insert "__c4" (.int (Int.ofNat value.toNat))).insert "assets" (.int (Int.ofNat value.toNat)) } evm) :=
      ExecStmt.assign (by simp only [evalExpr?, store_get_self, EvalResult.ofOption]) (assignLocalWord hl1.assets_eq)
    refine .ok ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.iteFalse hfalse
      (ExecBlock.consNormal hcall (ExecBlock.consNormal hass ExecBlock.nil))) h⟩ (hl1.setAssets value) ?_ rd3
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  · have hp : 0 < assets.toNat := Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h))
    have htrue : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
        (.binary .gt (.var "assets") (.intLit 0)) = .ok (.bool true) := by simpa only [decide_eq_true hp] using hcond
    obtain ⟨a1, k1, C1, rd1⟩ := morphoSupplyReachShares p hstack hz h
    by_cases hf : SharesDownFits assets (marketFieldWord σ ee p.id 0) (marketFieldWord σ ee p.id 1)
    swap
    · exact .reverted (ExecBlock.consRevert (ExecStmt.iteTrue htrue (ExecBlock.consRevert
        (morphoSharesDownCallReverts _ _ _ evm locals imms _ _ _ "__c3" hea het heq hf))))
        (morphoSharesDownReverts (v := v) (by change R.length + 10 + 12 ≤ 1024; omega) hf rd1)
    obtain ⟨k2, C2, rd2⟩ := morphoSharesDownOk (v := v) (by change R.length + 10 + 12 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) hf rd1
    have rd3 := morphoBlocks.morpho_block_3982 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 9 ≤ 1024; omega) rd2
    let value := sharesDownWord assets (marketFieldWord σ ee p.id 0) (marketFieldWord σ ee p.id 1)
    have hcall := morphoSharesDownCallOk _ _ _ evm locals imms _ _ _ "__c3" hea het heq hf
    have hl1 := hl.insert "__c3" (.int (Int.ofNat value.toNat)) (by decide) (by decide)
    have hass : ExecStmt config
        { contract := contract, locals := locals.insert "__c3" (.int (Int.ofNat value.toNat)), immutables := imms }
        evm (.assign .localVar ⟨"shares", []⟩ (.var "__c3"))
        (.ok { contract := contract, immutables := imms,
                locals := (locals.insert "__c3" (.int (Int.ofNat value.toNat))).insert "shares" (.int (Int.ofNat value.toNat)) } evm) :=
      ExecStmt.assign (by simp only [evalExpr?, store_get_self, EvalResult.ofOption]) (assignLocalWord hl1.shares_eq)
    refine .ok ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.iteTrue htrue
      (ExecBlock.consNormal hcall (ExecBlock.consNormal hass ExecBlock.nil))) h⟩ (hl1.setShares value) ?_ rd3
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]

end Benchmarks.Morpho.MorphoBlue
