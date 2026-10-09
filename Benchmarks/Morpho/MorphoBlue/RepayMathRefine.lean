import Benchmarks.Morpho.MorphoBlue.SupplyMathRefine
import Benchmarks.Morpho.MorphoBlue.RepayMathReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive RepayMathRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (account srcOff len : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (σ : AccountMap) (mem : ByteArray) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (repayTransition.body.drop 11) .reverted → RDrev (deployedRuntime v) g s0 →
      RepayMathRefines v ee g s0 p account srcOff len data locals imms evm σ mem R
  | ok {assets' shares' locals' aw' k' C' out'} :
      ABlock config evm { contract := contract, locals := locals, immutables := imms }
        (repayTransition.body.drop 11) { contract := contract, locals := locals', immutables := imms }
        (repayTransition.body.drop 12) → SupplyLocals p assets' shares' account data locals' →
      locals'.get? "__memory" = locals.get? "__memory" →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10609)
        (repayUpdateTail p.id assets' shares' account srcOff len R)
        (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' out' σ k' C' →
      RepayMathRefines v ee g s0 p account srcOff len data locals imms evm σ mem R

theorem morphoRepayMathRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw assets shares account srcOff len : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (data : ByteArray)
    (locals imms : Store) (hstack : R.length + 28 ≤ 1024)
    (hl : SupplyLocals p assets shares account data locals) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10571)
      (repayAccrueTail p.id assets shares account srcOff len R) mem aw out σ k C) :
    RepayMathRefines v ee g s0 p account srcOff len data locals imms evm σ mem R := by
  have hea := hl.evalAssets imms evm
  have hes := hl.evalShares imms evm
  have het : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"market", [.mindex (.var "id"), .field "totalBorrowAssets"]⟩) =
      .ok (.int (Int.ofNat (marketFieldWord σ ee p.id 2).toNat)) := by
    simpa only [hs.env, ← hs.accounts] using hl.evalField imms evm ⟨2, by decide⟩
  have heq : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"market", [.mindex (.var "id"), .field "totalBorrowShares"]⟩) =
      .ok (.int (Int.ofNat (marketFieldWord σ ee p.id 3).toNat)) := by
    simpa only [hs.env, ← hs.accounts] using hl.evalField imms evm ⟨3, by decide⟩
  have hcond := evalExpr_uint256_var_positive (cfg := config)
    (frame := { contract := contract, locals := locals, immutables := imms }) evm "assets" assets hl.assets_eq
  by_cases hz : assets = ⟨0⟩
  · have hfalse : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
        (.binary .gt (.var "assets") (.intLit 0)) = .ok (.bool false) := by simpa only [hz, Nat.lt_irrefl, decide_false] using hcond
    obtain ⟨a1, k1, C1, rd1⟩ := morphoRepayReachAssets p hstack hz h
    by_cases hf : AssetsUpFits shares (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3)
    swap
    · exact .reverted (ExecBlock.consRevert (ExecStmt.iteFalse hfalse (ExecBlock.consRevert
        (morphoAssetsUpCallReverts _ _ _ evm locals imms _ _ _ "__c4" hes het heq hf))))
        (morphoAssetsUpReverts (v := v) (by change R.length + 11 + 14 ≤ 1024; omega) hf rd1)
    obtain ⟨k2, C2, rd2⟩ := morphoAssetsUpOk (v := v) (by change R.length + 11 + 14 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) hf rd1
    have rd3 := morphoBlocks.morpho_block_11034 (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 12 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    let value := assetsUpWord shares (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3)
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
    obtain ⟨a1, k1, C1, rd1⟩ := morphoRepayReachShares p hstack hz h
    by_cases hf : SharesDownFits assets (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3)
    swap
    · exact .reverted (ExecBlock.consRevert (ExecStmt.iteTrue htrue (ExecBlock.consRevert
        (morphoSharesDownCallReverts _ _ _ evm locals imms _ _ _ "__c3" hea het heq hf))))
        (morphoSharesDownReverts (v := v) (by change R.length + 11 + 12 ≤ 1024; omega) hf rd1)
    obtain ⟨k2, C2, rd2⟩ := morphoSharesDownOk (v := v) (by change R.length + 11 + 12 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) hf rd1
    have rd3 := morphoBlocks.morpho_block_10607 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 10 ≤ 1024; omega) rd2
    let value := sharesDownWord assets (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3)
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
