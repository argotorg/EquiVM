import Benchmarks.Morpho.MorphoBlue.LiquidateEvent

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem liquidateCollateralTransfer_args {p assets seized shares account badAssets badShares data locals fp}
    (hl : LiquidateEventLocals p account seized shares data assets badAssets badShares locals)
    (imms : Store) (evm : EVM.State)
    (hg : locals.get? "__memory" = some (.int (Int.ofNat fp))) :
    evalExprs? config { contract := contract, locals := locals, immutables := imms } evm
      [.tupleGet (.var "marketParams") 1, .env .caller, .var "seizedAssets", .var "__memory"] =
      .ok (safeTransferArgs false (AccountAddress.ofNat p.collateralToken.toNat)
        evm.executionEnv.source evm.executionEnv.source seized fp) := by
  have ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "marketParams") 1) = .ok (.address (AccountAddress.ofNat p.collateralToken.toNat)) := by
    simp only [evalExpr?, hl.evalParams, MarketParamsWords.value, tupleGetValue?, EvalResult.bind, EvalResult.ofOption, bind]
    rfl
  simp only [evalExprs?, ht, hl.evalSeized, evalExpr?, envValue, hg, EvalResult.ofOption, pure, bind, EvalResult.bind]
  rfl

inductive LiquidateCollateralTransferRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets seized srcOff len : UInt256)
    (locals imms : Store) (evm : EVM.State) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 31) .reverted → RDrev (deployedRuntime v) g s0 →
      LiquidateCollateralTransferRefines v ee g s0 p assets seized srcOff len locals imms evm R
  | ok {evm' σ' mem' fp' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (liquidateTransition.body.drop 31)
        { contract := contract, locals := locals.insert "__c21" (.int (Int.ofNat fp'.toNat)), immutables := imms }
        evm' (liquidateTransition.body.drop 33) →
      SourceState s0 ee σ' evm' → MorphoHeap mem' fp' 0 → 192 ≤ mem'.size → 192 ≤ fp'.toNat →
      memLoad (UInt256.ofNat 96) mem' = UInt256.ofNat 0 →
      memLoad (UInt256.ofNat 128) mem' = p.loanToken →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2704)
        (liquidateTransferTail assets seized srcOff len R) mem' aw' out' σ' k' C' →
      LiquidateCollateralTransferRefines v ee g s0 p assets seized srcOff len locals imms evm R

theorem morphoLiquidateCollateralTransfer {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp trash assets seized shares account badAssets badShares srcOff len : UInt256} {out mem data : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (locals imms : Store)
    (hc : p.Canonical) (hstack : R.length + 40 ≤ 1024) (hperm : ee.perm = true)
    (hl : LiquidateEventLocals p account seized shares data assets badAssets badShares locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 384) (hsize : 192 ≤ mem.size) (hptr : 192 ≤ fp.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat fp.toNat)))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (hloan : memLoad (UInt256.ofNat 128) mem = p.loanToken)
    (htoken : memLoad (UInt256.ofNat 160) mem = p.collateralToken)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2574)
      (liquidateEventTail trash p.id assets seized shares badAssets badShares srcOff len R) mem aw out σ k C) :
    LiquidateCollateralTransferRefines v ee g s0 p assets seized srcOff len locals imms evm R := by
  have hab : StateBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 31) { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 32) := StateBlock.start.step (liquidateEmit p _ _ _ _ _ _ data locals imms evm hl)
  obtain ⟨a0, k0, C0, rd0⟩ := morphoLiquidateEvent (v := v) (by omega) hperm hm h
  obtain ⟨hm0, hp0⟩ := liquidateEvent_heap hm (by decide) assets shares seized badAssets badShares
  have ht0 := memoryPrefix_memLoad hp0 (UInt256.ofNat 160) (by decide) hptr hsize
  have hz0 : memLoad (UInt256.ofNat 96) (liquidateEventMem mem fp assets shares seized badAssets badShares) = UInt256.ofNat 0 := by
    rw [memoryPrefix_memLoad hp0 (UInt256.ofNat 96) (by decide) (by change 128 ≤ fp.toNat; omega) (by change 128 ≤ mem.size; omega)]
    exact hzero
  rw [ht0, htoken, solcAddrMask_clean hc.2.1] at rd0
  let token := AccountAddress.ofNat p.collateralToken.toNat
  have hw : UInt256.ofNat token.val = p.collateralToken := addressWord_eq_ofNat_address hc.2.1
  rw [← hw] at rd0
  have he := liquidateCollateralTransfer_args hl imms evm hget
  rw [hs.env] at he
  have hf := morphoSafeTransferFunctionRefineAt (v := v) (ret := UInt256.ofNat 2704)
    (R := liquidateTransferTail assets seized srcOff len R) false token ee.source ee.source imms
    (by change R.length + 6 + 21 ≤ 1024; omega) hs (hm0.weaken (by decide))
    (by have hh := hp0.size; omega) (by omega) 192 hptr hz0
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd0
  cases hf with
  | reverted hb hr =>
    exact .reverted (hab.reverts (morphoSafeTransferInternalRevert false token ee.source ee.source
      seized fp.toNat locals imms evm _ "__c21" he hb)) hr
  | ok hb hs1 hm1 hp1 hsiz1 hlo1 hz1 rd1 =>
    have he1 := morphoSafeTransferInternalOk false token ee.source ee.source seized fp.toNat
      locals imms evm _ _ _ _ "__c21" he hb
    have hp := hp0.trans hp1
    refine .ok (hab.step he1) hs1 hm1 (le_trans hsize hp.size) hlo1 hz1 ?_ rd1
    rw [memoryPrefix_memLoad hp (UInt256.ofNat 128) (by decide) (by change 160 ≤ fp.toNat; omega) (by change 160 ≤ mem.size; omega)]
    exact hloan

end Benchmarks.Morpho.MorphoBlue
