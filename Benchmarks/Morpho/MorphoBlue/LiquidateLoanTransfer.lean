import Benchmarks.Morpho.MorphoBlue.LiquidateCollateralTransfer
import Benchmarks.Morpho.MorphoBlue.ReturnBlockRefines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem liquidateLoanTransfer_args {p assets seized shares account badAssets badShares data locals fp}
    (hl : LiquidateEventLocals p account seized shares data assets badAssets badShares locals)
    (imms : Store) (evm : EVM.State)
    (hg : locals.get? "__c21" = some (.int (Int.ofNat fp))) :
    evalExprs? config { contract := contract, locals := locals, immutables := imms } evm
      [.tupleGet (.var "marketParams") 0, .env .caller, .env .this, .var "repaidAssets", .var "__c21"] =
      .ok (safeTransferArgs true (AccountAddress.ofNat p.loanToken.toNat)
        evm.executionEnv.source evm.executionEnv.codeOwner assets fp) := by
  have ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "marketParams") 0) = .ok (.address (AccountAddress.ofNat p.loanToken.toNat)) := by
    simp only [evalExpr?, hl.evalParams, MarketParamsWords.value, tupleGetValue?, EvalResult.bind, EvalResult.ofOption, bind]
    rfl
  simp only [evalExprs?, ht, hl.evalAssets, evalExpr?, envValue, hg, EvalResult.ofOption, pure, bind, EvalResult.bind]
  rfl

theorem morphoLiquidateLoanTransfer {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets seized shares account badAssets badShares x0 x1 x2 : UInt256} {out mem data : ByteArray}
    {σ : AccountMap} {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (hl : LiquidateEventLocals p account seized shares data assets badAssets badShares locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 0) (hsize : 128 ≤ mem.size) (hptr : 128 ≤ fp.toNat)
    (hget : locals.get? "__c21" = some (.int (Int.ofNat fp.toNat)))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (hloan : memLoad (UInt256.ofNat 128) mem = p.loanToken)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2710)
      [x0, x1, x2, assets, seized, UInt256.ofNat 128] mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (liquidateTransition.body.drop 34) liquidateTransition.returnType := by
  obtain ⟨a0, k0, C0, rd0⟩ := morphoBlocks.morpho_block_2710_packed (immWords := wordsOf (immStore v))
    (by decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_2710_stack] at rd0
  change RD _ _ _ _ _ [UInt256.land (memLoad (UInt256.ofNat 128) mem) solcAddrMask,
    UInt256.ofNat ee.source.val, UInt256.ofNat ee.codeOwner.val, assets, UInt256.ofNat 2752,
    assets, seized, UInt256.ofNat 64] _ _ _ _ _ _ at rd0
  rw [hloan, solcAddrMask_clean hc.1] at rd0
  let token := AccountAddress.ofNat p.loanToken.toNat
  have hw : UInt256.ofNat token.val = p.loanToken := addressWord_eq_ofNat_address hc.1
  rw [← hw] at rd0
  have he := liquidateLoanTransfer_args hl imms evm hget
  rw [hs.env] at he
  have hf := morphoSafeTransferFunctionRefine (v := v) (ret := UInt256.ofNat 2752)
    (R := [assets, seized, UInt256.ofNat 64]) true token ee.source ee.codeOwner imms
    (by change 24 ≤ 1024; decide) hs hm hsize hptr hzero (by rw [morphoPatchedValidJumps v]; jump_dest) rd0
  cases hf with
  | reverted hb hr =>
    exact .reverted (ExecBlock.consRevert (morphoSafeTransferInternalRevert true token ee.source ee.codeOwner
      assets fp.toNat locals imms evm _ "__c23" he hb)) hr
  | @ok frame' evm' σ' mem' fp' aw' out' k' C' hb hs1 hm1 hp1 hsiz1 hlo1 hz1 rd1 =>
    have he1 := morphoSafeTransferInternalOk true token ee.source ee.codeOwner assets fp.toNat
      locals imms evm evm' frame' _ _ "__c23" he hb
    have hl1 := hl.insert "__c23" (.int (Int.ofNat fp'.toNat)) (by decide) (by decide) (by decide)
    have hret : ExecBlock config
        { contract := contract, locals := locals.insert "__c23" (.int (Int.ofNat fp'.toNat)), immutables := imms }
        evm' (liquidateTransition.body.drop 35)
        (.returned { contract := contract, locals := locals.insert "__c23" (.int (Int.ofNat fp'.toNat)), immutables := imms }
          evm' (some [.int (Int.ofNat seized.toNat), .int (Int.ofNat assets.toNat)])) := by
      apply ExecBlock.consReturn (ExecStmt.return ?_)
      change evalExprs? config _ _ [.var "seizedAssets", .var "repaidAssets"] = _
      simp only [evalExprs?, hl1.evalSeized imms evm', hl1.evalAssets imms evm', pure, bind, EvalResult.bind]
    have hr := morphoBlocks.morpho_block_2752 (immWords := wordsOf (immStore v)) (by decide) rd1
    rw [hm1.free] at hr
    have hadd : (fp' + UInt256.ofNat 32).toNat = fp'.toNat + 32 :=
      uadd_word_ofNat_toNat _ _ (by have hh := hm1.space; change _ < 2 ^ 256; omega)
    rw [hadd] at hr
    have hr' : RDret (deployedRuntime v) g s0 σ' (returnWordBytes [seized, assets]) := by
      change RDret _ _ _ _ ((writeCascade mem' (returnWordWrites fp'.toNat [seized, assets])).readWithPadding
        fp'.toNat (32 * [seized, assets].length)) at hr
      rw [readReturnWords _ _ _ (by have hh := hm1.gap; omega)] at hr
      exact hr
    exact .ok (ExecBlock.consNormal he1 hret) hs1 (uint256PairReturnEncoding seized assets) hr'

end Benchmarks.Morpho.MorphoBlue
