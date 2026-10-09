import Benchmarks.Morpho.MorphoBlue.VoidBlockRefines
import Benchmarks.Morpho.MorphoBlue.SupplyCollateralEvent
import Benchmarks.Morpho.MorphoBlue.SafeTransferFunctionRefine
import Benchmarks.Morpho.MorphoBlue.SafeTransferInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem supplyCollateralTransfer_args {p assets account data locals}
    (hl : SupplyCollateralLocals p assets account data locals) (imms : Store) (evm : EVM.State) :
    evalExprs? config { contract := contract, locals := locals, immutables := imms } evm
      [.tupleGet (.var "marketParams") 1, .env .caller, .env .this, .var "assets", .intLit 544] =
      .ok (safeTransferArgs true (AccountAddress.ofNat p.collateralToken.toNat)
        evm.executionEnv.source evm.executionEnv.codeOwner assets 544) := by
  have ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "marketParams") 1) = .ok (.address (AccountAddress.ofNat p.collateralToken.toNat)) := by
    simp only [evalExpr?, hl.evalParams, MarketParamsWords.value, tupleGetValue?,
      EvalResult.bind, EvalResult.ofOption, bind]
    rfl
  simp only [evalExprs?, ht, hl.evalAssets, evalExpr?, envValue,
    EvalResult.ofOption, pure, bind, EvalResult.bind]
  rfl

theorem morphoSupplyCollateralTransfer {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out data : ByteArray} {aw assets account x0 x1 : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (hl : SupplyCollateralLocals p assets account data locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem (UInt256.ofNat 544) 0) (hsize : 192 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (htoken : memLoad (UInt256.ofNat 160) mem = p.collateralToken)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10286)
      [x0, x1, solcAddrMask, assets, UInt256.ofNat 0, UInt256.ofNat 128] mem aw out σ k C) :
    VoidBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm (supplyCollateralTransition.body.drop 11) := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_10286_packed
    (immWords := wordsOf (immStore v)) (by decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_10286_stack] at rd1
  rw [show UInt256.ofNat 128 + UInt256.ofNat 32 = UInt256.ofNat 160 from rfl,
    htoken, solcAddrMask_clean hc.2.1] at rd1
  let token := AccountAddress.ofNat p.collateralToken.toNat
  have hw : UInt256.ofNat token.val = p.collateralToken := addressWord_eq_ofNat_address hc.2.1
  rw [← hw] at rd1
  have he := supplyCollateralTransfer_args hl imms evm
  rw [hs.env] at he
  have hf := morphoSafeTransferFunctionRefine (v := v) true token ee.source ee.codeOwner imms
    (by decide) hs hm (by omega) (by decide) hzero (by rw [morphoPatchedValidJumps v]; jump_dest) rd1
  cases hf with
  | reverted hb hr =>
    exact .reverted (ExecBlock.consRevert (morphoSafeTransferInternalRevert true token ee.source ee.codeOwner
      assets 544 locals imms evm _ "__c3" he hb)) hr
  | @ok frame' evm' σ' mem' ptr' aw' rdata' k' C' hb hs' hm' hpref hsize' hlower' hzero' rd =>
    have he' := morphoSafeTransferInternalOk true token ee.source ee.codeOwner assets 544
      locals imms evm evm' frame' _ _ "__c3" he hb
    have hr := morphoBlocks.morpho_block_1211 (immWords := wordsOf (immStore v)) (by decide) rd
    exact .ok (ExecBlock.consNormal he' ExecBlock.nil) hs'
      (by simpa only [show (UInt256.ofNat 0).toNat = 0 from rfl, byteArray_readWithPadding_zero] using hr)

end Benchmarks.Morpho.MorphoBlue
