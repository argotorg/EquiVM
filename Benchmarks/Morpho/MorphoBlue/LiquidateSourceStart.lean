import Benchmarks.Morpho.MorphoBlue.LiquidateLocals
import Benchmarks.Morpho.MorphoBlue.LiquidateGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoLiquidatePrelude (p : MarketParamsWords) (account seized shares : UInt256) (data : ByteArray)
    (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm { contract := contract, locals := liquidateArgs p account seized shares data, immutables := imms }
      liquidateTransition.body (liquidateFrame p account seized shares data evm.executionEnv.calldata imms)
      (liquidateTransition.body.drop 4) := by
  refine ⟨fun h ↦ (calldataPrelude_ok hcv hsize).run (ExecBlock.consNormal ?_ h)⟩
  exact morphoMarketParamsIdCall p hc evm _ imms (.var "marketParams") "id"
    (by simp [evalExpr?, liquidateArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, EvalResult.ofOption])

theorem morphoLiquidateExactlyOneZero (p : MarketParamsWords) (account seized shares : UInt256)
    (data : ByteArray) (evm : EVM.State) (imms : Store) :
    ExecStmt config (liquidateFrame p account seized shares data evm.executionEnv.calldata imms) evm
      liquidateTransition.body[5]!
      (.ok (liquidateInputFrame p account seized shares data evm.executionEnv.calldata imms) evm) := by
  have hl := liquidateFrame_locals p account seized shares data evm.executionEnv.calldata imms
  apply morphoExactlyOneZeroCall
  have ha := hl.evalSeized imms evm
  have hs := hl.evalShares imms evm
  dsimp only [liquidateFrame] at ha hs
  simp only [evalExprs?, ha, hs, pure, bind, EvalResult.bind]

theorem morphoLiquidateSourceInput (p : MarketParamsWords) (account seized shares : UInt256) (data : ByteArray)
    (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : marketFieldWord evm.accountMap evm.executionEnv p.id 4 ≠ ⟨0⟩) :
    ABlock config evm { contract := contract, locals := liquidateArgs p account seized shares data, immutables := imms }
      liquidateTransition.body (liquidateInputFrame p account seized shares data evm.executionEnv.calldata imms)
      (liquidateTransition.body.drop 6) := by
  have hl := liquidateFrame_locals p account seized shares data evm.executionEnv.calldata imms
  have pref := (morphoLiquidatePrelude p account seized shares data hc evm imms hcv hsize).requireStep
    (by simpa only [decide_eq_true hg] using evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩))
  exact ⟨fun h ↦ pref.run (ExecBlock.consNormal (morphoLiquidateExactlyOneZero p account seized shares data evm imms) h)⟩

theorem liquidateInputFrame_eval_c1 (p : MarketParamsWords) (account seized shares : UInt256)
    (data cd : ByteArray) (evm : EVM.State) (imms : Store) :
    evalExpr? config (liquidateInputFrame p account seized shares data cd imms) evm (.var "__c1") =
      .ok (.bool (exactlyOneZero seized shares)) := by
  simp only [evalExpr?, liquidateInputFrame, store_get_self, EvalResult.ofOption]

theorem morphoLiquidateSourceGuards (p : MarketParamsWords) (account seized shares : UInt256) (data : ByteArray)
    (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : LiquidateGuards evm.accountMap evm.executionEnv p seized shares) :
    ABlock config evm { contract := contract, locals := liquidateArgs p account seized shares data, immutables := imms }
      liquidateTransition.body (liquidateBeforeAccrue p account seized shares data evm imms)
      (liquidateTransition.body.drop 8) := by
  have hl := liquidateInputFrame_locals p account seized shares data evm.executionEnv.calldata imms
  exact ((morphoLiquidateSourceInput p account seized shares data hc evm imms hcv hsize hg.1).requireStep
    (by rw [liquidateInputFrame_eval_c1, hg.2])).letStep
    (evalAccrueActive p _ imms evm hc hl.toMarketLocals)

theorem morphoLiquidateSourceReject (p : MarketParamsWords) (account seized shares : UInt256) (data : ByteArray)
    (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : ¬ LiquidateGuards evm.accountMap evm.executionEnv p seized shares) :
    ExecTransitionBody config contract evm (liquidateArgs p account seized shares data)
      liquidateTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  by_cases hcreated : marketFieldWord evm.accountMap evm.executionEnv p.id 4 ≠ ⟨0⟩
  swap
  · have hl := liquidateFrame_locals p account seized shares data evm.executionEnv.calldata imms
    exact (morphoLiquidatePrelude p account seized shares data hc evm imms hcv hsize).requireRevert
      (by simpa only [decide_eq_false hcreated] using evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩))
  have pref := morphoLiquidateSourceInput p account seized shares data hc evm imms hcv hsize hcreated
  exact pref.requireRevert (by rw [liquidateInputFrame_eval_c1,
    Bool.eq_false_iff.mpr (fun hz ↦ hg ⟨hcreated, hz⟩)])

end Benchmarks.Morpho.MorphoBlue
