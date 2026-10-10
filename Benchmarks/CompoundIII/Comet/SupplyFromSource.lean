import Benchmarks.CompoundIII.Comet.SupplyInternalSource
import Benchmarks.CompoundIII.Comet.VoidCallSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def supplyFromArgs (sender dst asset : AccountAddress) (amount : UInt256) : Store :=
  ((((∅ : Store).insert "from" (.address sender)).insert "dst" (.address dst)).insert "asset" (.address asset)).insert
    "amount" (.int amount.toNat)

theorem supplyFromTransition_body : supplyFromTransition.body = calldataPrologue
    [.internalCall "supplyInternal" [.env .caller, .var "from", .var "dst", .var "asset",
      .var "amount"] "__c0", .return []] := rfl

theorem supplyFrom_source {v sender dst asset amount evm result}
    (ht : SupplyInternalTrace v evm.executionEnv.source sender
      dst asset amount evm result)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < 2^255 + 4) :
    explicitVoidSourceResult config
      { contract := contract, locals := supplyFromArgs sender dst asset amount, immutables := immStore v }
      evm supplyFromTransition.body result := by
  rw [supplyFromTransition_body]
  let frame := calldataLocalFrame
    { contract := contract, locals := supplyFromArgs sender dst asset amount, immutables := immStore v } evm
  apply voidCallPrologue_source hv hhi (final := frame) (ret := "__c0")
  apply supplyInternal_call ht frame (.env .caller) (.var "from") (.var "dst") (.var "asset")
    (.var "amount") "__c0" rfl rfl
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, frame, calldataLocalFrame, supplyFromArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, supplyFromArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, supplyFromArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, supplyFromArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl

end Benchmarks.CompoundIII.Comet
