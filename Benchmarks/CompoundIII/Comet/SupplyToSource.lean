import Benchmarks.CompoundIII.Comet.SupplyInternalSource
import Benchmarks.CompoundIII.Comet.VoidCallSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def supplyToArgs (dst asset : AccountAddress) (amount : UInt256) : Store :=
  (((∅ : Store).insert "dst" (.address dst)).insert "asset" (.address asset)).insert
    "amount" (.int amount.toNat)

theorem supplyToTransition_body : supplyToTransition.body = calldataPrologue
    [.internalCall "supplyInternal" [.env .caller, .env .caller, .var "dst", .var "asset",
      .var "amount"] "__c0", .return []] := rfl

theorem supplyTo_source {v dst asset amount evm result}
    (ht : SupplyInternalTrace v evm.executionEnv.source evm.executionEnv.source
      dst asset amount evm result)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < 2^255 + 4) :
    explicitVoidSourceResult config
      { contract := contract, locals := supplyToArgs dst asset amount, immutables := immStore v }
      evm supplyToTransition.body result := by
  rw [supplyToTransition_body]
  let frame := calldataLocalFrame
    { contract := contract, locals := supplyToArgs dst asset amount, immutables := immStore v } evm
  apply voidCallPrologue_source hv hhi (final := frame) (ret := "__c0")
  apply supplyInternal_call ht frame (.env .caller) (.env .caller) (.var "dst") (.var "asset")
    (.var "amount") "__c0" rfl rfl
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, frame, calldataLocalFrame, supplyToArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, supplyToArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, supplyToArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl

end Benchmarks.CompoundIII.Comet
