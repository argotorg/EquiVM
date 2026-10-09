import Benchmarks.CompoundIII.Comet.SupplyInternalSource
import Benchmarks.CompoundIII.Comet.VoidCallSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def supplyArgs (asset : AccountAddress) (amount : UInt256) : Store :=
  ((∅ : Store).insert "asset" (.address asset)).insert
    "amount" (.int amount.toNat)

theorem supplyTransition_body : supplyTransition.body = calldataPrologue
    [.internalCall "supplyInternal" [.env .caller, .env .caller, .env .caller, .var "asset",
      .var "amount"] "__c0", .return []] := rfl

theorem supply_source {v asset amount evm result}
    (ht : SupplyInternalTrace v evm.executionEnv.source evm.executionEnv.source
      evm.executionEnv.source asset amount evm result)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < 2^255 + 4) :
    explicitVoidSourceResult config
      { contract := contract, locals := supplyArgs asset amount, immutables := immStore v }
      evm supplyTransition.body result := by
  rw [supplyTransition_body]
  let frame := calldataLocalFrame
    { contract := contract, locals := supplyArgs asset amount, immutables := immStore v } evm
  apply voidCallPrologue_source hv hhi (final := frame) (ret := "__c0")
  apply supplyInternal_call ht frame (.env .caller) (.env .caller) (.env .caller) (.var "asset")
    (.var "amount") "__c0" rfl rfl
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, frame, calldataLocalFrame, supplyArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, supplyArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl

end Benchmarks.CompoundIII.Comet
