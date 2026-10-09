import Benchmarks.CompoundIII.Comet.WithdrawInternalSource
import Benchmarks.CompoundIII.Comet.VoidCallSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def withdrawToArgs (recipient asset : AccountAddress) (amount : UInt256) : Store :=
  (((∅ : Store).insert "to" (.address recipient)).insert "asset" (.address asset)).insert
    "amount" (.int amount.toNat)

theorem withdrawToTransition_body : withdrawToTransition.body = calldataPrologue
    [.internalCall "withdrawInternal" [.env .caller, .env .caller, .var "to", .var "asset",
      .var "amount"] "__c0", .return []] := rfl

theorem withdrawTo_source {v recipient asset amount evm result}
    (ht : WithdrawInternalTrace v evm.executionEnv.source evm.executionEnv.source
      recipient asset amount evm result)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < 2^255 + 4) :
    explicitVoidSourceResult config
      { contract := contract, locals := withdrawToArgs recipient asset amount, immutables := immStore v }
      evm withdrawToTransition.body result := by
  rw [withdrawToTransition_body]
  let frame := calldataLocalFrame
    { contract := contract, locals := withdrawToArgs recipient asset amount, immutables := immStore v } evm
  apply voidCallPrologue_source hv hhi (final := frame) (ret := "__c0")
  apply withdrawInternal_call ht frame (.env .caller) (.env .caller) (.var "to") (.var "asset")
    (.var "amount") "__c0" rfl rfl
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, frame, calldataLocalFrame, withdrawToArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, withdrawToArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, withdrawToArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl

end Benchmarks.CompoundIII.Comet
