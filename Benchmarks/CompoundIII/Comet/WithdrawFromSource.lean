import Benchmarks.CompoundIII.Comet.WithdrawInternalSource
import Benchmarks.CompoundIII.Comet.VoidCallSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def withdrawFromArgs (src recipient asset : AccountAddress) (amount : UInt256) : Store :=
  ((((∅ : Store).insert "src" (.address src)).insert "to" (.address recipient)).insert "asset" (.address asset)).insert
    "amount" (.int amount.toNat)

theorem withdrawFromTransition_body : withdrawFromTransition.body = calldataPrologue
    [.internalCall "withdrawInternal" [.env .caller, .var "src", .var "to", .var "asset",
      .var "amount"] "__c0", .return []] := rfl

theorem withdrawFrom_source {v src recipient asset amount evm result}
    (ht : WithdrawInternalTrace v evm.executionEnv.source src
      recipient asset amount evm result)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < 2^255 + 4) :
    explicitVoidSourceResult config
      { contract := contract, locals := withdrawFromArgs src recipient asset amount, immutables := immStore v }
      evm withdrawFromTransition.body result := by
  rw [withdrawFromTransition_body]
  let frame := calldataLocalFrame
    { contract := contract, locals := withdrawFromArgs src recipient asset amount, immutables := immStore v } evm
  apply voidCallPrologue_source hv hhi (final := frame) (ret := "__c0")
  apply withdrawInternal_call ht frame (.env .caller) (.var "src") (.var "to") (.var "asset")
    (.var "amount") "__c0" rfl rfl
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, frame, calldataLocalFrame, withdrawFromArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, withdrawFromArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, withdrawFromArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, withdrawFromArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl

end Benchmarks.CompoundIII.Comet
