import Benchmarks.CompoundIII.Comet.TransferInternalSource
import Benchmarks.CompoundIII.Comet.VoidCallSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def transferAssetFromArgs (src dst asset : AccountAddress) (amount : UInt256) : Store :=
  ((((∅ : Store).insert "src" (.address src)).insert "dst" (.address dst)).insert "asset" (.address asset)).insert
    "amount" (.int amount.toNat)

theorem transferAssetFromTransition_body : transferAssetFromTransition.body = calldataPrologue
    [.internalCall "transferInternal" [.env .caller, .var "src", .var "dst", .var "asset",
      .var "amount"] "__c0", .return []] := rfl

theorem transferAssetFrom_source {v src dst asset amount evm result}
    (ht : TransferInternalTrace v evm.executionEnv.source src
      dst asset amount evm result)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < 2^255 + 4) :
    explicitVoidSourceResult config
      { contract := contract, locals := transferAssetFromArgs src dst asset amount, immutables := immStore v }
      evm transferAssetFromTransition.body result := by
  rw [transferAssetFromTransition_body]
  let frame := calldataLocalFrame
    { contract := contract, locals := transferAssetFromArgs src dst asset amount, immutables := immStore v } evm
  apply voidCallPrologue_source hv hhi (final := frame) (ret := "__c0")
  apply transferInternal_call ht frame (.env .caller) (.var "src") (.var "dst") (.var "asset")
    (.var "amount") "__c0" rfl rfl
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, frame, calldataLocalFrame, transferAssetFromArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, transferAssetFromArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, transferAssetFromArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, transferAssetFromArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl

end Benchmarks.CompoundIII.Comet
