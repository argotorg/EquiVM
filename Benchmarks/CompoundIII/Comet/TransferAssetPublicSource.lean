import Benchmarks.CompoundIII.Comet.TransferInternalSource
import Benchmarks.CompoundIII.Comet.VoidCallSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def transferAssetArgs (dst asset : AccountAddress) (amount : UInt256) : Store :=
  (((∅ : Store).insert "dst" (.address dst)).insert "asset" (.address asset)).insert
    "amount" (.int amount.toNat)

theorem transferAssetTransition_body : transferAssetTransition.body = calldataPrologue
    [.internalCall "transferInternal" [.env .caller, .env .caller, .var "dst", .var "asset",
      .var "amount"] "__c0", .return []] := rfl

theorem transferAssetPublic_source {v dst asset amount evm result}
    (ht : TransferInternalTrace v evm.executionEnv.source evm.executionEnv.source
      dst asset amount evm result)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < 2^255 + 4) :
    explicitVoidSourceResult config
      { contract := contract, locals := transferAssetArgs dst asset amount, immutables := immStore v }
      evm transferAssetTransition.body result := by
  rw [transferAssetTransition_body]
  let frame := calldataLocalFrame
    { contract := contract, locals := transferAssetArgs dst asset amount, immutables := immStore v } evm
  apply voidCallPrologue_source hv hhi (final := frame) (ret := "__c0")
  apply transferInternal_call ht frame (.env .caller) (.env .caller) (.var "dst") (.var "asset")
    (.var "amount") "__c0" rfl rfl
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, frame, calldataLocalFrame, transferAssetArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, transferAssetArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, transferAssetArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl

end Benchmarks.CompoundIII.Comet
