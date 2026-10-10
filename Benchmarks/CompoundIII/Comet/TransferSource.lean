import Benchmarks.CompoundIII.Comet.TransferInternalSource
import Benchmarks.CompoundIII.Comet.CallReturnSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def transferArgs (dst : AccountAddress) (amount : UInt256) : Store :=
  ((∅ : Store).insert "dst" (.address dst)).insert "amount" (.int amount.toNat)

theorem transferTransition_body : transferTransition.body = calldataPrologue
    [.internalCall "transferInternal" [.env .caller, .env .caller, .var "dst",
      .immutable "baseToken", .var "amount"] "__c0", .return [.boolLit true]] := rfl

theorem transfer_source {v dst amount evm result}
    (ht : TransferInternalTrace v evm.executionEnv.source evm.executionEnv.source
      dst v.baseToken amount evm result)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < 2^255 + 4) :
    explicitSourceResult config
      { contract := contract, locals := transferArgs dst amount, immutables := immStore v }
      evm transferTransition.body [.bool true] result := by
  rw [transferTransition_body]
  let frame := calldataLocalFrame
    { contract := contract, locals := transferArgs dst amount, immutables := immStore v } evm
  apply callReturnPrologue_source hv hhi (final := frame) (ret := "__c0")
    (fun _ ↦ by simp only [evalExprs?, evalExpr?, pure, bind, EvalResult.bind])
  apply transferInternal_call ht frame (.env .caller) (.env .caller) (.var "dst")
    (.immutable "baseToken") (.var "amount") "__c0" rfl rfl
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, frame, calldataLocalFrame, transferArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, immStore_get_baseToken, EvalResult.ofOption]
  · simp only [evalExpr?, frame, calldataLocalFrame, transferArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl

end Benchmarks.CompoundIII.Comet
