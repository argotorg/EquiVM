import Benchmarks.CompoundIII.Comet.TransferInternalSource
import Benchmarks.CompoundIII.Comet.CallReturnSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def transferFromArgs (src dst : AccountAddress) (amount : UInt256) : Store :=
  (((∅ : Store).insert "src" (.address src)).insert "dst" (.address dst)).insert
    "amount" (.int amount.toNat)

theorem transferFromTransition_body : transferFromTransition.body = calldataPrologue
    [.internalCall "transferInternal" [.env .caller, .var "src", .var "dst",
      .immutable "baseToken", .var "amount"] "__c0", .return [.boolLit true]] := rfl

theorem transferFrom_source {v src dst amount evm result}
    (ht : TransferInternalTrace v evm.executionEnv.source src dst v.baseToken amount evm result)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < 2^255 + 4) :
    explicitSourceResult config
      { contract := contract, locals := transferFromArgs src dst amount, immutables := immStore v }
      evm transferFromTransition.body [.bool true] result := by
  rw [transferFromTransition_body]
  let frame := calldataLocalFrame
    { contract := contract, locals := transferFromArgs src dst amount, immutables := immStore v } evm
  apply callReturnPrologue_source hv hhi (final := frame) (ret := "__c0")
    (fun _ ↦ by simp only [evalExprs?, evalExpr?, pure, bind, EvalResult.bind])
  apply transferInternal_call ht frame (.env .caller) (.var "src") (.var "dst")
    (.immutable "baseToken") (.var "amount") "__c0" rfl rfl
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, frame, calldataLocalFrame, transferFromArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, transferFromArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  · simp only [evalExpr?, frame, calldataLocalFrame, immStore_get_baseToken, EvalResult.ofOption]
  · simp only [evalExpr?, frame, calldataLocalFrame, transferFromArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl

end Benchmarks.CompoundIII.Comet
