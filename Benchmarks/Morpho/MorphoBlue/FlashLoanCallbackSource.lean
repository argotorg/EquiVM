import Benchmarks.Morpho.MorphoBlue.FlashLoanSourceStart
import Benchmarks.Morpho.MorphoBlue.FlashLoanCallbackABI
import Benchmarks.Morpho.MorphoBlue.CallerCallbackSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem FlashLoanInputs.insert {frame token assets data} (hi : FlashLoanInputs frame token assets data)
    (name : Ident) (value : Value) (ht : name ≠ "token") (ha : name ≠ "assets") (hd : name ≠ "data") :
    FlashLoanInputs { frame with locals := frame.locals.insert name value } token assets data := by
  constructor
  · simpa only [store_get_ne _ _ (show (name == "token") = false by simp [ht])] using hi.token_eq
  · simpa only [store_get_ne _ _ (show (name == "assets") = false by simp [ha])] using hi.assets_eq
  · simpa only [store_get_ne _ _ (show (name == "data") = false by simp [hd])] using hi.data_eq

def flashLoanCallbackFrame (frame : Frame) (caller : AccountAddress) : Frame :=
  { frame with locals := frame.locals.insert "callback" (.address caller) }

def flashLoanCalledFrame (frame : Frame) (caller : AccountAddress) : Frame :=
  { flashLoanCallbackFrame frame caller with locals :=
    (flashLoanCallbackFrame frame caller).locals.insert "__c1" .unit }

theorem flashLoanCallbackPrelude (frame : Frame) (evm : EVM.State) :
    ABlock config evm frame (flashLoanTransition.body.drop 6)
      (flashLoanCallbackFrame frame evm.executionEnv.source) (flashLoanTransition.body.drop 7) := by
  exact callerCallbackPrelude config frame evm "onMorphoFlashLoan" [.var "assets", .var "data"] "__c1"
    (flashLoanTransition.body.drop 9)

theorem flashLoanCallback_receiver (frame : Frame) (evm : EVM.State) :
    evalExpr? config (flashLoanCallbackFrame frame evm.executionEnv.source) evm (.var "callback") =
      .ok (.address evm.executionEnv.source) := by
  exact callerCallback_receiver config frame evm

theorem flashLoanCallback_guard (frame : Frame) (evm : EVM.State) :
    evalExpr? config (flashLoanCallbackFrame frame evm.executionEnv.source) evm
      (.binary .gt (.extCodeSize (.var "callback")) (.intLit 0)) =
      .ok (.bool (decide (0 < (extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val)).toNat))) :=
  callerCallback_guard config frame evm

theorem flashLoanCallbackSourceNoCode (frame : Frame) (evm : EVM.State)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) = UInt256.ofNat 0) :
    ExecBlock config frame evm (flashLoanTransition.body.drop 6) .reverted := by
  exact callerCallbackSourceNoCode config frame evm "onMorphoFlashLoan" [.var "assets", .var "data"] "__c1"
    (flashLoanTransition.body.drop 9) hc

theorem flashLoanCallbackSourceGuard (frame : Frame) (evm : EVM.State)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0) :
    ABlock config evm frame (flashLoanTransition.body.drop 6)
      (flashLoanCallbackFrame frame evm.executionEnv.source) (flashLoanTransition.body.drop 8) := by
  exact callerCallbackSourceGuard config frame evm "onMorphoFlashLoan" [.var "assets", .var "data"] "__c1"
    (flashLoanTransition.body.drop 9) hc

theorem flashLoanCallback_args {frame token assets data} (hi : FlashLoanInputs frame token assets data)
    (evm : EVM.State) :
    evalExprs? config (flashLoanCallbackFrame frame evm.executionEnv.source) evm [.var "assets", .var "data"] =
      .ok [.int (Int.ofNat assets.toNat), .bytes data] := by
  have hi' := hi.insert "callback" (.address evm.executionEnv.source) (by decide) (by decide) (by decide)
  simp only [evalExprs?, evalExpr?, hi'.assets_eq, hi'.data_eq, flashLoanCallbackFrame, callerCallbackFrame,
    EvalResult.ofOption, pure, bind, EvalResult.bind]

theorem flashLoanCallbackSourceFailure {frame token assets data} (hi : FlashLoanInputs frame token assets data)
    (evm evm' : EVM.State) (out : ByteArray)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0)
    (hcall : typedCallViaEVM config evm evm.executionEnv.source "onMorphoFlashLoan" 0
      [.int (Int.ofNat assets.toNat), .bytes data] (false, evm', out)) :
    ExecBlock config frame evm (flashLoanTransition.body.drop 6) .reverted := by
  exact callerCallbackSourceFailure config frame evm evm' "onMorphoFlashLoan" [.var "assets", .var "data"] "__c1"
    (flashLoanTransition.body.drop 9) _ out hc (flashLoanCallback_args hi evm) hcall

theorem flashLoanCallbackSourceSuccess {frame token assets data} (hi : FlashLoanInputs frame token assets data)
    (evm evm' : EVM.State) (out : ByteArray)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0)
    (hcall : typedCallViaEVM config evm evm.executionEnv.source "onMorphoFlashLoan" 0
      [.int (Int.ofNat assets.toNat), .bytes data] (true, evm', out))
    {result : ExecResult}
    (htail : ExecBlock config (flashLoanCalledFrame frame evm.executionEnv.source) evm'
      (flashLoanTransition.body.drop 9) result) :
    ExecBlock config frame evm (flashLoanTransition.body.drop 6) result := by
  exact callerCallbackSourceSuccess config frame evm evm' "onMorphoFlashLoan" [.var "assets", .var "data"] "__c1"
    (flashLoanTransition.body.drop 9) _ out hc (flashLoanCallback_args hi evm) hcall rfl htail

end Benchmarks.Morpho.MorphoBlue
