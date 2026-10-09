import Benchmarks.Morpho.MorphoBlue.SupplySourceStart
import Benchmarks.Morpho.MorphoBlue.LocalBytesGuard
import Benchmarks.Morpho.MorphoBlue.CallerCallbackSource
import Benchmarks.Morpho.MorphoBlue.SupplyCallbackABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev supplyCallbackBody : List Stmt :=
  callerCallbackBody "onMorphoSupply" [.var "assets", .var "data"] "__c7"

theorem supplyDataGuard {p assets shares account data locals}
    (hl : SupplyLocals p assets shares account data locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .gt (.arrayLength .localVar ⟨"data", []⟩) (.intLit 0)) = .ok (.bool (decide (0 < data.size))) :=
  evalLocalBytesNonempty hl.data_eq

theorem supplyCallback_args {p assets shares account data locals}
    (hl : SupplyLocals p assets shares account data locals) (imms : Store) (evm : EVM.State) :
    evalExprs? config (callerCallbackFrame { contract := contract, locals := locals, immutables := imms }
      evm.executionEnv.source) evm [.var "assets", .var "data"] =
      .ok [.int (Int.ofNat assets.toNat), .bytes data] := by
  have hl1 := hl.insert "callback" (.address evm.executionEnv.source) (by decide) (by decide)
  simp only [evalExprs?, evalExpr?, callerCallbackFrame, hl1.assets_eq, hl1.data_eq,
    EvalResult.ofOption, pure, bind, EvalResult.bind]

theorem supplyCallback_noCode (frame : Frame) (evm : EVM.State)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) = UInt256.ofNat 0) :
    ExecBlock config frame evm supplyCallbackBody .reverted := by
  exact callerCallbackSourceNoCode config frame evm "onMorphoSupply" [.var "assets", .var "data"] "__c7" [] hc

theorem supplyCallback_failure {p assets shares account data locals}
    (hl : SupplyLocals p assets shares account data locals) (imms : Store) (evm evm' : EVM.State) (out : ByteArray)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0)
    (hcall : typedCallViaEVM config evm evm.executionEnv.source "onMorphoSupply" 0
      [.int (Int.ofNat assets.toNat), .bytes data] (false, evm', out)) :
    ExecBlock config { contract := contract, locals := locals, immutables := imms } evm supplyCallbackBody .reverted := by
  exact callerCallbackSourceFailure config _ evm evm' "onMorphoSupply" [.var "assets", .var "data"] "__c7"
    [] _ out hc (supplyCallback_args hl imms evm) hcall

theorem supplyCallback_success {p assets shares account data locals}
    (hl : SupplyLocals p assets shares account data locals) (imms : Store) (evm evm' : EVM.State) (out : ByteArray)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0)
    (hcall : typedCallViaEVM config evm evm.executionEnv.source "onMorphoSupply" 0
      [.int (Int.ofNat assets.toNat), .bytes data] (true, evm', out)) :
    ExecBlock config { contract := contract, locals := locals, immutables := imms } evm supplyCallbackBody
      (.ok (callerCallbackCalledFrame { contract := contract, locals := locals, immutables := imms }
        evm.executionEnv.source "__c7") evm') := by
  exact callerCallbackSourceSuccess config _ evm evm' "onMorphoSupply" [.var "assets", .var "data"] "__c7"
    [] _ out hc (supplyCallback_args hl imms evm) hcall rfl ExecBlock.nil

end Benchmarks.Morpho.MorphoBlue
