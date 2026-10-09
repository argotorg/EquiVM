import Benchmarks.Morpho.MorphoBlue.SupplyCollateralSourceStart
import Benchmarks.Morpho.MorphoBlue.LocalBytesGuard
import Benchmarks.Morpho.MorphoBlue.CallerCallbackSource
import Benchmarks.Morpho.MorphoBlue.SupplyCollateralCallbackABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev supplyCollateralCallbackBody : List Stmt :=
  callerCallbackBody "onMorphoSupplyCollateral" [.var "assets", .var "data"] "__c2"

theorem supplyCollateralDataGuard {p assets account data locals}
    (hl : SupplyCollateralLocals p assets account data locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .gt (.arrayLength .localVar ⟨"data", []⟩) (.intLit 0)) = .ok (.bool (decide (0 < data.size))) :=
  evalLocalBytesNonempty hl.data_eq

theorem supplyCollateralCallback_args {p assets account data locals}
    (hl : SupplyCollateralLocals p assets account data locals) (imms : Store) (evm : EVM.State) :
    evalExprs? config (callerCallbackFrame { contract := contract, locals := locals, immutables := imms }
      evm.executionEnv.source) evm [.var "assets", .var "data"] =
      .ok [.int (Int.ofNat assets.toNat), .bytes data] := by
  have hl1 := hl.insert "callback" (.address evm.executionEnv.source) (by decide) (by decide)
  simp only [evalExprs?, evalExpr?, callerCallbackFrame, hl1.assets_eq, hl1.data_eq,
    EvalResult.ofOption, pure, bind, EvalResult.bind]

theorem supplyCollateralCallback_noCode (frame : Frame) (evm : EVM.State)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) = UInt256.ofNat 0) :
    ExecBlock config frame evm supplyCollateralCallbackBody .reverted := by
  exact callerCallbackSourceNoCode config frame evm "onMorphoSupplyCollateral" [.var "assets", .var "data"] "__c2" [] hc

theorem supplyCollateralCallback_failure {p assets account data locals}
    (hl : SupplyCollateralLocals p assets account data locals) (imms : Store) (evm evm' : EVM.State) (out : ByteArray)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0)
    (hcall : typedCallViaEVM config evm evm.executionEnv.source "onMorphoSupplyCollateral" 0
      [.int (Int.ofNat assets.toNat), .bytes data] (false, evm', out)) :
    ExecBlock config { contract := contract, locals := locals, immutables := imms } evm supplyCollateralCallbackBody .reverted := by
  exact callerCallbackSourceFailure config _ evm evm' "onMorphoSupplyCollateral" [.var "assets", .var "data"] "__c2"
    [] _ out hc (supplyCollateralCallback_args hl imms evm) hcall

theorem supplyCollateralCallback_success {p assets account data locals}
    (hl : SupplyCollateralLocals p assets account data locals) (imms : Store) (evm evm' : EVM.State) (out : ByteArray)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0)
    (hcall : typedCallViaEVM config evm evm.executionEnv.source "onMorphoSupplyCollateral" 0
      [.int (Int.ofNat assets.toNat), .bytes data] (true, evm', out)) :
    ExecBlock config { contract := contract, locals := locals, immutables := imms } evm supplyCollateralCallbackBody
      (.ok (callerCallbackCalledFrame { contract := contract, locals := locals, immutables := imms }
        evm.executionEnv.source "__c2") evm') := by
  exact callerCallbackSourceSuccess config _ evm evm' "onMorphoSupplyCollateral" [.var "assets", .var "data"] "__c2"
    [] _ out hc (supplyCollateralCallback_args hl imms evm) hcall rfl ExecBlock.nil

end Benchmarks.Morpho.MorphoBlue
