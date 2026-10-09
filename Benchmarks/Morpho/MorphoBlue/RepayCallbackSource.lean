import Benchmarks.Morpho.MorphoBlue.SupplyCallbackSource
import Benchmarks.Morpho.MorphoBlue.RepayCallbackABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev repayCallbackBody : List Stmt :=
  callerCallbackBody "onMorphoRepay" [.var "assets", .var "data"] "__c8"

theorem repayCallback_noCode (frame : Frame) (evm : EVM.State)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) = UInt256.ofNat 0) :
    ExecBlock config frame evm repayCallbackBody .reverted := by
  exact callerCallbackSourceNoCode config frame evm "onMorphoRepay" [.var "assets", .var "data"] "__c8" [] hc

theorem repayCallback_failure {p assets shares account data locals}
    (hl : SupplyLocals p assets shares account data locals) (imms : Store) (evm evm' : EVM.State) (out : ByteArray)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0)
    (hcall : typedCallViaEVM config evm evm.executionEnv.source "onMorphoRepay" 0
      [.int (Int.ofNat assets.toNat), .bytes data] (false, evm', out)) :
    ExecBlock config { contract := contract, locals := locals, immutables := imms } evm repayCallbackBody .reverted := by
  exact callerCallbackSourceFailure config _ evm evm' "onMorphoRepay" [.var "assets", .var "data"] "__c8"
    [] _ out hc (supplyCallback_args hl imms evm) hcall

theorem repayCallback_success {p assets shares account data locals}
    (hl : SupplyLocals p assets shares account data locals) (imms : Store) (evm evm' : EVM.State) (out : ByteArray)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0)
    (hcall : typedCallViaEVM config evm evm.executionEnv.source "onMorphoRepay" 0
      [.int (Int.ofNat assets.toNat), .bytes data] (true, evm', out)) :
    ExecBlock config { contract := contract, locals := locals, immutables := imms } evm repayCallbackBody
      (.ok (callerCallbackCalledFrame { contract := contract, locals := locals, immutables := imms }
        evm.executionEnv.source "__c8") evm') := by
  exact callerCallbackSourceSuccess config _ evm evm' "onMorphoRepay" [.var "assets", .var "data"] "__c8"
    [] _ out hc (supplyCallback_args hl imms evm) hcall rfl ExecBlock.nil

end Benchmarks.Morpho.MorphoBlue
