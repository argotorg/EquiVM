import Benchmarks.Safe.ViaIR.ContractSignatureReject
import Benchmarks.Safe.ViaIR.PreModuleSource
import Benchmarks.Safe.ViaIR.PreModuleCallEncoding
import Benchmarks.Safe.ViaIR.Bytes32ReturnDecoder

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safePreModuleCanReject (evm : EVM.State) (target value operation guard : UInt256)
    (payload : ByteArray) (hz : UInt256.land guard solcAddrMask ≠ ⟨0⟩)
    (ho : operation.toNat < 256) :
    ExecStmt fork config (preModuleCheckingFrame (AccountAddress.ofUInt256 target)
      value payload operation guard) evm preModuleCheck .reverted := by
  let data := preModuleCallBytes target value payload operation
    (UInt256.ofNat evm.executionEnv.source.val)
  have hinput : data.size ≠ 213 := by
    dsimp only [data, preModuleCallBytes]
    simp only [ByteArray.size_append, wordBytes_size, List.length_cons, List.length_nil,
      ByteArray_zeroes_size]
    have hs : checkModuleTransactionSelector.size = 4 := by decide +kernel
    rw [hs]
    change 4 + 32 * 6 + payload.size + (ABI.paddedSize payload.size - payload.size) ≠ 213
    unfold ABI.paddedSize
    omega
  obtain ⟨z, evm', hcall⟩ := callZeroGasEmptyOutput evm
    (EVM.address (AccountAddress.ofUInt256 guard)) data true hinput
  have htyped : typedCallViaEVM fork config evm (EVM.address (AccountAddress.ofUInt256 guard))
      "checkModuleTransaction" 0 [.address (AccountAddress.ofUInt256 target),
        .int (Int.ofNat value.toNat), .bytes payload, .int (Int.ofNat operation.toNat),
        .address evm.executionEnv.source] (z, evm', ByteArray.empty) := by
    refine ⟨data, ?_, hcall⟩
    simpa only [accountAddress_roundtrip] using safePreModuleCallEncoding
      target value payload operation (UInt256.ofNat evm.executionEnv.source.val) ho
  cases z
  · exact safePreModuleCheckFailed hz htyped
  · apply safePreModuleCheckInvalid hz htyped
    change (ABI.decodeReturnValueWithMode? .modern abiBytes32 ByteArray.empty).map
      (fun v ↦ [v]) = none
    rw [decodeBytes32ReturnShort (by decide)]
    rfl

theorem safePreModuleExecutionCanReject (evm : EVM.State) (target value operation : UInt256)
    (payload : ByteArray) (hz : UInt256.land (preModuleGuardWord evm) solcAddrMask ≠ ⟨0⟩)
    (ho : operation.toNat < 256) :
    ExecFuncBody fork config (preModuleFrame (AccountAddress.ofUInt256 target)
      value payload operation) evm preModuleExecutionFunction.body .reverted := by
  by_cases ha : preModuleAuthorized evm
  · exact safePreModuleSourceRevert ha
      (safePreModuleCanReject evm target value operation (preModuleGuardWord evm) payload hz ho)
  · exact safePreModuleUnauthorized evm _ value payload operation ha

end Benchmarks.Safe.ViaIR
