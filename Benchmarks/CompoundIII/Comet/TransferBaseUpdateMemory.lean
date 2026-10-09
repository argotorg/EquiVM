import Benchmarks.CompoundIII.Comet.TransferBaseUpdateModel
import Benchmarks.CompoundIII.Comet.UpdateBaseMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def transferBaseUpdateMemory (mem : ByteArray) (srcPtr dstPtr : UInt256)
    (v : CometWithExtendedAssetListImmutables) (evm : EVM.State) (src dst : AccountAddress)
    (srcBasic dstBasic : UserBasicData) (srcNext dstNext : UInt256) : ByteArray :=
  let mem' := updateBaseMemory mem srcPtr v evm src srcBasic srcNext
  match updateBaseOutcome v evm src srcBasic srcNext with
  | .ok evm' => updateBaseMemory mem' dstPtr v evm' dst dstBasic dstNext
  | _ => mem'

theorem transferBaseUpdateMemory_size {mem srcPtr dstPtr}
    (v : CometWithExtendedAssetListImmutables) (evm : EVM.State) (src dst : AccountAddress)
    (srcBasic dstBasic : UserBasicData) (srcNext dstNext : UInt256)
    (hsm : UserBasicMemory mem srcPtr srcBasic) (hdm : UserBasicMemory mem dstPtr dstBasic)
    (hslo : 96 ≤ srcPtr.toNat) (hdlo : 96 ≤ dstPtr.toNat)
    (hsep : srcPtr.toNat + 96 ≤ dstPtr.toNat) :
    (transferBaseUpdateMemory mem srcPtr dstPtr v evm src dst srcBasic dstBasic srcNext dstNext).size =
      mem.size := by
  have hd := updateBaseMemory_preserveLater v evm src srcBasic dstBasic srcNext hsm hdm hdlo hsep
  unfold transferBaseUpdateMemory
  cases updateBaseOutcome v evm src srcBasic srcNext with
  | ok evm' =>
      rw [updateBaseMemory_size v evm' dst dstBasic dstNext hd hdlo,
        updateBaseMemory_size v evm src srcBasic srcNext hsm hslo]
  | reverted => exact updateBaseMemory_size v evm src srcBasic srcNext hsm hslo
  | staticViolation => exact updateBaseMemory_size v evm src srcBasic srcNext hsm hslo

theorem transferBaseUpdateMemory_free {mem srcPtr dstPtr}
    (v : CometWithExtendedAssetListImmutables) (evm : EVM.State) (src dst : AccountAddress)
    (srcBasic dstBasic : UserBasicData) (srcNext dstNext : UInt256)
    (hsm : UserBasicMemory mem srcPtr srcBasic) (hdm : UserBasicMemory mem dstPtr dstBasic)
    (hslo : 96 ≤ srcPtr.toNat) (hdlo : 96 ≤ dstPtr.toNat)
    (hsep : srcPtr.toNat + 96 ≤ dstPtr.toNat) :
    memLoad ⟨64⟩
      (transferBaseUpdateMemory mem srcPtr dstPtr v evm src dst srcBasic dstBasic srcNext dstNext) =
        memLoad ⟨64⟩ mem := by
  have hd := updateBaseMemory_preserveLater v evm src srcBasic dstBasic srcNext hsm hdm hdlo hsep
  unfold transferBaseUpdateMemory
  cases updateBaseOutcome v evm src srcBasic srcNext with
  | ok evm' =>
      rw [updateBaseMemory_free v evm' dst dstBasic dstNext hd hdlo,
        updateBaseMemory_free v evm src srcBasic srcNext hsm hslo]
  | reverted => exact updateBaseMemory_free v evm src srcBasic srcNext hsm hslo
  | staticViolation => exact updateBaseMemory_free v evm src srcBasic srcNext hsm hslo

end Benchmarks.CompoundIII.Comet
