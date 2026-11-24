import Benchmarks.Safe.ViaIR.StorageAtSource
import Benchmarks.Safe.ViaIR.WordPairDecoder

variable {fork : Ethereum.Fork}

/-! Regression witness for the IR storage reader's final allocation-pointer guard. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def safeIRStorageAllocationLength : UInt256 := UInt256.ofNat (2 ^ 59 - 1)

def safeIRStorageAllocationCalldata : ByteArray :=
  ⟨#[0x56, 0x24, 0xb2, 0x5b]⟩ ++
    (⟨0⟩ : UInt256).toByteArray ++ safeIRStorageAllocationLength.toByteArray

def safeIRStorageAllocationEnv : ExecutionEnv :=
  { (default : ExecutionEnv) with
    code := safeBytecode
    codeOwner := AccountAddress.ofNat 4096
    source := AccountAddress.ofNat 4096
    calldata := safeIRStorageAllocationCalldata
    weiValue := ⟨0⟩
    perm := true }

def safeIRStorageAllocationAccounts : AccountMap :=
  (default : AccountMap).insert (AccountAddress.ofNat 4096) default

def safeIRStorageAllocationState : State :=
  initState safeIRStorageAllocationAccounts safeIRStorageAllocationAccounts
    (.ofUInt256 ⟨100000⟩) default safeIRStorageAllocationEnv

theorem safeIRStorageAllocationPremises :
    safeIRStorageAllocationEnv.code = safeBytecode ∧
      safeIRStorageAllocationEnv.calldata.size < UInt256.size ∧
      safeIRStorageAllocationAccounts.get? safeIRStorageAllocationEnv.codeOwner ≠ none ∧
      selectorDispatchMsg contract safeIRStorageAllocationEnv.calldata =
        some getstorageatTransition := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> native_decide

theorem safeIRStorageAllocationDecoding :
    config.externalABI.decodeCalldata?
      (getstorageatTransition.params.map Param.name)
      (transitionSignature getstorageatTransition).paramTypes
      safeIRStorageAllocationEnv.calldata =
        some (storageAtArgs ⟨0⟩ safeIRStorageAllocationLength) := by
  have h0 : calldataWord safeIRStorageAllocationCalldata 4 = ⟨0⟩ := by native_decide
  have hn : calldataWord safeIRStorageAllocationCalldata 36 = safeIRStorageAllocationLength := by
    native_decide
  have hd := decodeWordPair (cd := safeIRStorageAllocationCalldata)
    (x := "offset") (y := "length") (by native_decide) (by native_decide)
  simpa only [h0, hn] using hd

theorem safeIRStorageAllocationSourceGuard :
    (UInt256.shiftLeft safeIRStorageAllocationLength (UInt256.ofNat 5)).toNat = 2 ^ 64 - 32 ∧
      (UInt256.shiftLeft safeIRStorageAllocationLength (UInt256.ofNat 5)).toNat ≤ 2 ^ 64 - 1 := by
  decide

theorem safeIRStorageAllocationExecution :
    (match Ξ .cancun safeIRStorageAllocationAccounts safeIRStorageAllocationAccounts ⟨100000⟩
        default safeIRStorageAllocationEnv with
      | .ok (.revert gas out) => gas == ⟨99481⟩ &&
          out == (⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ ++ (⟨0x41⟩ : UInt256).toByteArray)
      | _ => false) = true := by
  native_decide

theorem safeIRStorageAllocationSourceReverts :
    ExecTransitionBody fork config contract safeIRStorageAllocationState
      (storageAtArgs ⟨0⟩ safeIRStorageAllocationLength) getstorageatTransition.body .reverted :=
  safeStorageAtLengthRevert safeIRStorageAllocationState ⟨0⟩ safeIRStorageAllocationLength
    rfl (by decide)

theorem safeIRStorageAllocationRefines :
    runtimeRefinementFor .cancun config contract safeIRStorageAllocationAccounts
      safeIRStorageAllocationAccounts ⟨100000⟩ default safeIRStorageAllocationEnv := by
  have hex := safeIRStorageAllocationExecution
  have hbody := safeIRStorageAllocationSourceReverts (fork := .cancun)
  have hsel := safeIRStorageAllocationPremises.2.2.2
  cases he : Ξ .cancun safeIRStorageAllocationAccounts safeIRStorageAllocationAccounts ⟨100000⟩
      default safeIRStorageAllocationEnv with
  | error => rw [he] at hex; cases hex
  | ok result =>
    cases result with
    | success => rw [he] at hex; cases hex
    | revert gas out =>
      exact reEquivSelectorExecution hsel safeIRStorageAllocationDecoding hbody
        (.revert he rfl)

-- The guard includes the 128-byte starting pointer and 32-byte header.
theorem safeIRStorageAllocationCorrectedBound (bytes : Nat) :
    bytes + 160 ≤ 2 ^ 64 - 1 ↔ bytes ≤ 2 ^ 64 - 161 := by omega

theorem safeIRStorageAllocationRejectedByCorrectedBound :
    ¬(UInt256.shiftLeft safeIRStorageAllocationLength (UInt256.ofNat 5)).toNat ≤
      2 ^ 64 - 161 := by decide

end Benchmarks.Safe.ViaIR
