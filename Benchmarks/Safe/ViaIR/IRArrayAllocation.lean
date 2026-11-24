import Benchmarks.Safe.ViaIR.GetOwnersSource
import Benchmarks.Safe.ViaIR.Calldata
import Benchmarks.Safe.ViaIR.IRLengthCheck

variable {fork : Ethereum.Fork}

/-! Regression witness for the IR owner-array allocation-pointer check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def safeIROwnerAllocationCount : UInt256 := UInt256.ofNat (2 ^ 59 - 1)

def safeIROwnerAllocationEnv : ExecutionEnv :=
  { (default : ExecutionEnv) with
    code := safeBytecode
    codeOwner := AccountAddress.ofNat 4096
    source := AccountAddress.ofNat 4096
    calldata := ⟨#[0xa0, 0xe6, 0x7e, 0x2b]⟩
    weiValue := ⟨0⟩
    perm := true }

def safeIROwnerAllocationAccounts : AccountMap :=
  (default : AccountMap).insert (AccountAddress.ofNat 4096)
    { (default : Account) with
      storage := (default : Storage).insert ⟨3⟩ safeIROwnerAllocationCount |>.insert
        (mapSlot ⟨1⟩ ⟨2⟩) ⟨1⟩ }

def safeIROwnerAllocationState : State :=
  initState safeIROwnerAllocationAccounts safeIROwnerAllocationAccounts
    (.ofUInt256 ⟨100000⟩) default safeIROwnerAllocationEnv

theorem safeIROwnerAllocationPremises :
    safeIROwnerAllocationEnv.code = safeBytecode ∧
      safeIROwnerAllocationEnv.calldata.size < UInt256.size ∧
      safeIROwnerAllocationAccounts.get? safeIROwnerAllocationEnv.codeOwner ≠ none ∧
      selectorDispatchMsg contract safeIROwnerAllocationEnv.calldata =
        some getownersTransition := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> native_decide

theorem safeIROwnerAllocationStorage :
    ownerCount safeIROwnerAllocationState = safeIROwnerAllocationCount ∧
      ownerLink safeIROwnerAllocationState ⟨1⟩ = ⟨1⟩ := by native_decide

theorem safeIROwnerAllocationDecoding :
    config.externalABI.decodeCalldata?
      (getownersTransition.params.map Param.name)
      (transitionSignature getownersTransition).paramTypes safeIROwnerAllocationEnv.calldata =
        some ∅ := by
  exact safeDecodeCalldata_empty_ok (cd := safeIROwnerAllocationEnv.calldata)
    (by decide) (by decide)

theorem safeIROwnerAllocationExecution :
    (match Ξ .cancun safeIROwnerAllocationAccounts safeIROwnerAllocationAccounts ⟨100000⟩
        default safeIROwnerAllocationEnv with
      | .ok (.revert gas out) => gas == ⟨97240⟩ &&
          out == (⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ ++ (⟨0x41⟩ : UInt256).toByteArray)
      | _ => false) = true := by native_decide

theorem safeIROwnerAllocationSourceReverts :
    ExecTransitionBody fork config contract safeIROwnerAllocationState ∅
      getownersTransition.body .reverted := by
  apply safeGetOwnersCountRevert safeIROwnerAllocationState rfl
  rw [safeIROwnerAllocationStorage.1]
  decide

theorem safeIROwnerAllocationRefines :
    runtimeRefinementFor .cancun config contract safeIROwnerAllocationAccounts
      safeIROwnerAllocationAccounts ⟨100000⟩ default safeIROwnerAllocationEnv := by
  have hex := safeIROwnerAllocationExecution
  have hbody := safeIROwnerAllocationSourceReverts (fork := .cancun)
  have hsel := safeIROwnerAllocationPremises.2.2.2
  cases he : Ξ .cancun safeIROwnerAllocationAccounts safeIROwnerAllocationAccounts ⟨100000⟩
      default safeIROwnerAllocationEnv with
  | error => rw [he] at hex; cases hex
  | ok result =>
    cases result with
    | success => rw [he] at hex; cases hex
    | revert gas out =>
      exact reEquivSelectorExecution hsel safeIROwnerAllocationDecoding hbody
        (.revert he rfl)

theorem safeIROwnerAllocationCorrectedBound (count : Nat) :
    32 * count + 160 ≤ 2 ^ 64 - 1 ↔ count ≤ 2 ^ 59 - 6 := by omega

theorem safeIROwnerAllocationRejectedByCorrectedBound :
    ¬safeIROwnerAllocationCount.toNat ≤ 2 ^ 59 - 6 := by decide

end Benchmarks.Safe.ViaIR
