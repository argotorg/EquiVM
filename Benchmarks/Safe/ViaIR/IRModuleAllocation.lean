import Benchmarks.Safe.ViaIR.ModulesSource
import Benchmarks.Safe.ViaIR.Calldata
import Benchmarks.Safe.ViaIR.Dispatch

variable {fork : Ethereum.Fork}

/-! Boundary witness for the IR paginated-module array allocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

def safeIRModuleAllocationSize : UInt256 := UInt256.ofNat (2 ^ 59 - 1)

def safeIRModuleAllocationEnv : ExecutionEnv :=
  { (default : ExecutionEnv) with
    code := safeBytecode
    codeOwner := AccountAddress.ofNat 4096
    source := AccountAddress.ofNat 4096
    calldata := ⟨#[0xcc, 0x2f, 0x84, 0x52]⟩ ++ (⟨1⟩ : UInt256).toByteArray ++
      safeIRModuleAllocationSize.toByteArray
    weiValue := ⟨0⟩
    perm := true }

def safeIRModuleAllocationAccounts : AccountMap :=
  (default : AccountMap).insert (AccountAddress.ofNat 4096)
    { (default : Account) with
      storage := (default : Storage).insert (mapSlot ⟨1⟩ ⟨1⟩) ⟨1⟩ }

def safeIRModuleAllocationState : State :=
  initState safeIRModuleAllocationAccounts safeIRModuleAllocationAccounts
    (.ofUInt256 ⟨100000⟩) default safeIRModuleAllocationEnv

theorem safeIRModuleAllocationPremises :
    safeIRModuleAllocationEnv.code = safeBytecode ∧
      safeIRModuleAllocationEnv.calldata.size < UInt256.size ∧
      safeIRModuleAllocationAccounts.get? safeIRModuleAllocationEnv.codeOwner ≠ none ∧
      selectorDispatchMsg contract safeIRModuleAllocationEnv.calldata =
        some getmodulespaginatedTransition := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> native_decide

theorem safeIRModuleAllocationStorage :
    moduleLink safeIRModuleAllocationState ⟨1⟩ = ⟨1⟩ := by native_decide

theorem safeIRModuleAllocationDecoding :
    config.externalABI.decodeCalldata?
      (getmodulespaginatedTransition.params.map Param.name)
      (transitionSignature getmodulespaginatedTransition).paramTypes
      safeIRModuleAllocationEnv.calldata =
        some (modulesArgs ⟨1⟩ safeIRModuleAllocationSize) := by
  have hs : calldataWord safeIRModuleAllocationEnv.calldata 4 = ⟨1⟩ := by native_decide
  have hn : calldataWord safeIRModuleAllocationEnv.calldata 36 = safeIRModuleAllocationSize := by
    native_decide
  have hd := decodeCalldata_addr_uint256_ok (cd := safeIRModuleAllocationEnv.calldata)
    (x := "start") (y := "pageSize")
    (by native_decide) (by native_decide) (by rw [hs]; decide)
  simpa only [hs, hn] using hd

theorem safeIRModuleAllocationExecution :
    (match Ξ .cancun safeIRModuleAllocationAccounts safeIRModuleAllocationAccounts ⟨100000⟩
        default safeIRModuleAllocationEnv with
      | .ok (.revert gas out) => gas == ⟨99080⟩ &&
          out == (⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ ++ (⟨0x41⟩ : UInt256).toByteArray)
      | _ => false) = true := by native_decide

theorem safeIRModuleAllocationSourceReverts :
    ExecTransitionBody fork config contract safeIRModuleAllocationState
      (modulesArgs ⟨1⟩ safeIRModuleAllocationSize) getmodulespaginatedTransition.body
      .reverted := by
  exact safeModulesSourceLarge safeIRModuleAllocationState ⟨1⟩ safeIRModuleAllocationSize
    (by decide) rfl (.inl rfl) (by decide) (by decide)

theorem safeIRModuleAllocationRefines :
    runtimeRefinementFor .cancun config contract safeIRModuleAllocationAccounts
      safeIRModuleAllocationAccounts ⟨100000⟩ default safeIRModuleAllocationEnv := by
  have hex := safeIRModuleAllocationExecution
  have hbody := safeIRModuleAllocationSourceReverts (fork := .cancun)
  have hsel := safeIRModuleAllocationPremises.2.2.2
  cases he : Ξ .cancun safeIRModuleAllocationAccounts safeIRModuleAllocationAccounts ⟨100000⟩
      default safeIRModuleAllocationEnv with
  | error => rw [he] at hex; cases hex
  | ok result =>
    cases result with
    | success => rw [he] at hex; cases hex
    | revert gas out =>
      exact reEquivSelectorExecution hsel safeIRModuleAllocationDecoding hbody
        (.revert he rfl)

theorem safeIRModuleAllocationCorrectedBound (pageSize : Nat) :
    32 * pageSize + 160 ≤ 2 ^ 64 - 1 ↔ pageSize ≤ 2 ^ 59 - 6 := by omega

theorem safeIRModuleAllocationRejectedByCorrectedBound :
    ¬safeIRModuleAllocationSize.toNat ≤ 2 ^ 59 - 6 := by decide

end Benchmarks.Safe.ViaIR
