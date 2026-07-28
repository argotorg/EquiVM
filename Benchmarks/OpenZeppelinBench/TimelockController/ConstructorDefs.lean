import Benchmarks.OpenZeppelinBench.TimelockController.GrantRole
import Benchmarks.OpenZeppelinBench.TimelockController.ProposerRole
import Benchmarks.OpenZeppelinBench.TimelockController.CancellerRole
import Benchmarks.OpenZeppelinBench.TimelockController.ExecutorRole
import Benchmarks.OpenZeppelinBench.TimelockController.DefaultAdminRole
import Reasoning.Initcode
import Reasoning.Constructor
import Solm.Equiv

/-!
# OpenZeppelin TimelockController constructor — shared definitions

The payable constructor grants five role bits, writes `_minDelay = 1 days` (slot 2), and deploys the
runtime.  Because the initial storage is arbitrary (only `accountMapEquiv`-coupled), each `_grantRole`
call is a *conditional* nested-mapping bool write: `if (word & 0xff == 0) then set the low byte to 1`.
The `tlcCtorGrantMap` operator captures that single step uniformly on `AccountMap`s; both the EVM and
Solm sides reach a tower of these, so reconciliation just threads `accountMapEquiv` through it.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-! ## Creation-bytecode size and runtime window -/

theorem tlcCreation_size : timelockControllerBenchCreationBytecode.size = 7161 := by native_decide

theorem tlcRuntime_size : timelockControllerBenchBytecode.size = 6509 := by native_decide

/-- The runtime window `CODECOPY`'d + `RETURN`'d by the creation code (`PUSH2 6509 DUP1 PUSH2 652`:
    offset `652`, length `6509`) is exactly the deployed runtime. -/
theorem tlcCreation_runtime_window :
    timelockControllerBenchCreationBytecode.extract 652 (652 + 6509)
      = timelockControllerBenchBytecode := by native_decide

/-! ## Deployment shape (empty constructor, payable) -/

theorem tlc_selfDeployment_eq :
    config.selfDeployment = genSolidityConstructorDeployment contract.ctor.params := rfl

theorem tlc_ctor_params_nil : contract.ctor.params = [] := rfl

/-! ## Role / account words and the five nested-mapping slots -/

/-- Account word for `address(this)` (the `ADDRESS` opcode pushes `codeOwner.val`). -/
abbrev tlcThisWord (I : ExecutionEnv) : UInt256 := UInt256.ofNat I.codeOwner.val

/-- `_roles[role].hasRole[account]` slot as the constructor helper computes it (base slot 0). -/
def tlcCtorSlot (role account : UInt256) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨0⟩ role) account

def tlcSlotAdminThis (I : ExecutionEnv) : UInt256 :=
  tlcCtorSlot tlcDefaultAdminRoleWord (tlcThisWord I)

def tlcSlotAdminSender (I : ExecutionEnv) : UInt256 :=
  tlcCtorSlot tlcDefaultAdminRoleWord (solcSourceWord I)

def tlcSlotPropSender (I : ExecutionEnv) : UInt256 :=
  tlcCtorSlot tlcProposerRoleWord (solcSourceWord I)

def tlcSlotCancSender (I : ExecutionEnv) : UInt256 :=
  tlcCtorSlot tlcCancellerRoleWord (solcSourceWord I)

def tlcSlotExecZero (I : ExecutionEnv) : UInt256 :=
  tlcCtorSlot tlcExecutorRoleWord ⟨0⟩

/-! ## The single-grant map operator and the final constructor map -/

/-- One `_grantRole(role, account)` write on the raw account map: if the low byte of the current slot
    word is `0` (role absent), set it to `1`; otherwise leave the map unchanged.  The stored value
    `lor (land w ~0xff) 1` is the solc read-modify-write and equals the Solm `storageStore` of a bool
    `true` at offset `0` (`storageLocStore_bool_true_offset0`). -/
def tlcCtorGrantMap (cO : AccountAddress) (slot : UInt256) (σ : AccountMap) : AccountMap :=
  if UInt256.land ⟨255⟩ (σ.find? cO |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩)) = ⟨0⟩ then
    sstoreAccountMap cO σ slot
      (UInt256.lor
        (UInt256.land (σ.find? cO |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩))
          (UInt256.lnot ⟨255⟩)) ⟨1⟩)
  else σ

/-- Grants 1-2 (admin→this, then admin→sender guarded by `sender ≠ 0`). -/
def tlcCtorAdminMap (I : ExecutionEnv) (σ : AccountMap) : AccountMap :=
  if solcSourceWord I = ⟨0⟩ then
    tlcCtorGrantMap I.codeOwner (tlcSlotAdminThis I) σ
  else
    tlcCtorGrantMap I.codeOwner (tlcSlotAdminSender I)
      (tlcCtorGrantMap I.codeOwner (tlcSlotAdminThis I) σ)

/-- The full constructor post-state map: five conditional grants then `_minDelay = 86400` (slot 2). -/
def tlcCtorFinalMap (I : ExecutionEnv) (σ : AccountMap) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (tlcCtorGrantMap I.codeOwner (tlcSlotExecZero I)
      (tlcCtorGrantMap I.codeOwner (tlcSlotCancSender I)
        (tlcCtorGrantMap I.codeOwner (tlcSlotPropSender I)
          (tlcCtorAdminMap I σ))))
    ⟨2⟩ ⟨86400⟩

/-! ## Reconciliation: `accountMapEquiv` is preserved by every step -/

theorem tlcCtorGrantMap_reconcile {σ_evm σ_solm : AccountMap} (cO : AccountAddress) (slot : UInt256)
    (hAcc : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (tlcCtorGrantMap cO slot σ_evm) (tlcCtorGrantMap cO slot σ_solm) := by
  have hword : (σ_evm.find? cO |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩)) =
      (σ_solm.find? cO |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩)) :=
    accountMapEquiv_storage_findD hAcc cO slot ⟨0⟩
  unfold tlcCtorGrantMap
  rw [hword]
  split
  · exact accountMapEquiv_sstoreAccountMap cO slot _ hAcc
  · exact hAcc

theorem tlcCtorAdminMap_reconcile {σ_evm σ_solm : AccountMap} (I : ExecutionEnv)
    (hAcc : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (tlcCtorAdminMap I σ_evm) (tlcCtorAdminMap I σ_solm) := by
  unfold tlcCtorAdminMap
  split
  · exact tlcCtorGrantMap_reconcile _ _ hAcc
  · exact tlcCtorGrantMap_reconcile _ _ (tlcCtorGrantMap_reconcile _ _ hAcc)

theorem tlcCtorFinalMap_reconcile {σ_evm σ_solm : AccountMap} (I : ExecutionEnv)
    (hAcc : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (tlcCtorFinalMap I σ_evm) (tlcCtorFinalMap I σ_solm) := by
  unfold tlcCtorFinalMap
  exact accountMapEquiv_sstoreAccountMap _ _ _
    (tlcCtorGrantMap_reconcile _ _
      (tlcCtorGrantMap_reconcile _ _
        (tlcCtorGrantMap_reconcile _ _
          (tlcCtorAdminMap_reconcile I hAcc))))

/-! ## Spec-slot identity: `roleHasRoleSlot` in `solcMappingSlot` form -/

/-- The spec nested-mapping slot equals the solc keccak form used by the EVM helper. -/
theorem roleHasRoleSlot_solcForm (roleKV accountKV : KeyValue) :
    roleHasRoleSlot roleKV accountKV
      = solcMappingSlot (solcMappingSlot ⟨0⟩ (keyValueToWord roleKV)) (keyValueToWord accountKV) := by
  unfold roleHasRoleSlot roleDataSlot mapSlot solcMappingSlot
  rfl

end OpenZeppelinBench.TimelockController
