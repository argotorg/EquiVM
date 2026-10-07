import Solm.MetaSolidityLayout
import Solm.Notation
import Solm.Semantics

/-! Regression checks for transient layouts, operations, name resolution, and static mode. -/

namespace Solm.TransientTests

open ABI

private def wordTy : StorageType := .elem (.int (.uint ⟨256, by decide⟩))
private def halfTy : StorageType := .elem (.int (.uint ⟨128, by decide⟩))

private def contract : ContractDecl :=
  { name := "TransientTests"
    storage := [{ name := "persistent", ty := wordTy },
      { name := "saved", ty := .dynamicArray wordTy }]
    transient := [{ name := "a", ty := halfTy }, { name := "b", ty := halfTy },
      { name := "flag", ty := wordTy }, { name := "values", ty := .dynamicArray wordTy },
      { name := "data", ty := .bytes }]
    ctor := { params := [], body := [] } }

private def cfg : Config :=
  { storageBackend := solidityStorage! [contract.structs] [contract.storage]
    transientBackend := solidityTransientStorage! [contract.structs] [contract.transient]
    externalABI := defaultExternalCallABI
    selfDeployment := fun code _ ↦ some code }

private def singleLayout : StorageLayout :=
  solidityLayout! [([] : List StructDecl)] [([{ name := "flag", ty := wordTy }] : List StorageDecl)]

private def position (layout : StorageLayout) (name : Ident) : Option (Nat × Nat × Nat) := do
  let .leaf loc ← layout { base := name } | none
  pure (loc.slot.toNat, loc.offset.val, loc.size.val)

-- Both failed with the PR's old allocator: an exact fit must stay in the current slot.
#guard position singleLayout "flag" = some (0, 0, 32)
#guard position cfg.transientBackend.locate? "a" = some (0, 0, 16)
#guard position cfg.transientBackend.locate? "b" = some (0, 16, 16)
#guard position cfg.transientBackend.locate? "flag" = some (1, 0, 32)
#guard position cfg.storageBackend.locate? "persistent" = some (0, 0, 32)

private def owner : EVM.Address := .ofNat 256
private def other : EVM.Address := .ofNat 512
private def evm : EVM.State :=
  { (default : EVM.State) with
    executionEnv := { (default : Ethereum.ExecutionEnv) with codeOwner := owner, perm := true }
    accountMap := ((∅ : Ethereum.AccountMap).insert owner
      { (default : Ethereum.Account) with storage := (∅ : Ethereum.Storage).insert ⟨0⟩ ⟨777⟩ })
      |>.insert other { (default : Ethereum.Account) with
        tstorage := (∅ : Ethereum.Storage).insert ⟨0⟩ ⟨888⟩ } }

private def frame : Frame := { contract := contract, locals := ∅ }

private def read (state : EVM.State) (name : Ident) : EvalResult Value :=
  evalExpr? cfg frame state (.transient { base := name })

private def assign (state : EVM.State) (name : Ident) (value : Value) : EvalResult EVM.State := do
  let (_, state') ← assignStorageRef? cfg frame state .transient { base := name } value
  pure state'

private def readAfter (result : EvalResult EVM.State) (name : Ident) : EvalResult Value := do
  let state ← result
  read state name

private def packedWrite : EvalResult EVM.State := do
  let state ← assign evm "a" (.int 42)
  assign state "b" (.int 99)

#guard read evm "a" = .ok (.int 0)
#guard readAfter packedWrite "a" = .ok (.int 42)
#guard readAfter packedWrite "b" = .ok (.int 99)
#guard (do
  let state ← packedWrite
  pure (EVM.transientLoad state owner ⟨0⟩).toNat) = .ok (42 + 99 * 2 ^ 128)
#guard (do
  let state ← packedWrite
  pure ((EVM.storageLoad state owner ⟨0⟩).toNat,
    (EVM.transientLoad state other ⟨0⟩).toNat)) = .ok (777, 888)
#guard readAfter (do let state ← packedWrite; assign state "a" (.int 0)) "b" = .ok (.int 99)
#guard readAfter (do let state ← packedWrite; assign state "a" (.int 0)) "a" = .ok (.int 0)
#guard readAfter (assign evm "a" (.int (2 ^ 128 + 3))) "a" = .ok (.int 3)

private def flagWrite : EvalResult EVM.State := assign evm "flag" (.int 123)
#guard readAfter flagWrite "flag" = .ok (.int 123)
#guard readAfter (do
  let state ← flagWrite
  deleteStorage? cfg frame state { base := "flag" }) "flag" = .ok (.int 0)

-- Aggregate support reuses the current Solidity backend, including bounds and empty-pop reverts.
private def arrayWrite : EvalResult EVM.State := do
  let state ← pushArray? cfg frame evm { base := "values" } (some (.int 11))
  pushArray? cfg frame state { base := "values" } (some (.int 22))

#guard readAfter arrayWrite "values" = .ok (.array [.int 11, .int 22])
#guard (do
  let state ← arrayWrite
  evalExpr? cfg frame state (.arrayLength .transient { base := "values" })) = .ok (.int 2)
#guard (do
  let state ← arrayWrite
  evalExpr? cfg frame state
    (.transient { base := "values", steps := [.aindex (.intLit 1)] })) = .ok (.int 22)
#guard (do
  let state ← arrayWrite
  evalExpr? cfg frame state
    (.transient { base := "values", steps := [.aindex (.intLit 2)] })) = .revert
#guard readAfter (do
  let state ← arrayWrite
  popArray? cfg frame state { base := "values" }) "values" = .ok (.array [.int 11])
#guard readAfter (popArray? cfg frame evm { base := "values" }) "values" = .revert
#guard readAfter (do
  let state ← arrayWrite
  deleteStorage? cfg frame state { base := "values" }) "values" = .ok (.array [])

-- Index expressions still read persistent storage through its original backend.
#guard (do
  let state ← arrayWrite
  evalExpr? cfg frame state (.transient
    { base := "values"
      steps := [.aindex (.binary .sub (.storage { base := "persistent" }) (.intLit 776))] })) =
  .ok (.int 22)

private def longBytes : ByteArray := ⟨Array.replicate 33 0xab⟩
private def shortBytes : ByteArray := ⟨#[0x12, 0x34]⟩
#guard readAfter (assign evm "data" (.bytes longBytes)) "data" = .ok (.bytes longBytes)
#guard readAfter (do
  let state ← assign evm "data" (.bytes longBytes)
  assign state "data" (.bytes shortBytes)) "data" = .ok (.bytes shortBytes)
#guard readAfter (do
  let state ← assign evm "data" (.bytes shortBytes)
  pushArray? cfg frame state { base := "data" } (some (.fixedBytes 0 [0x56]))) "data" =
  .ok (.bytes ⟨#[0x12, 0x34, 0x56]⟩)

-- A local persistent-storage alias wins for unqualified push/pop/delete, even when its name
-- shadows a transient declaration. Explicit transient references still address the declared map.
private def aliasedFrame : Frame :=
  { frame with
    locals := (∅ : Store).insert "values"
      (.storageRef { base := "saved" } (.dynamicArray wordTy)) }
#guard usesTransientStorage aliasedFrame { base := "values" } = false
#guard (do
  let state ← pushArray? cfg aliasedFrame evm { base := "values" } (some (.int 7))
  cfg.storageBackend.read { base := "saved" } (.dynamicArray wordTy) state) =
  .ok (.array [.int 7])
#guard readAfter
  (pushArray? cfg aliasedFrame evm { base := "values" } (some (.int 7))) "values" =
  .ok (.array [])
#guard (do
  let state ← arrayWrite
  evalExpr? cfg aliasedFrame state (.transient { base := "values" })) =
  .ok (.array [.int 11, .int 22])

private def syntaxContract : ContractDecl := solidity% contract TransientSyntax {
  uint256 persistent;
  uint256 transient flag;
  uint256 immutable version;
  uint256 constant answer = 42;
  constructor(uint256 v) { version = v; }
  function set(uint256 v) external {
    flag = v;
    persistent = answer;
    require(flag == v);
  }
}

#guard syntaxContract.storage.map (·.name) = ["persistent"]
#guard syntaxContract.transient.map (·.name) = ["flag"]
#guard syntaxContract.immutables.map (·.name) = ["version"]
#guard syntaxContract.constants.map (·.name) = ["answer"]
#guard (syntaxContract.transitions[0]!).body[1]? =
  some (.assign .transient { base := "flag" } (.var "v"))

private def aliasSyntax : ContractDecl := solidity% contract TransientAliases {
  uint256[] saved;
  uint256[] transient values;
  function append() external {
    uint256[] storage values = saved;
    values.push(7);
  }
  function echoValue(uint256 values) external returns (uint256) {
    return values;
  }
}
#guard (aliasSyntax.transitions[0]!).body[1]? =
  some (.letStorage "values" { base := "saved" })
#guard (aliasSyntax.transitions[0]!).body[2]? =
  some (.push { base := "values" } (some (.intLit 7)))
#guard (aliasSyntax.transitions[1]!).body[1]? = some (.return [.var "values"])

/-- error: solm: duplicate state variable name -/
#guard_msgs in
private def duplicateNames : ContractDecl := solidity% contract DuplicateNames {
  uint256 flag;
  uint256 transient flag;
}

-- A transient setter has the same static-halt rule as persistent mutation; transient reads
-- remain available. Full bytecode refinement in both modes is proved by TransientFlag.Correct.
private def staticState : EVM.State := { evm with executionEnv.perm := false }
#guard read staticState "flag" = .ok (.int 0)

-- Exercise the EVM message-call bridge shared by Solm calls. Transient state survives successful
-- calls within a transaction, belongs to the execution context, and rolls back with a failed call.
private def runMessage (state : EVM.State) (recipient : EVM.Address) (code : ByteArray)
    (perm : Bool := true) : Bool × EVM.State × ByteArray :=
  let (accounts, _, substate, ok, output) := Ethereum.EVM.Θ
    state.accountMap state.σ₀ state.substate state.executionEnv.codeOwner
    state.executionEnv.sender recipient (.Code code) ⟨100000⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ .empty 1
    state.executionEnv.header state.executionEnv.blobVersionedHashes state.executionEnv.blocks perm
  (ok, { state with accountMap := accounts, substate := substate }, output)

private def setCode : ByteArray := ⟨#[0x60, 0x4d, 0x5f, 0x5d, 0x00]⟩
private def getCode : ByteArray := ⟨#[0x5f, 0x5c, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩
private def revertCode : ByteArray := ⟨#[0x60, 0x63, 0x5f, 0x5d, 0x5f, 0x5f, 0xfd]⟩
private def firstCall := runMessage evm owner setCode

#guard firstCall.1
#guard (EVM.transientLoad firstCall.2.1 owner ⟨0⟩).toNat = 77
#guard (EVM.storageLoad firstCall.2.1 owner ⟨0⟩).toNat = 777
#guard (runMessage firstCall.2.1 owner getCode).2.2 = Ethereum.UInt256.toByteArray ⟨77⟩
#guard (runMessage firstCall.2.1 owner getCode false).1
#guard !(runMessage firstCall.2.1 owner setCode false).1
#guard (EVM.transientLoad (runMessage firstCall.2.1 owner setCode false).2.1 owner ⟨0⟩).toNat
  = 77
#guard !(runMessage firstCall.2.1 owner revertCode).1
#guard (EVM.transientLoad (runMessage firstCall.2.1 owner revertCode).2.1 owner ⟨0⟩).toNat = 77
#guard (EVM.transientLoad (runMessage firstCall.2.1 other setCode).2.1 owner ⟨0⟩).toNat = 77
#guard (EVM.transientLoad (runMessage firstCall.2.1 other setCode).2.1 other ⟨0⟩).toNat = 77

end Solm.TransientTests
