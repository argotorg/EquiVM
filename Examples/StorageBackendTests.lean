import Solm.MetaSolidityLayout
import Solm.Semantics

/-! Executable layout regressions for the compile-time Solidity generator. -/

namespace Examples.StorageBackendTests
open Solm ABI Ethereum

def uint256St : StorageType := .elem (.int (.uint ⟨256, by decide⟩))
def uint128St : StorageType := .elem (.int (.uint ⟨128, by decide⟩))
def boolSt : StorageType := .elem .bool
def addressSt : StorageType := .elem .address

def packedStruct : StorageType :=
  .struct "Packed" [("flag", boolSt), ("owner", addressSt), ("count", uint256St)]

def declarations : List StorageDecl :=
  [ { name := "first", ty := uint256St }
  , { name := "left", ty := uint128St }
  , { name := "right", ty := uint128St }
  , { name := "records", ty := .mapping .address (.dynamicArray packedStruct) }
  , { name := "tail", ty := boolSt }
  , { name := "blob", ty := .bytes }
  , { name := "direct", ty := packedStruct }
  , { name := "items", ty := .dynamicArray uint256St }
  , { name := "pairs", ty := .array packedStruct 2 }
  , { name := "afterPairs", ty := boolSt }
  ]

def layout : StorageLayout := solidityLayout! [([] : List StructDecl)] [declarations]

def leafSummary (ref : EvaledStorageRef) : Option (Nat × Nat × Nat) :=
  match layout ref with
  | some (.leaf loc) => some (loc.slot.toNat, loc.offset.val, loc.size.val)
  | _ => none

def anchorSummary (ref : EvaledStorageRef) : Option Nat :=
  match layout ref with
  | some (.anchor slot) => some slot.toNat
  | _ => none

def byteSummary (ref : EvaledStorageRef) : Option (Nat × Nat) :=
  match layout ref with
  | some (.byte header index) => some (header.toNat, index)
  | _ => none

-- A full-slot first declaration starts at slot zero (the old generator incorrectly returned one).
#guard leafSummary { base := "first" } = some (0, 0, 32)
-- Two uint128 declarations share slot one and advance to slot two afterwards.
#guard leafSummary { base := "left" } = some (1, 0, 16)
#guard leafSummary { base := "right" } = some (1, 16, 16)
-- The mapping root consumes slot two, even though it has no directly readable leaf.
#guard leafSummary { base := "tail" } = some (3, 0, 1)
-- A dynamic value following a packed scalar starts at the next slot. Its indexed byte retains
-- the header and logical index; the backend resolves short or long representation from the state.
#guard anchorSummary { base := "blob" } = some 4
#guard byteSummary { base := "blob", steps := [.aindex (.int 0)] } = some (4, 0)
-- Struct fields pack internally, while the full-width field starts the next word.
#guard leafSummary { base := "direct", steps := [.field "flag"] } = some (5, 0, 1)
#guard leafSummary { base := "direct", steps := [.field "owner"] } = some (5, 1, 20)
#guard leafSummary { base := "direct", steps := [.field "count"] } = some (6, 0, 32)
-- The struct occupies two complete words, so the following dynamic-array root starts at slot seven.
#guard anchorSummary { base := "items" } = some 7
-- Struct sizes are byte counts, so fixed-array elements advance by the struct's two-word stride.
#guard leafSummary { base := "pairs", steps := [.aindex (.int 0), .field "flag"] } = some (8, 0, 1)
#guard leafSummary { base := "pairs", steps := [.aindex (.int 0), .field "count"] } = some (9, 0, 32)
#guard leafSummary { base := "pairs", steps := [.aindex (.int 1), .field "count"] } = some (11, 0, 32)
#guard leafSummary { base := "afterPairs" } = some (12, 0, 1)

def generatedBackend : StorageBackend :=
  solidityStorage! [([] : List StructDecl)] [declarations]

private def noExternalCalls : ExternalCallABI where
  encode? := fun _ _ => none
  decode? := fun _ _ => none

/-- A representative configuration using generated operation-owned storage, rather than the
    compatibility fallback. -/
def generatedConfig : Config :=
  { storageBackend := generatedBackend
    externalABI := noExternalCalls
    selfDeployment := fun _ _ => none }

example : generatedConfig.storageBackend = generatedBackend := rfl

example (er : EvaledStorageRef) (ty : StorageType) (evm : EVM.State) :
    generatedConfig.storageBackend.read er ty evm = generatedBackend.read er ty evm := by
  rfl

example (ref : EvaledStorageRef) :
    generatedBackend.locate? ref = layout ref := by
  rfl

/-! ## Executable backend-law regressions

These checks exercise the operation-owned interface itself, not just its optional `locate?`
oracle.  The state contains the contract account required by `EVM.storageStore`, so successful
mutations are observable by subsequent backend operations.
-/

def backendTestState : EVM.State :=
  let evm : EVM.State := default
  evm.setAccount evm.executionEnv.codeOwner default

def scalarRoundTrip : EvalResult Value := do
  let evm' <- generatedBackend.write { base := "left" } uint128St (.int 42) backendTestState
  generatedBackend.read { base := "left" } uint128St evm'

#guard scalarRoundTrip = .ok (.int 42)

-- Writing the low half of a packed word leaves its high-half neighbour unchanged.
def packedWriteFrame : EvalResult Value := do
  let evm' <- generatedBackend.write { base := "left" } uint128St (.int 42) backendTestState
  generatedBackend.read { base := "right" } uint128St evm'

#guard packedWriteFrame = .ok (.int 0)

def scalarClearRead : EvalResult Value := do
  let evm' <- generatedBackend.write { base := "left" } uint128St (.int 42) backendTestState
  let evm'' <- generatedBackend.clear { base := "left" } uint128St evm'
  generatedBackend.read { base := "left" } uint128St evm''

#guard scalarClearRead = .ok (.int 0)

def packedValue (flag : Bool) (owner count : Nat) : Value :=
  .struct "Packed"
    [("flag", .bool flag),
     ("owner", .address (.ofNat owner)),
     ("count", .int count)]

def structRoundTrip : EvalResult Value := do
  let value := packedValue true 5 9
  let evm' <- generatedBackend.write { base := "direct" } packedStruct value backendTestState
  generatedBackend.read { base := "direct" } packedStruct evm'

#guard structRoundTrip = .ok (packedValue true 5 9)

def pairsTy : StorageType := .array packedStruct 2

-- Statically known lengths come from the type and do not consult a layout location.
#guard generatedBackend.length { base := "pairs" } pairsTy backendTestState = .ok 2
#guard generatedBackend.length { base := "unused" }
  (.elem (.bytes ⟨31, by decide⟩)) backendTestState = .ok 32

def structArrayRoundTrip : EvalResult Value := do
  let value := Value.array [packedValue true 5 9, packedValue false 7 11]
  let evm' <- generatedBackend.write { base := "pairs" } pairsTy value backendTestState
  generatedBackend.read { base := "pairs" } pairsTy evm'

#guard structArrayRoundTrip =
  .ok (.array [packedValue true 5 9, packedValue false 7 11])

-- The multi-slot array ends before `afterPairs`; its write cannot affect that declaration.
def structArrayWriteFrame : EvalResult Value := do
  let value := Value.array [packedValue true 5 9, packedValue false 7 11]
  let evm' <- generatedBackend.write { base := "pairs" } pairsTy value backendTestState
  generatedBackend.read { base := "afterPairs" } boolSt evm'

#guard structArrayWriteFrame = .ok (.bool false)

def bytesRoundTrip : EvalResult Value := do
  let evm' <- generatedBackend.write { base := "blob" } .bytes
    (.bytes "abc".toByteArray) backendTestState
  generatedBackend.read { base := "blob" } .bytes evm'

#guard bytesRoundTrip = .ok (.bytes "abc".toByteArray)

def bytesClearLength : EvalResult Nat := do
  let evm' <- generatedBackend.write { base := "blob" } .bytes
    (.bytes "abc".toByteArray) backendTestState
  let evm'' <- generatedBackend.clear { base := "blob" } .bytes evm'
  generatedBackend.length { base := "blob" } .bytes evm''

#guard bytesClearLength = .ok 0

def bytesPushPop : EvalResult Value := do
  let evm' <- generatedBackend.write { base := "blob" } .bytes
    (.bytes "abc".toByteArray) backendTestState
  let evm'' <- generatedBackend.push { base := "blob" } .bytes
    (some (.fixedBytes ⟨0, by decide⟩ [100])) evm'
  let evm''' <- generatedBackend.pop { base := "blob" } .bytes evm''
  generatedBackend.read { base := "blob" } .bytes evm'''

#guard bytesPushPop = .ok (.bytes "abc".toByteArray)

def itemsTy : StorageType := .dynamicArray uint256St

def dynamicPushLength : EvalResult Nat := do
  -- A valueless push only mutates the length and therefore does not require evaluating Keccak in
  -- the command interpreter (the native Keccak symbol is linked only into executable targets).
  let evm' <- generatedBackend.push { base := "items" } itemsTy none backendTestState
  generatedBackend.length { base := "items" } itemsTy evm'

#guard dynamicPushLength = .ok 1

def dynamicPopEmptyReverts : Bool :=
  match generatedBackend.pop { base := "items" } itemsTy backendTestState with
  | .revert => true
  | _ => false

#guard dynamicPopEmptyReverts

end Examples.StorageBackendTests
