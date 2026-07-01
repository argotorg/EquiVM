import Examples.BytesStoreLite.Spec

/-!
# BytesStoreLite — executable storage checks

These checks exercise the Solm storage semantics for the byte-write paths in
`BytesStoreLite.sol`.  The Solidity source itself is compiled as part of the verification workflow;
these Lean examples make sure the corresponding storage references are writable and bounds-checked.
-/

open Solm ABI Ethereum

namespace BytesStoreLite

def baseFrame : Frame :=
  { contract := bytesStoreLiteContract, locals := ∅ }

def baseState : EVM.State :=
  (default : EVM.State).setSelfAccount default

def sampleBytes : ByteArray :=
  ⟨#[0x11, 0x22, 0x33]⟩

def currentSetup : EvalResult (Frame × EVM.State) :=
  assignStorageRef? bytesStoreLiteConfig baseFrame baseState .storage
    currentRef (.bytes sampleBytes)

def currentSetByteInBounds : EvalResult Value :=
  match currentSetup with
  | .ok (frame, evm) =>
      match assignStorageRef? bytesStoreLiteConfig frame evm .storage
          (currentByteRef (.intLit 1)) (.int 0xaa) with
      | .ok (_, evm') => readStorage? bytesStoreLiteConfig evm'
          { base := "current", steps := [.aindex (.int 1)] } uint8St
      | .revert => .revert
      | .error e => .error e
  | .revert => .revert
  | .error e => .error e

def isOkInt (expected : Int) : EvalResult Value -> Bool
  | .ok (.int actual) => actual == expected
  | _ => false

example : isOkInt 0xaa currentSetByteInBounds = true := by
  native_decide

def currentSetByteOutOfBounds : EvalResult (Frame × EVM.State) :=
  match currentSetup with
  | .ok (frame, evm) =>
      assignStorageRef? bytesStoreLiteConfig frame evm .storage
        (currentByteRef (.intLit 3)) (.int 0xaa)
  | .revert => .revert
  | .error e => .error e

def isRevert {α : Type} : EvalResult α -> Bool
  | .revert => true
  | _ => false

example : isRevert currentSetByteOutOfBounds = true := by
  native_decide

def packetSetup : EvalResult (Frame × EVM.State) :=
  assignStorageRef? bytesStoreLiteConfig baseFrame baseState .storage
    packetDataRef (.bytes sampleBytes)

def packetSetByteInBounds : EvalResult Value :=
  match packetSetup with
  | .ok (frame, evm) =>
      match assignStorageRef? bytesStoreLiteConfig frame evm .storage
          (packetDataByteRef (.intLit 2)) (.int 0xbb) with
      | .ok (_, evm') => readStorage? bytesStoreLiteConfig evm'
          { base := "packet", steps := [.field "data", .aindex (.int 2)] } uint8St
      | .revert => .revert
      | .error e => .error e
  | .revert => .revert
  | .error e => .error e

example : isOkInt 0xbb packetSetByteInBounds = true := by
  native_decide

def mappedSetup : EvalResult (Frame × EVM.State) :=
  assignStorageRef? bytesStoreLiteConfig baseFrame baseState .storage
    (mappedRef (.intLit 7)) (.bytes sampleBytes)

def mappedSetByteInBounds : EvalResult Value :=
  match mappedSetup with
  | .ok (frame, evm) =>
      match assignStorageRef? bytesStoreLiteConfig frame evm .storage
          (mappedByteRef (.intLit 7) (.intLit 0)) (.int 0xcc) with
      | .ok (_, evm') => readStorage? bytesStoreLiteConfig evm'
          { base := "mapped", steps := [.mindex (.int 7), .aindex (.int 0)] } uint8St
      | .revert => .revert
      | .error e => .error e
  | .revert => .revert
  | .error e => .error e

example (evm : EVM.State) :
    (bytesStoreLiteStorageLayout.layout
      { base := "mapped", steps := [.mindex (.int 7), .length] } evm).isSome = true := by
  simp [bytesStoreLiteStorageLayout, solidityStorageLayout, bytesStoreLiteLayout,
    bytesLikeLengthLoc, Solm.bytesLikeLengthLoc]

def chunkSetup : EvalResult (Frame × EVM.State) :=
  match pushArray? bytesStoreLiteConfig baseFrame baseState chunksRef
      (some (.bytes sampleBytes)) with
  | .ok evm => .ok (baseFrame, evm)
  | .revert => .revert
  | .error e => .error e

def chunkSetByteInBounds : EvalResult Value :=
  match chunkSetup with
  | .ok (frame, evm) =>
      match assignStorageRef? bytesStoreLiteConfig frame evm .storage
          (chunkByteRef (.intLit 0) (.intLit 1)) (.int 0xdd) with
      | .ok (_, evm') => readStorage? bytesStoreLiteConfig evm'
          { base := "chunks", steps := [.aindex (.int 0), .aindex (.int 1)] } uint8St
      | .revert => .revert
      | .error e => .error e
  | .revert => .revert
  | .error e => .error e

example (evm : EVM.State) :
    (bytesStoreLiteStorageLayout.layout
      { base := "chunks", steps := [.aindex (.int 0), .length] } evm).isSome = true := by
  simp [bytesStoreLiteStorageLayout, solidityStorageLayout, bytesStoreLiteLayout,
    chunksElemSlot?, nonnegativeIndexSlot?, bytesLikeLengthLoc, Solm.bytesLikeLengthLoc]

end BytesStoreLite
