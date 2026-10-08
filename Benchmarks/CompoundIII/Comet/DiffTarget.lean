import Solm.DiffTest.Harness
import Benchmarks.CompoundIII.Comet.Spec
import Benchmarks.CompoundIII.Comet.Bytecode
import Benchmarks.CompoundIII.Comet.ImmutableCode

/-!
# CometWithExtendedAssetList differential-test target

Registered in `Tests/DiffTest/Generated.lean`; run with `lake exe solm-difftest --only CometWithExtendedAssetList`.
The scaffold target is extended with ABI-specific callees and a deterministic constructor run.
The runtime and all 25 immutable values come from that run, checked against the runtime template.
-/

open Solm Solm.DiffTest Solm.Interp Ethereum Ethereum.EVM

namespace Benchmarks.CompoundIII.Comet

private def pushWord (n : Nat) : ByteArray := ⟨#[0x7f]⟩ ++ wordBytes n

private def returnWords (words : List Nat) : ByteArray :=
  let stores := words.zipIdx.foldl (fun code (word, i) ↦
    code ++ pushWord word ++ push2 (32 * i) ++ ⟨#[0x52]⟩) ByteArray.empty
  stores ++ push2 (32 * words.length) ++ ⟨#[0x60, 0, 0xf3]⟩

-- Each arm is a terminating EVM fragment. The default returns a recognizable raw byte string.
private def calleeDispatch (arms : List (Nat × ByteArray))
    (otherwise : ByteArray := ⟨#[0x60, 0, 0x60, 0, 0xfd]⟩) : ByteArray := Id.run do
  let mut offset := 6 + 11 * arms.length + 1 + otherwise.size
  let mut checks : ByteArray := ⟨#[0x60, 0, 0x35, 0x60, 0xe0, 0x1c]⟩
  let mut bodies := ByteArray.empty
  for (selector, body) in arms do
    checks := checks ++ ⟨#[0x80, 0x63]⟩ ++ (wordBytes selector).extract 28 32 ++
      ⟨#[0x14]⟩ ++ push2 offset ++ ⟨#[0x57]⟩
    bodies := bodies ++ ⟨#[0x5b, 0x50]⟩ ++ body
    offset := offset + 2 + body.size
  return checks ++ ⟨#[0x50]⟩ ++ otherwise ++ bodies

-- The ERC20 holds a signed offset from its initial 10^12 balance in slot zero. transferFrom
-- increases that balance; transfer decreases it. The full account effects are replayed by Solm.
private def tokenCode : ByteArray :=
  let balance := ⟨#[0x60, 0, 0x54]⟩ ++ pushWord (10 ^ 12) ++
    ⟨#[0x01, 0x60, 0, 0x52, 0x60, 32, 0x60, 0, 0xf3]⟩
  let transferIn := ⟨#[0x60, 68, 0x35, 0x60, 0, 0x54, 0x01, 0x60, 0, 0x55]⟩ ++ returnWords [1]
  let transferOut := ⟨#[0x60, 36, 0x35, 0x60, 0, 0x54, 0x03, 0x60, 0, 0x55]⟩ ++ returnWords [1]
  calleeDispatch [(0x313ce567, returnWords [6]), (0x70a08231, balance),
    (0x23b872dd, transferIn), (0xa9059cbb, transferOut), (0x095ea7b3, returnWords [1])]

private def priceFeedCode : ByteArray :=
  calleeDispatch [(0x313ce567, returnWords [8]),
    (0xfeaf968c, returnWords [1, 10 ^ 8, 1, 1, 1])]

private def assetListCode : ByteArray :=
  calleeDispatch [(0xc8c7fe6b, returnWords
    [0, 0x6002, 0x6001, 10 ^ 6, 8 * 10 ^ 17, 9 * 10 ^ 17, 95 * 10 ^ 16, 10 ^ 24]),
    (0xa46fe83b, returnWords [1])]

private def extensionCode : ByteArray :=
  calleeDispatch [(0x7042e2d8, returnWords [0x6004])] (returnWords [0xc0de])

def compoundCallees : List (EVM.Address × ByteArray) :=
  [(EVM.address 0x6000, tokenCode), (EVM.address 0x6001, priceFeedCode),
    (EVM.address 0x6002, tokenCode), (EVM.address 0x6003, extensionCode),
    (EVM.address 0x6004, calleeDispatch [(0xba15b9d1, returnWords [0x6005])]),
    (EVM.address 0x6005, assetListCode)]

-- Padding is only a layout directive: no expression can reach it. The concrete backend was
-- already generated from the full declarations, so removing this unused declaration from the
-- test contract avoids attempting to materialize a 256-bit-sized array of random test values.
def fixtureTarget : Target :=
  { name := "CometWithExtendedAssetList",
    contract := { contract with storage := contract.storage.filter (·.name != "__slotPadding") },
    config := config, runtime := cometWithExtendedAssetListBytecode,
    initcode := some cometWithExtendedAssetListCreationBytecode,
    immutables := initialImmutables contract,
    callers := [EVM.address 0x2000, EVM.address 0x3000, EVM.address 0x4000],
    runtimeCodeOf := some (immutableLayout.deployed cometWithExtendedAssetListBytecode),
    -- Repeated token entries weight the address pool toward the configured assets. They
    -- install identical code at the same addresses and do not change the test world.
    callees := List.replicate 12 (EVM.address 0x6000, tokenCode) ++
      List.replicate 12 (EVM.address 0x6002, tokenCode) ++ compoundCallees,
    words := (List.replicate 8 [0, 1, 10 ^ 3, 10 ^ 6, 10 ^ 15]).flatten ++
      [0, 1, 6, 8, 10 ^ 3, 10 ^ 6, 10 ^ 8, 10 ^ 12, 10 ^ 15, 10 ^ 18,
      8 * 10 ^ 17, 9 * 10 ^ 17, 10 ^ 24, 31536000, 2 ^ 104 - 1, 2 ^ 256 - 1] }

def deploymentArgs : List Value :=
  [.tuple [
    .address (EVM.address 0x2000), .address (EVM.address 0x3000),
    .address (EVM.address 0x6000), .address (EVM.address 0x6001),
    .address (EVM.address 0x6003),
    .int (8 * 10 ^ 17), .int 0, .int 0, .int 0,
    .int (8 * 10 ^ 17), .int 0, .int 0, .int 0,
    .int (5 * 10 ^ 17), .int (10 ^ 15), .int 0, .int 0,
    .int (10 ^ 6), .int 1, .int (10 ^ 15),
    .array [.tuple [.address (EVM.address 0x6002), .address (EVM.address 0x6001),
      .int 6, .int (8 * 10 ^ 17), .int (9 * 10 ^ 17), .int (95 * 10 ^ 16), .int (10 ^ 24)]]]]

def fixtureDeployment : Except String (ByteArray × Store) := do
  let t := fixtureTarget
  let some code := t.config.selfDeployment cometWithExtendedAssetListCreationBytecode deploymentArgs
    | throw "fixture constructor arguments do not encode"
  let accounts := t.world ByteArray.empty
  let env := t.env code (EVM.address 0x2000) 0 ByteArray.empty true
  let gas : UInt256 := .ofNat t.gas
  let trace := runTrace (initialState accounts accounts gas default env) (t.gas + 1)
  let some (outcome, replay) := solmCtorExecRun t.fuel replayOracle (Replay.ofTrace trace)
      t.config t.contract deploymentArgs accounts accounts gas default env
    | throw "fixture constructor parameters do not bind"
  let verdict := compareConstructor trace.xiResult outcome t.codeOf
  unless verdict.isAgree && replay.mismatches.isEmpty && replay.boundaries.isEmpty do
    throw s!"fixture deployment: {verdict.describe}; {replay.mismatches}"
  match trace.result, outcome with
  | .ok (.success _ runtime), .result (.returned frame _ _) =>
      return (runtime, frame.immutables)
  | _, _ => throw s!"fixture did not deploy: {verdict.describe}"

def diffTarget : Target :=
  letI : Inhabited Target := ⟨fixtureTarget⟩
  match fixtureDeployment with
  | .ok (runtime, immutables) => { fixtureTarget with runtime, immutables }
  | .error message => panic! message

end Benchmarks.CompoundIII.Comet
