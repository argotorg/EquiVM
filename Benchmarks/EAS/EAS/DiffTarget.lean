import Solm.DiffTest.Harness
import Benchmarks.EAS.EAS.Spec
import Benchmarks.EAS.EAS.Bytecode
import Benchmarks.EAS.EAS.ImmutableCode

/-!
# EAS differential target

The runtime is EAS v0.26 recompiled with Solidity 0.8.32. The immutable valuation
uses the original mainnet constructor environment as a reference. The schema-registry
fixture returns a record with a resolver for odd schema words and one without a
resolver for even words. Extra accounts exercise bool returns and ETH refunds.
The ERC-1271 fixture is supplied as requested, but EAS v0.26 does not call it:
its delegated paths call the ECDSA precompile at address 1.
-/

open Solm Solm.DiffTest

namespace Benchmarks.EAS.EAS

def mainnetImmutables : Store := (∅ : Store)
  |>.insert "_HASHED_NAME" (.int 0x9fed719e0073f95229e6f4f6b6f28f260c524ab08aa40b11f9c28cb710d7c72a)
  |>.insert "_HASHED_VERSION" (.int 0x83db343c12693770eafd99637d8f0bd997774ed25c402f824d1ac79f642587c8)
  |>.insert "_TYPE_HASH" (.int 0x8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f)
  |>.insert "_CACHED_CHAIN_ID" (.int 0x0000000000000000000000000000000000000000000000000000000000000001)
  |>.insert "_CACHED_THIS" (.address (EVM.address 0x000000000000000000000000a1207f3bba224e2c9c3c6d5af63d0eb1582ce587))
  |>.insert "_CACHED_DOMAIN_SEPARATOR" (.int 0x1b86e1aefca1c2cc067f67f9d06e2f79c85094c488f7c6b8d7bc828a69952348)
  |>.insert "_schemaRegistry" (.address (EVM.address 0x000000000000000000000000a7b39296258348c78294f95b872b282326a97bdf))

/-- ABI-encoded (bytes32,address,bool,string) returned as one dynamic tuple. -/
def schemaReturn (resolver : Nat) : ByteArray :=
  wordBytes 32 ++ wordBytes 1 ++ wordBytes resolver ++ wordBytes 1 ++ wordBytes 128 ++ wordBytes 0

/-- Return schema uid 1, a resolver selected by the requested uid's low bit,
    revocable=true, and an empty schema string. The record's ABI head is at 32. -/
def schemaRegistryCode : ByteArray :=
  ⟨#[0x60, 0x20, 0x60, 0x00, 0x52,
     0x60, 0x01, 0x60, 0x20, 0x52,
     0x60, 0x04, 0x35, 0x60, 0x01, 0x16, 0x61, 0x60, 0x02, 0x02, 0x60, 0x40, 0x52,
     0x60, 0x01, 0x60, 0x60, 0x52,
     0x60, 0x80, 0x60, 0x80, 0x52,
     0x60, 0x00, 0x60, 0xa0, 0x52,
     0x60, 0xc0, 0x60, 0x00, 0xf3]⟩

def easCallees : List (EVM.Address × ByteArray) :=
  [ (EVM.address 0xa7b39296258348c78294f95b872b282326a97bdf, schemaRegistryCode),
    (EVM.address 0x6000, callee (schemaReturn 0x6002)),
    (EVM.address 0x6001, callee (schemaReturn 0)),
    -- isPayable(), attest(), revoke(), multiAttest(), and multiRevoke(): true.
    (EVM.address 0x6002, callee (wordBytes 1)),
    -- isValidSignature(bytes32,bytes): ERC-1271 magic bytes4, ABI left-aligned.
    (EVM.address 0x6003, callee (wordBytes (0x1626ba7e * 2 ^ 224))),
    -- A contract recipient which accepts an ETH refund.
    (EVM.address 0x6004, callee .empty) ]

def fixtureTarget : Target :=
  { name := "EAS", contract := contract, config := config,
    runtime := immutableLayout.deployed easBytecode mainnetImmutables,
    selfAddress := EVM.address 0xa1207f3bba224e2c9c3c6d5af63d0eb1582ce587,
    callers := [EVM.address 0x2000, EVM.address 0x6004],
    initcode := some easCreationBytecode,
    immutables := mainnetImmutables,
    runtimeCodeOf := some (immutableLayout.deployed easBytecode),
    callees := easCallees,
    words := [0, 0, 0, 1, 1, 2, 3, 27, 28, 32, 64, 255, 256, 1000, 10 ^ 18] }

private def fixtureBytes32 (n : Nat) : Value :=
  .fixedBytes ⟨31, by decide⟩ (wordBytes n).toList

/-- An ordinary ABI call, checked by the same EVM/replay comparison as the random suite. -/
def fixtureCall (t : Target) (accounts : Ethereum.AccountMap) (name : String)
    (args : List Value) (value : Nat := 0) : Except String (Ethereum.AccountMap × ByteArray) := do
  let some transition := t.contract.transitions.find? (·.name == name)
    | throw s!"unknown fixture transition: {name}"
  let selector := (Ethereum.KEC (transitionSigStr transition).toUTF8).extract 0 4
  let some calldata := ABI.encodeCallWithSelector? selector (transition.params.map Param.ty) args
    | throw s!"fixture arguments do not encode: {name}"
  let caller := EVM.address 0x6004
  let accounts := transferValue accounts caller t.selfAddress value
  let result := runCase t
    { label := s!"deterministic {name}", σ := accounts,
      I := t.env t.runtime caller value calldata true 1000 16756728 }
  unless result.verdict.isSuccess do
    throw s!"deterministic {name}: {result.verdict.describe}"
  match result.postState, result.evmResult with
  | some accounts, .ok (.success _ output) => return (accounts, output)
  | _, _ => throw s!"deterministic {name}: missing successful EVM result"

private def fixtureAttestData (payload : Nat) (value : Nat := 0) : Value :=
  .tuple [.address (EVM.address 0x6004), .int 0, .bool true, fixtureBytes32 0,
    .bytes (wordBytes payload), .int value]

/-- Successful nonempty batches and matching revocations, including forwarding and refunds.
    Kept separate from `diffTarget` so failures remain directly inspectable while developing. -/
def fixtureSequence : Except String (List String) := do
  let t := fixtureTarget
  let registry := EVM.address 0xa7b39296258348c78294f95b872b282326a97bdf
  let (verdict, deployed) := runConstructor t easCreationBytecode [.address registry] 0 (EVM.address 0x6004)
  unless verdict.isSuccess do throw s!"deterministic constructor: {verdict.describe}"
  let some accounts := deployed | throw "deterministic constructor: no post-state"
  unless (accounts.get? t.selfAddress).map (·.code) == some t.runtime do
    throw "deterministic constructor: deployed code differs from the patched 0.8.32 runtime"
  let (accounts, output) ← fixtureCall t accounts "attest"
    [.tuple [fixtureBytes32 0, fixtureAttestData 11]] 5
  unless output.size == 32 do throw "attest returned a non-word UID"
  let uid : Value := .fixedBytes ⟨31, by decide⟩ output.toList
  let (accounts, _) ← fixtureCall t accounts "getAttestation" [uid]
  let (accounts, _) ← fixtureCall t accounts "revoke"
    [.tuple [fixtureBytes32 0, .tuple [uid, .int 0]]]
  let (accounts, _) ← fixtureCall t accounts "attest"
    [.tuple [fixtureBytes32 1, fixtureAttestData 12 3]] 7
  let (accounts, output) ← fixtureCall t accounts "multiAttest"
    [.array [.tuple [fixtureBytes32 1, .array [fixtureAttestData 13 1, fixtureAttestData 14 2]]]] 9
  let some (.array uids) := ABI.decodeReturnValueWithMode? .modern
      (.dynamicArray (.elem (.bytes ⟨31, by decide⟩))) output
    | throw "multiAttest UIDs did not decode"
  unless uids.length == 2 do throw "multiAttest did not return two UIDs"
  let (accounts, _) ← fixtureCall t accounts "multiRevoke"
    [.array [.tuple [fixtureBytes32 1, .array (uids.map fun uid => .tuple [uid, .int 1])]]] 4
  let (accounts, _) ← fixtureCall t accounts "timestamp" [fixtureBytes32 101]
  let (accounts, _) ← fixtureCall t accounts "multiTimestamp"
    [.array [fixtureBytes32 102, fixtureBytes32 103]]
  let (accounts, _) ← fixtureCall t accounts "revokeOffchain" [fixtureBytes32 104]
  let (accounts, _) ← fixtureCall t accounts "multiRevokeOffchain"
    [.array [fixtureBytes32 105, fixtureBytes32 106]]
  let (_, _) ← fixtureCall t accounts "getDomainSeparator" []
  return ["constructor", "attest (no resolver)", "getAttestation", "revoke",
    "attest (resolver, payment, refund)", "multiAttest (two)", "multiRevoke (two)",
    "timestamp", "multiTimestamp", "revokeOffchain", "multiRevokeOffchain", "getDomainSeparator"]

def diffTarget : Target := fixtureTarget

end Benchmarks.EAS.EAS
