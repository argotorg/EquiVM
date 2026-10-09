import Benchmarks.EAS.EAS.DiffTarget

/-!
Check that validation of a later batch request does not precede an earlier write.
Run with `lake env lean --run Benchmarks/EAS/EAS/CalldataOrderCheck.lean`.
Every case must agree, including malformed input in both permission modes.
-/

open Solm Solm.Interp Solm.DiffTest Ethereum Ethereum.EVM

private def bytes32 (n : Nat) : Value :=
  .fixedBytes ⟨31, by decide⟩ (wordBytes n).toList

private def encodeCall (name : String) (args : List Value) : IO ByteArray := do
  let t := Benchmarks.EAS.EAS.fixtureTarget
  let some transition := t.contract.transitions.find? (·.name == name)
    | throw (IO.userError s!"missing {name} transition")
  let selector := (Ethereum.KEC (transitionSigStr transition).toUTF8).extract 0 4
  let some calldata := ABI.encodeCallWithSelector? selector (transition.params.map Param.ty) args
    | throw (IO.userError "fixture encoding failed")
  return calldata

private def wordAt (input : ByteArray) (offset : Nat) : Nat :=
  (ABI.bytesToWord (input.extract offset (offset + 32)).toList).toNat

private def check (label : String) (input : ByteArray) (perm : Bool) (expected : String)
    (accounts : AccountMap) : IO Bool := do
  let t := Benchmarks.EAS.EAS.fixtureTarget
  let result := runCase t
    { label := label, σ := accounts,
      I := t.env t.runtime (EVM.address 0x6004) 0 input perm 1000 16756728 }
  IO.println s!"{label}, perm={perm}: {result.verdict.describe}"
  let actual := match result.evmResult with
    | .error .StaticModeViolation => "static"
    | .ok (.success _ _) => "success"
    | .ok (.revert _ _) => "revert"
    | _ => "unexpected"
  unless actual == expected do
    IO.eprintln s!"expected {expected}, got {describeEvm result.evmResult}"
  return result.verdict.isAgree && actual == expected

def main : IO UInt32 := do
  let t := Benchmarks.EAS.EAS.fixtureTarget
  let data : Value := .tuple [.address (EVM.address 0x6004), .int 0,
    .bool true, bytes32 0, .bytes (wordBytes 99), .int 0]
  let row : Value := .tuple [bytes32 0, .array [data]]
  let calldata ← encodeCall "multiAttest" [.array [row, row]]
  -- Absolute byte 100 holds the second request's offset, relative to byte 68.
  let malformed := replaceWord calldata 100 65536
  let mut failed := false
  for (label, input, valid) in [("canonical", calldata, true), ("bad second request", malformed, false)] do
    for perm in [true, false] do
      let expected := if !perm then "static" else if valid then "success" else "revert"
      unless ← check label input perm expected t.world do failed := true

  let signature : Value := .tuple [.int 27, bytes32 0, bytes32 0]
  let delegatedRow : Value := .tuple [bytes32 0, .array [data, data],
    .array [signature, signature], .address (EVM.address 0x6004)]
  let delegated ← encodeCall "multiAttestByDelegation" [.array [delegatedRow, delegatedRow]]
  let heads := 4 + wordAt delegated 4 + 32
  let request := heads + wordAt delegated heads
  let dataHeads := request + wordAt delegated (request + 32) + 32
  let signatures := request + wordAt delegated (request + 64) + 32
  for (label, input, expected) in [
      ("delegated attest canonical", delegated, "static"),
      ("delegated attest bad second request", replaceWord delegated (heads + 32) 65536, "static"),
      ("delegated attest bad second datum", replaceWord delegated (dataHeads + 32) 65536, "static"),
      ("delegated attest dirty second signature", replaceWord delegated (signatures + 96) 256, "static"),
      ("delegated attest bad first datum", replaceWord delegated dataHeads 65536, "revert"),
      ("delegated attest dirty first signature", replaceWord delegated signatures 256, "revert"),
      ("delegated attest dirty attester", replaceWord delegated (request + 96) (2^160), "revert"),
      ("delegated attest invalid signatures tail", replaceWord delegated (request + 64) 65536, "revert")] do
    unless ← check label input false expected t.world do failed := true

  let revokeData : Value := .tuple [bytes32 1, .int 0]
  let delegatedRevokeRow : Value := .tuple [bytes32 0, .array [revokeData, revokeData],
    .array [signature, signature], .address (EVM.address 0x6004)]
  let revoke ← encodeCall "multiRevokeByDelegation" [.array [delegatedRevokeRow, delegatedRevokeRow]]
  let request := 68 + wordAt revoke 68
  let signatures := request + wordAt revoke (request + 64) + 32
  for (label, input, expected) in [
      ("delegated revoke canonical", revoke, "static"),
      ("delegated revoke bad second request", replaceWord revoke 100 65536, "static"),
      -- Revocation copies the entire request, including both signatures, before verification.
      ("delegated revoke dirty second signature", replaceWord revoke (signatures + 96) 256, "revert")] do
    unless ← check label input false expected t.world do failed := true

  let .ok (accounts, uid1) := Benchmarks.EAS.EAS.fixtureCall t t.world "attest" [.tuple [bytes32 0, data]]
    | throw (IO.userError "first attestation fixture failed")
  let .ok (accounts, uid2) := Benchmarks.EAS.EAS.fixtureCall t accounts "attest" [.tuple [bytes32 0, data]]
    | throw (IO.userError "second attestation fixture failed")
  let revokeRow (uid : ByteArray) : Value := .tuple [bytes32 0,
    .array [.tuple [.fixedBytes ⟨31, by decide⟩ uid.toList, .int 0]]]
  let revoke ← encodeCall "multiRevoke" [.array [revokeRow uid1, revokeRow uid2]]
  for (label, input, valid) in [("revoke canonical", revoke, true),
      ("revoke bad second request", replaceWord revoke 100 65536, false)] do
    for perm in [true, false] do
      let expected := if !perm then "static" else if valid then "success" else "revert"
      unless ← check label input perm expected accounts do failed := true
  return if failed then 1 else 0
