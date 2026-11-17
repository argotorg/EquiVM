import Benchmarks.Midnight.DiffTarget

open Stele Stele.DiffTest ABI Ethereum Ethereum.EVM

namespace Benchmarks.Midnight.EdgeCases

def multicallInput (offset : Nat) : ByteArray :=
  ⟨#[0xac, 0x96, 0x50, 0xd8]⟩ ++ wordBytes 32 ++ wordBytes 1 ++ wordBytes offset

def rawReturnCases : List (String × ByteArray × Bool) :=
  [("empty", ⟨#[0x00]⟩, true),
   ("true32", ⟨#[0x60, 1, 0x5f, 0x52, 0x60, 32, 0x5f, 0xf3]⟩, true),
   ("true64", ⟨#[0x60, 1, 0x5f, 0x52, 0x60, 64, 0x5f, 0xf3]⟩, true),
   ("false", ⟨#[0x60, 32, 0x5f, 0xf3]⟩, false),
   ("dirty bool", ⟨#[0x60, 2, 0x5f, 0x52, 0x60, 32, 0x5f, 0xf3]⟩, false),
   ("short31", ⟨#[0x60, 1, 0x5f, 0x52, 0x60, 31, 0x5f, 0xf3]⟩, false),
   ("revert", ⟨#[0x5f, 0x5f, 0xfd]⟩, false),
   ("no code", .empty, false)]

def run : IO UInt32 := do
  -- The refinement quantifies over the current account map independently of I.code.
  -- STOP at the delegatecall target makes acceptance of an empty child call observable.
  let σ := diffTarget.world ⟨#[0x00]⟩
  for offset in [0, 32, 2^256 - 100, 2^256 - 99, 2^256 - 69,
      2^256 - 68, 2^256 - 64, 2^256 - 36, 2^255] do
    for perm in [true, false] do
      let c : Case := {
        label := s!"multicall nested offset {offset}, perm={perm}"
        σ := σ
        I := diffTarget.env diffTarget.runtime (EVM.address 0x2000) 0
          (multicallInput offset) perm }
      let result := runCase diffTarget c
      IO.println s!"{c.label}: {result.verdict.describe}"
      (← IO.getStdout).flush
      match result.verdict with
      | .agree _ => pure ()
      | _ => throw (IO.userError result.verdict.describe)
  let tr := (contract.transitions.find? (fun t => t.name == "claimSettlementFee")).get!
  let calldata := (ABI.encodeCallWithSelector? ⟨#[0x2a, 0xbd, 0xc1, 0x5e]⟩
    (transitionSignature tr).paramTypes
    [.address (EVM.address 0x7000), .int 0, .address (EVM.address 0x2000)]).getD .empty
  for (name, code, succeeds) in rawReturnCases do
    for perm in [true, false] do
      let σ := diffTarget.world
      let account := (σ.get? diffTarget.selfAddress).getD default
      let σ := σ.insert diffTarget.selfAddress { account with
        storage := account.storage.insert (.ofNat 11) (.ofNat 0x2000) }
      let σ := σ.insert (EVM.address 0x7000) { (default : Account) with code := code }
      let c : Case := {
        label := s!"token return {name}, perm={perm}"
        σ := σ
        I := diffTarget.env diffTarget.runtime (EVM.address 0x2000) 0 calldata perm }
      let result := runCase diffTarget c
      IO.println s!"{c.label}: {result.verdict.describe}"
      match result.verdict with
      | .agree _ =>
          if result.verdict.isSuccess != (succeeds && perm) then
            throw (IO.userError s!"unexpected success classification: {c.label}")
      | _ => throw (IO.userError result.verdict.describe)
  IO.println "All 34 decoder/return/static-mode edge cases agree."
  pure 0

end Benchmarks.Midnight.EdgeCases

def main : IO UInt32 := Benchmarks.Midnight.EdgeCases.run
