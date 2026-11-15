import Examples.ERC20.SpecSyntax
import Examples.ERC20.Bytecode
import Stele.DiffTest.Harness

/-!
# ERC20 specification checks, independent of the refinement proofs

Run with `lake env lean --run Examples/ERC20/SpecTests.lean`.
Boundary cases check independently specified outcomes and storage, as well as agreement with
the bytecode. Generated cases also exercise malformed calldata, nonpayability, and call sequences.
-/

open Stele Stele.DiffTest ABI Ethereum

namespace ERC20.SpecTests

private def target : Target :=
  { name := "ERC20", contract := Syntax.contractSyntax, config := erc20Config,
    runtime := erc20Bytecode, initcode := some erc20Initcode }

private def alice : EVM.Address := EVM.address 0x2000
private def bob : EVM.Address := EVM.address 0x3000
private def spender : EVM.Address := EVM.address 0x4000
private def maxWord : Nat := 2 ^ 256 - 1
private def balanceSlot (a : EVM.Address) : UInt256 := erc20BalanceOfSlot (.address a)
private def allowanceSlot : UInt256 := erc20AllowanceSlot (.address alice) (.address spender)

private def world (slots : List (UInt256 × Nat)) : AccountMap :=
  let acc := (target.world.get? target.selfAddress).getD default
  let storage := slots.foldl (fun st (slot, value) ↦ st.insert slot (UInt256.ofNat value)) acc.storage
  target.world.insert target.selfAddress { acc with storage }

private def checkSlots (label : String) (σ : AccountMap) (slots : List (UInt256 × Nat)) :
    IO Unit := do
  let acc := (σ.get? target.selfAddress).getD default
  for (slot, expected) in slots do
    let actual := (acc.storage.get? slot).getD ⟨0⟩
    unless actual.toNat == expected do
      throw <| IO.userError s!"{label}: expected storage {expected}, got {actual.toNat}"

private def check (label : String) (fn : TransitionDecl) (caller : EVM.Address)
    (args : List Value) (slots : List (UInt256 × Nat)) (expected : String)
    (after : List (UInt256 × Nat) := []) (returned : Nat := 1)
    (perm := true) (value := 0) : IO Unit := do
  let selector := (Ethereum.KEC (transitionSigStr fn).toByteArray).extract 0 4
  let some cd := encodeCallWithSelector? selector (fn.params.map Param.ty) args
    | throw <| IO.userError s!"{label}: invalid test arguments"
  let result := runCase target
    { label, σ := world slots, I := target.env target.runtime caller value cd perm }
  match result.verdict with
  | .agree how =>
      unless how == expected do
        throw <| IO.userError s!"{label}: expected {expected}, got {how}"
  | verdict => throw <| IO.userError s!"{label}: {verdict.describe}"
  if expected == "success" then
    let .ok (.success (σ, _, _) output) := result.evmResult
      | throw <| IO.userError s!"{label}: missing successful result"
    unless output == (UInt256.ofNat returned).toByteArray do
      throw <| IO.userError s!"{label}: unexpected return value"
    checkSlots label σ after
  IO.println s!"{label}: {result.verdict.describe}"

def run : IO UInt32 := do
  let a := balanceSlot alice
  let b := balanceSlot bob
  check "transfer" transferTransition alice [.address bob, .int 10]
    [(a, 100), (b, 7)] "success" [(a, 90), (b, 17)]
  check "self transfer at uint256 maximum" transferTransition alice [.address alice, .int 1]
    [(a, maxWord)] "success" [(a, maxWord)]
  check "zero transfer at uint256 maximum" transferTransition alice [.address bob, .int 0]
    [(b, maxWord)] "success" [(a, 0), (b, maxWord)]
  check "insufficient balance" transferTransition alice [.address bob, .int 10]
    [(a, 9)] "revert"
  check "recipient reaches uint256 maximum" transferTransition alice [.address bob, .int 1]
    [(a, 1), (b, maxWord - 1)] "success" [(a, 0), (b, maxWord)]
  check "recipient overflow" transferTransition alice [.address bob, .int 1]
    [(a, 1), (b, maxWord)] "revert"
  check "transferFrom" transferFromTransition spender [.address alice, .address bob, .int 10]
    [(allowanceSlot, 20), (a, 100), (b, 7)] "success"
    [(allowanceSlot, 10), (a, 90), (b, 17)]
  check "transferFrom self at uint256 maximum" transferFromTransition spender
    [.address alice, .address alice, .int 1] [(allowanceSlot, 20), (a, maxWord)] "success"
    [(allowanceSlot, 19), (a, maxWord)]
  check "insufficient allowance" transferFromTransition spender
    [.address alice, .address bob, .int 10] [(allowanceSlot, 9), (a, 100)] "revert"
  check "transferFrom insufficient balance" transferFromTransition spender
    [.address alice, .address bob, .int 10] [(allowanceSlot, 20), (a, 9)] "revert"
  check "transferFrom recipient overflow" transferFromTransition spender
    [.address alice, .address bob, .int 1]
    [(allowanceSlot, 20), (a, 100), (b, maxWord)] "revert"
  check "approve maximum" approveTransition alice [.address spender, .int maxWord]
    [] "success" [(allowanceSlot, maxWord)]
  check "balance getter" balanceOfTransition spender [.address alice]
    [(a, maxWord)] "success" [] maxWord
  check "allowance getter" allowanceTransition bob [.address alice, .address spender]
    [(allowanceSlot, 20)] "success" [] 20
  check "supply getter" totalSupplyTransition alice [] [(⟨2⟩, 100)] "success" [] 100
  check "static transfer" transferTransition alice [.address bob, .int 1]
    [(a, 100)] "static halt" (perm := false)
  check "static approve" approveTransition alice [.address spender, .int 1]
    [] "static halt" (perm := false)
  check "static transferFrom" transferFromTransition spender [.address alice, .address bob, .int 1]
    [(allowanceSlot, 20), (a, 100)] "static halt" (perm := false)
  check "nonpayable transfer" transferTransition alice [.address bob, .int 1]
    [(a, 100)] "revert" (value := 1)
  for supply in [0, 100, maxWord] do
    let (verdict, σ) := runConstructor target erc20Initcode [.int supply] 0 alice
    let (.agree "deployed", some σ) := (verdict, σ)
      | throw <| IO.userError s!"constructor {supply}: {verdict.describe}"
    checkSlots "constructor" σ [(a, supply), (⟨2⟩, supply)]
    IO.println s!"constructor {supply}: agree (deployed)"
  let summary := runTarget target 20261014 40
  IO.println s!"Generated cases: {summary.describe}"
  IO.println summary.coverage
  printFailures summary
  unless summary.agree == summary.cases do
    throw <| IO.userError "some generated cases failed or were inconclusive"
  return 0

end ERC20.SpecTests

def main : IO UInt32 := ERC20.SpecTests.run
