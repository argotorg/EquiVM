import Solidity.Test.Scenarios.ERC20
import Solidity.Test.Scenarios.Ballot
import Solidity.Test.Scenarios.SimpleAuction
import Solidity.Test.Scenarios.Truth
import Solidity.Test.Scenarios.Pow
import Solidity.Test.Scenarios.Caller
import Solidity.Test.Scenarios.Reuse
import Solidity.Test.Scenarios.CtorStore
import Solidity.Test.Scenarios.CtorTruth
import Solidity.Test.Scenarios.StringStoreLite
import Solidity.Test.Scenarios.TinyImmutable
import Solidity.Test.Scenarios.BlindAuction
import Solidity.Test.Scenarios.Ownable2Step
import Solidity.Test.Scenarios.AccessControl
import Solidity.Test.Scenarios.Pausable
import Solidity.Test.Scenarios.ERC6909
import Solidity.Test.Scenarios.Factory
import Solidity.Test.Scenarios.HexLit
import Solidity.Test.Scenarios.TryCatch
import Solidity.Test.Scenarios.BaseCall
import Solidity.Test.Scenarios.Ecrecover
import Solidity.Test.Scenarios.Fixes

/-!
# `solidity-diff`

Native keccak is only available in a compiled executable, so everything keccak-dependent is
checked here: selectors of the elaborated dispatch tables against `solc --hashes`, storage
locations (mapping / dynamic-array slots) against the hand-written Sol⁻ layouts, and the
differential scenarios (EVM on pinned bytecode vs the interpreter on the Solidity spec).
-/

namespace Solidity.Test

open Solidity

def selectorHex (sig : String) : String :=
  hexOfBytes ((ffi.KEC sig.toUTF8).extract 0 4)

/-! ## Self-check -/

def erc20Sigs : List (String × String) :=
  [ ("transfer(address,uint256)", "a9059cbb"),
    ("approve(address,uint256)", "095ea7b3"),
    ("transferFrom(address,address,uint256)", "23b872dd"),
    ("balanceOf(address)", "70a08231"),
    ("allowance(address,address)", "dd62ed3e"),
    ("totalSupply()", "18160ddd") ]

def selfcheck : IO Bool := do
  let empty := hexOfBytes (ffi.KEC ByteArray.empty)
  let mut ok := empty == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
  for (sig, expected) in erc20Sigs do
    ok := ok && selectorHex sig == expected
  IO.println s!"selfcheck: keccak(empty) = {empty} — {if ok then "OK" else "FAILED"}"
  return ok

/-! ## Selectors -/

structure SpecEntry where
  name : String
  program : Program
  target : String
  selectors : List (String × String)
  /-- Sol⁻ storage layout to compare against, with sample paths. -/
  solmLayout : Option (Storage.StorageLayout × List Solm.EvaledStorageRef) := none

def sortPairs (xs : List (String × String)) : List (String × String) :=
  xs.mergeSort fun a b => decide (a.1 ≤ b.1)

def checkSelectors (e : SpecEntry) : IO Bool := do
  match elabProgram e.program e.target with
  | .error err =>
    IO.println s!"[{e.name}] elaboration error: {err}"
    return false
  | .ok fc =>
    let computed := sortPairs (fc.entries.map fun d => (d.sigStr, selectorHex d.sigStr))
    let expected := sortPairs e.selectors
    let ok := computed == expected
    IO.println s!"[{e.name}] selectors: {if ok then "OK" else "MISMATCH"} ({computed.length} entries)"
    unless ok do
      IO.println s!"  computed: {computed}"
      IO.println s!"  expected: {expected}"
    return ok

/-! ## Layout -/

def locStr : Option Storage.StorageLoc → String
  | none => "none"
  | some l => s!"slot={l.slot.toNat} off={l.offset.val} size={l.size.val} bit={repr l.bitOffset} ty={repr l.type}"

def sameLoc : Option Storage.StorageLoc → Option Storage.StorageLoc → Bool
  | none, none => true
  | some a, some b =>
    a.slot == b.slot && a.offset.val == b.offset.val && a.size.val == b.size.val &&
      a.bitOffset == b.bitOffset && a.type == b.type
  | _, _ => false

def checkLayout (e : SpecEntry) : IO Bool := do
  let some (solm, refs) := e.solmLayout | return true
  match elabProgram e.program e.target with
  | .error err =>
    IO.println s!"[{e.name}] elaboration error: {err}"
    return false
  | .ok fc =>
    let some table := fc.layoutTable? | IO.println s!"[{e.name}] no layout"; return false
    let evm : EVM.State := default
    let mut ok := true
    for ref in refs do
      let ours := Solidity.layout table ref evm
      let theirs := solm.layout ref evm
      let same := sameLoc ours theirs
      ok := ok && same
      unless same do
        IO.println s!"  {ref.base}{repr ref.steps}: ours={locStr ours} solm={locStr theirs}"
    IO.println s!"[{e.name}] layout ({refs.length} paths): {if ok then "OK" else "MISMATCH"}"
    return ok

/-! ## The examples -/

def kAddr (n : Nat) : Solm.KeyValue := .address (.ofNat n)
def idx (n : Nat) : Solm.KeyValue := .int n
def b32 (n : Nat) : Solm.KeyValue := .fixedBytes ⟨31, by decide⟩ ((List.replicate 31 0) ++ [n.toUInt8])

def ref (base : String) (steps : List Solm.EvaledStorageRefStep := []) : Solm.EvaledStorageRef :=
  { base := base, steps := steps }

def specs : List SpecEntry :=
  [ { name := "Truth", program := Truth.SoliditySpec.program, target := "Truth",
      selectors := Truth.SoliditySpec.selectors },
    { name := "Pow", program := Pow.SoliditySpec.program, target := "Pow",
      selectors := Pow.SoliditySpec.selectors },
    { name := "Caller", program := Caller.SoliditySpec.program, target := "Caller",
      selectors := Caller.SoliditySpec.selectors,
      solmLayout := some (callerConfig.storage, [ref "stored"]) },
    { name := "Reuse", program := Reuse.SoliditySpec.program, target := "C",
      selectors := Reuse.SoliditySpec.selectors,
      solmLayout := some (cConfig.storage, [ref "s"]) },
    { name := "CtorStore", program := CtorStore.SoliditySpec.program, target := "CtorStore",
      selectors := CtorStore.SoliditySpec.selectors,
      solmLayout := some (ctorStoreConfig.storage, [ref "stored"]) },
    { name := "CtorTruth", program := CtorTruth.SoliditySpec.program, target := "CtorTruth",
      selectors := CtorTruth.SoliditySpec.selectors },
    { name := "ERC20", program := ERC20.SoliditySpec.program, target := "ERC20",
      selectors := ERC20.SoliditySpec.selectors,
      solmLayout := some (erc20Config.storage,
        [ ref "balanceOf" [.mindex (kAddr 0x1234)], ref "allowance" [.mindex (kAddr 1), .mindex (kAddr 2)],
          ref "totalSupply" ]) },
    { name := "StringStoreLite", program := StringStoreLite.SoliditySpec.program,
      target := "StringStoreLite", selectors := StringStoreLite.SoliditySpec.selectors,
      solmLayout := some (stringStoreLiteConfig.storage,
        [ ref "current" [.length], ref "current" [.aindex (idx 0)], ref "current" [.aindex (idx 5)] ]) },
    { name := "TinyImmutable", program := TinyImmutable.SoliditySpec.program, target := "TinyImmutable",
      selectors := TinyImmutable.SoliditySpec.selectors },
    { name := "Ballot", program := Ballot.SoliditySpec.program, target := "Ballot",
      selectors := Ballot.SoliditySpec.selectors,
      solmLayout := some (ballotConfig.storage,
        [ ref "chairperson",
          ref "voters" [.mindex (kAddr 7), .field "weight"], ref "voters" [.mindex (kAddr 7), .field "voted"],
          ref "voters" [.mindex (kAddr 7), .field "delegate"], ref "voters" [.mindex (kAddr 7), .field "vote"],
          ref "proposals" [.length], ref "proposals" [.aindex (idx 3), .field "name"],
          ref "proposals" [.aindex (idx 3), .field "voteCount"] ]) },
    { name := "SimpleAuction", program := SimpleAuction.SoliditySpec.program, target := "SimpleAuction",
      selectors := SimpleAuction.SoliditySpec.selectors,
      solmLayout := some (simpleAuctionConfig.storage,
        [ ref "beneficiary", ref "auctionEndTime", ref "highestBidder", ref "highestBid",
          ref "pendingReturns" [.mindex (kAddr 9)], ref "ended" ]) },
    { name := "BlindAuction", program := BlindAuction.SoliditySpec.program, target := "BlindAuction",
      selectors := BlindAuction.SoliditySpec.selectors,
      solmLayout := some (blindAuctionConfig.storage,
        [ ref "beneficiary", ref "biddingEnd", ref "revealEnd", ref "ended",
          ref "bids" [.mindex (kAddr 5), .length],
          ref "bids" [.mindex (kAddr 5), .aindex (idx 2), .field "blindedBid"],
          ref "bids" [.mindex (kAddr 5), .aindex (idx 2), .field "deposit"],
          ref "highestBidder", ref "highestBid", ref "pendingReturns" [.mindex (kAddr 5)] ]) },
    { name := "Ownable2Step", program := OpenZeppelinBench.Ownable2Step.SoliditySpec.program,
      target := "Ownable2StepBench", selectors := OpenZeppelinBench.Ownable2Step.SoliditySpec.selectors,
      solmLayout := some (OpenZeppelinBench.Ownable2Step.config.storage, [ref "_owner", ref "_pendingOwner"]) },
    { name := "AccessControl", program := OpenZeppelinBench.AccessControl.SoliditySpec.program,
      target := "AccessControlBench", selectors := OpenZeppelinBench.AccessControl.SoliditySpec.selectors,
      solmLayout := some (OpenZeppelinBench.AccessControl.config.storage,
        [ ref "_roles" [.mindex (b32 1), .field "adminRole"],
          ref "_roles" [.mindex (b32 1), .field "hasRole", .mindex (kAddr 3)] ]) },
    { name := "Pausable", program := OpenZeppelinBench.Pausable.SoliditySpec.program,
      target := "PausableBench", selectors := OpenZeppelinBench.Pausable.SoliditySpec.selectors,
      solmLayout := some (OpenZeppelinBench.Pausable.config.storage, [ref "_paused"]) },
    { name := "ERC6909", program := OpenZeppelinBench.ERC6909.SoliditySpec.program,
      target := "ERC6909Bench", selectors := OpenZeppelinBench.ERC6909.SoliditySpec.selectors,
      solmLayout := some (OpenZeppelinBench.ERC6909.config.storage,
        [ ref "_balances" [.mindex (kAddr 1), .mindex (idx 7)],
          ref "_operatorApprovals" [.mindex (kAddr 1), .mindex (kAddr 2)],
          ref "_allowances" [.mindex (kAddr 1), .mindex (kAddr 2), .mindex (idx 7)] ]) } ]

def runAll (f : SpecEntry → IO Bool) : IO Bool := do
  let mut ok := true
  for e in specs do
    ok := (← f e) && ok
  return ok

/-! ## Differential scenarios -/

def scenarios : List Scenario :=
  [ ERC20.scenario, ERC20.scenarioSolc, ERC20.scenarioPinnedCtor, Ballot.scenario,
    Ballot.scenarioSolc, SimpleAuction.scenario, SimpleAuction.scenarioSolc,
    SimpleAuction.scenarioPinnedCtor, Truth.scenario, Truth.scenarioSolc, Pow.scenario,
    Pow.scenarioSolc, Pow.scenarioPinnedCtor, Caller.scenario, Caller.scenarioSolc,
    Caller.scenarioPinnedCtor, Reuse.scenario, Reuse.scenarioSolc, Reuse.scenarioPinnedCtor,
    CtorStore.scenario, CtorStore.scenarioSolc, CtorStore.scenarioPinnedCtor, CtorTruth.scenario,
    CtorTruth.scenarioSolc, CtorTruth.scenarioPinnedCtor, StringStoreLite.scenario,
    StringStoreLite.scenarioSolc, StringStoreLite.scenarioPinnedCtor, TinyImmutable.scenario,
    BlindAuction.scenario, BlindAuction.scenarioSolc, BlindAuction.scenarioPinnedCtor,
    Ownable2Step.scenario, Ownable2Step.scenarioSolc, AccessControl.scenario,
    AccessControl.scenarioSolc, Pausable.scenario, Pausable.scenarioSolc, ERC6909.scenario,
    ERC6909.scenarioSolc, Factory.scenario, HexLit.scenario, TryCatch.scenario, BaseCall.scenario, Ecrecover.scenario,
    Fixes.evalOrder, Fixes.blockScope, Fixes.modifierArgs, Fixes.superMod ]

def runDiff (only : Option String := none) : IO Bool := do
  let mut ok := true
  for s in scenarios do
    if only.all (· == s.name) then
      ok := (← runScenario s) && ok
  return ok

/-- Fuzz the primary scenarios (pinned runtime code) only. -/
def runFuzz (seed n : Nat) : IO Bool := do
  let mut ok := true
  for s in scenarios do
    unless s.name.any (· == '/') do
      ok := (← fuzzScenario s seed n) && ok
  return ok

end Solidity.Test

open Solidity.Test in
def main (args : List String) : IO UInt32 := do
  let results ← match args with
    | [] | ["--selfcheck"] => do pure [← selfcheck]
    | ["--selectors"] => do pure [← runAll checkSelectors]
    | ["--layout"] => do pure [← runAll checkLayout]
    | ["--diff"] => do pure [← runDiff]
    | ["--diff", name] => do pure [← runDiff (some name)]
    | ["--fuzz"] => do pure [← runFuzz 1 30]
    | ["--fuzz", seed, n] => do pure [← runFuzz (seed.toNat!) (n.toNat!)]
    | ["--all"] => do pure [← selfcheck, ← runAll checkSelectors, ← runAll checkLayout, ← runDiff, ← runFuzz 1 30]
    | _ =>
      IO.eprintln s!"usage: solidity-diff [--selfcheck | --selectors | --layout | --diff [scenario] | --fuzz [seed n] | --all]"
      pure [false]
  let ok := results.all id
  IO.println (if ok then "ALL OK" else "FAILURES")
  return if ok then 0 else 1
