import Solidity.Test.Specs.OZ.Access

/-! Ownable2StepBench (`Examples/OpenZeppelinBench/Ownable2Step/Ownable2StepBench.sol`) in the
Solidity spec language, with its OpenZeppelin bases. -/

namespace OpenZeppelinBench.Ownable2Step.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation OpenZeppelinBench.OZ

def bench : SourceUnit := sol% contract Ownable2StepBench is Ownable2Step {
  constructor(address initialOwner) Ownable(initialOwner) {}
}

def program : Program := [context, ownable, ownable2Step, bench]
def target : String := "Ownable2StepBench"

#guard (bench.contract?.bind (·.ctor?)).map (·.modifiers.map (·.name)) = some ["Ownable"]

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) :=
  [ ("acceptOwnership()", "79ba5097"),
    ("owner()", "8da5cb5b"),
    ("pendingOwner()", "e30c3978"),
    ("renounceOwnership()", "715018a6"),
    ("transferOwnership(address)", "f2fde38b") ]

end OpenZeppelinBench.Ownable2Step.SoliditySpec
