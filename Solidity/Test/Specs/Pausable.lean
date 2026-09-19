import Solidity.Test.Specs.OZ.Utils

/-! PausableBench (`Examples/OpenZeppelinBench/Pausable/PausableBench.sol`) in the Solidity spec
language, with its OpenZeppelin bases. -/

namespace OpenZeppelinBench.Pausable.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation OpenZeppelinBench.OZ

def bench : SourceUnit := sol% contract PausableBench is Pausable {
  function pause() external {
    _pause();
  }

  function unpause() external {
    _unpause();
  }

  function guardedWhenNotPaused() external view whenNotPaused returns (bool) {
    return true;
  }

  function guardedWhenPaused() external view whenPaused returns (bool) {
    return true;
  }
}

def program : Program := [context, pausable, bench]
def target : String := "PausableBench"

#guard (bench.contract?.map (·.functions.length)) = some 4

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) :=
  [ ("guardedWhenNotPaused()", "9bb8bcec"),
    ("guardedWhenPaused()", "ddf70309"),
    ("pause()", "8456cb59"),
    ("paused()", "5c975abb"),
    ("unpause()", "3f4ba83a") ]

end OpenZeppelinBench.Pausable.SoliditySpec
