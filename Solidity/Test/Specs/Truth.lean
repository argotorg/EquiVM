import Solidity

/-! Truth (`Examples/Truth/Truth.sol`) in the Solidity spec language. -/

namespace Truth.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def truth : SourceUnit := sol% contract Truth {
  function truth() external pure returns (bool) {
    return true;
  }
}

def program : Program := [truth]
def target : String := "Truth"

#guard (truth.contract?.map (·.functions.length)) = some 1

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) :=
  [ ("truth()", "9e9f51d2") ]

end Truth.SoliditySpec
