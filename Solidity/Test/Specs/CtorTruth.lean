import Solidity

/-! CtorTruth (`Examples/CtorTruth/CtorTruth.sol`) in the Solidity spec language. -/

namespace CtorTruth.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def ctorTruth : SourceUnit := sol% contract CtorTruth {
  constructor() payable { }

  function truth() external pure returns (bool) {
    return true;
  }
}

def program : Program := [ctorTruth]
def target : String := "CtorTruth"

#guard (ctorTruth.contract?.map (·.functions.length)) = some 1

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) :=
  [ ("truth()", "9e9f51d2") ]

end CtorTruth.SoliditySpec
