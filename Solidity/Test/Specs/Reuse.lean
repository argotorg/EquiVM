import Solidity

/-! Reuse (`Examples/Reuse/C.sol`) in the Solidity spec language: a public function that is also
called internally. -/

namespace Reuse.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def c : SourceUnit := sol% contract C {
  uint256 s;

  function f(uint256 v) public pure returns (uint256) {
    return v * 2 + 1;
  }

  function g(uint256 v) external {
    s = f(v);
  }
}

def program : Program := [c]
def target : String := "C"

#guard (c.contract?.map (·.functions.length)) = some 2

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) :=
  [ ("f(uint256)", "b3de648b"),
    ("g(uint256)", "e420264a") ]

end Reuse.SoliditySpec
