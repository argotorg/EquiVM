import Solidity

/-! Caller (`Examples/Caller/Caller.sol`) in the Solidity spec language: the `IPow` interface and
the calling contract. -/

namespace Caller.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def ipow : SourceUnit := sol% interface IPow {
  function pow2(uint256 n) external returns (uint256);
}

def caller : SourceUnit := sol% contract Caller {
  uint256 stored;

  function run(address t, uint256 n) external {
    stored = IPow(t).pow2(n);
  }
}

def program : Program := [ipow, caller]
def target : String := "Caller"

#guard (caller.contract?.map (·.functions.length)) = some 1
#guard (ipow.contract?.map (·.kind)) = some .interface

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) :=
  [ ("run(address,uint256)", "381fd190") ]

end Caller.SoliditySpec
