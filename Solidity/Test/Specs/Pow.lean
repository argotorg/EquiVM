import Solidity

/-! Pow (`Examples/Pow/Pow.sol`) in the Solidity spec language. -/

namespace Pow.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def pow : SourceUnit := sol% contract Pow {
  function pow2(uint256 n) public pure returns (uint256) {
    require(n < 256);
    uint256 r = 1;
    uint256 i = 0;
    while (i < n) {
      unchecked {
        r *= 2;
        i += 1;
      }
    }
    return r;
  }
}

def program : Program := [pow]
def target : String := "Pow"

#guard (pow.contract?.map (·.functions.length)) = some 1

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) :=
  [ ("pow2(uint256)", "442b7ffb") ]

end Pow.SoliditySpec
