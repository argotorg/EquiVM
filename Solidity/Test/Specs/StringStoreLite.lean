import Solidity

/-! StringStoreLite (`Examples/StringStoreLite/StringStoreLite.sol`) in the Solidity spec
language. -/

namespace StringStoreLite.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def stringStoreLite : SourceUnit := sol% contract StringStoreLite {
  string private current;

  function set(string calldata value) external returns (uint256 currentBytes) {
    string memory copy = value;
    current = copy;
    currentBytes = bytes(copy).length;
  }

  function clearCurrent() external returns (uint256 oldBytes) {
    string memory copy = current;
    oldBytes = bytes(copy).length;
    delete current;
  }

  function currentLength() external view returns (uint256) {
    return bytes(current).length;
  }
}

def program : Program := [stringStoreLite]
def target : String := "StringStoreLite"

#guard (stringStoreLite.contract?.map (·.functions.length)) = some 3

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) :=
  [ ("clearCurrent()", "a6dfa262"),
    ("currentLength()", "a3d35f36"),
    ("set(string)", "4ed3885e") ]

end StringStoreLite.SoliditySpec
