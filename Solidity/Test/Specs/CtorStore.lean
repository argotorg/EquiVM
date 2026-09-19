import Solidity

/-! CtorStore (`Examples/CtorStore/CtorStore.sol`) in the Solidity spec language. -/

namespace CtorStore.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def ctorStore : SourceUnit := sol% contract CtorStore {
  uint256 private stored;

  constructor(uint256 x) payable {
    stored = x;
  }
}

def program : Program := [ctorStore]
def target : String := "CtorStore"

#guard (ctorStore.contract?.bind (·.ctor?)).map (·.mutability) = some .payable

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) := []

end CtorStore.SoliditySpec
