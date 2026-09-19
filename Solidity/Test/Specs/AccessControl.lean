import Solidity.Test.Specs.OZ.Access

/-! AccessControlBench (`Examples/OpenZeppelinBench/AccessControl/AccessControlBench.sol`) in the
Solidity spec language, with its OpenZeppelin bases. -/

namespace OpenZeppelinBench.AccessControl.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation OpenZeppelinBench.OZ

def bench : SourceUnit := sol% contract AccessControlBench is AccessControl {
  constructor() {
    _grantRole(DEFAULT_ADMIN_ROLE, msg.sender);
  }
}

def program : Program := [context, ierc165, erc165, iAccessControl, accessControl, bench]
def target : String := "AccessControlBench"

#guard (accessControl.contract?.map (·.functions.length)) = some 11

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) :=
  [ ("DEFAULT_ADMIN_ROLE()", "a217fddf"),
    ("getRoleAdmin(bytes32)", "248a9ca3"),
    ("grantRole(bytes32,address)", "2f2ff15d"),
    ("hasRole(bytes32,address)", "91d14854"),
    ("renounceRole(bytes32,address)", "36568abe"),
    ("revokeRole(bytes32,address)", "d547741f"),
    ("supportsInterface(bytes4)", "01ffc9a7") ]

end OpenZeppelinBench.AccessControl.SoliditySpec
