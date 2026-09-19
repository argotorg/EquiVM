import Solidity

/-! Factory / Child (`Solidity/Test/Fixtures/Factory.sol`): contract creation with `new`, plain, with
`value` and with `salt`, and a call on the created contract.  Harness input only. -/

namespace Factory.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def child : SourceUnit := sol% contract Child {
  uint public x;
  address public creator;

  constructor(uint v) payable {
    require(v != 7, "seven");
    x = v;
    creator = msg.sender;
  }

  function get() external view returns (uint) {
    return x;
  }
}

def factory : SourceUnit := sol% contract Factory {
  address public last;
  uint public count;

  function make(uint v) external payable returns (address) {
    Child c = new Child{value: msg.value}(v);
    last = address(c);
    count += 1;
    return address(c);
  }

  function make2(uint v, bytes32 salt) external returns (address) {
    Child c = new Child{salt: salt}(v);
    last = address(c);
    return address(c);
  }

  function makeAndRead(uint v) external returns (uint) {
    Child c = new Child(v);
    return c.get() + 1;
  }
}

def program : Program := [child, factory]
def target : String := "Factory"

#guard (factory.contract?.map (·.functions.length)) = some 3
#guard (child.contract?.bind (·.ctor?)).isSome

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) :=
  [ ("make(uint256)", "516517ab"), ("make2(uint256,bytes32)", "a5dcd9a2"), ("makeAndRead(uint256)", "341ed52e"),
    ("last()", "47799da8"), ("count()", "06661abd") ]

end Factory.SoliditySpec
