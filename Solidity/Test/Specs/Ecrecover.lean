import Solidity

/-! Ec (`Solidity/Test/Fixtures/Ecrecover.sol`): the `ecrecover` global function.  Harness input only. -/

namespace Ecrecover.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def ec : SourceUnit := sol% contract Ec {
  address public last;

  function rec(bytes32 h, uint8 v, bytes32 r, bytes32 s) external pure returns (address) {
    return ecrecover(h, v, r, s);
  }

  function recStore(bytes32 h, uint8 v, bytes32 r, bytes32 s) external {
    last = ecrecover(h, v, r, s);
  }

  function recNonZero(bytes32 h, uint8 v, bytes32 r, bytes32 s) external pure returns (address) {
    address a = ecrecover(h, v, r, s);
    require(a != address(0), "bad sig");
    return a;
  }
}

def program : Program := [ec]

end Ecrecover.SoliditySpec
