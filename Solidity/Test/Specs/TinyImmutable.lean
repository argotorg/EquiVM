import Solidity

/-! TinyImmutable (`Examples/TinyImmutable/TinyImmutable.sol`) in the Solidity spec language. -/

namespace TinyImmutable.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def tinyImmutable : SourceUnit := sol% contract TinyImmutable {
  address public immutable owner;
  uint256 public immutable scale;

  constructor(address _owner, uint256 _scale, bool useScale) {
    owner = _owner;
    if (useScale) {
      scale = _scale;
    }
  }

  function quote(uint256 amount) external view returns (uint256) {
    require(msg.sender == owner, "owner");
    unchecked {
      return amount * scale;
    }
  }
}

def program : Program := [tinyImmutable]
def target : String := "TinyImmutable"

#guard (tinyImmutable.contract?.map (·.stateVars.map (·.mutability))) =
  some [.immutable, .immutable]

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) :=
  [ ("owner()", "8da5cb5b"),
    ("quote(uint256)", "ed1bd76c"),
    ("scale()", "f51e181a") ]

end TinyImmutable.SoliditySpec
