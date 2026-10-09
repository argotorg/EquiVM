import Benchmarks.Dss.LinearDecrease.Spec
import Solm.Notation

/-!
# LinearDecrease spec in the Solidity-faithful Solm frontend

The whole `abaci.sol` `LinearDecrease` spec written with `solidity%` and proven definitionally
equal to the AST spec in `Spec.lean`.  Checked-math helpers are inlined as surface statements;
`"tau"` is the big-endian `bytes32` literal; `#RAY` is the spec's `RAY` constant.
Transition order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation Benchmarks.Dss.LinearDecrease

namespace Benchmarks.Dss.LinearDecrease.Syntax

def contractSyntax : ContractDecl := solidity% contract LinearDecrease {
  mapping(address => uint256) wards;
  uint256 tau;

  constructor() {
    wards[msg.sender] = 1;
  }

  function add(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x + y) as uint256;
    require(z >= x);
    return z;
  }

  function mul(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x * y) as uint256;
    require(y == 0 || z / y == x);
    return z;
  }

  function rmul(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x * y) as uint256;
    require(y == 0 || z / y == x);
    z = z / #RAY;
    return z;
  }

  function deny(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 0;
  }

  function file(bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x7461750000000000000000000000000000000000000000000000000000000000)) {
      tau = data;
    } else {
      require(false);
    }
  }

  function price(uint256 top, uint256 dur) external returns (uint256) {
    if (dur >= tau) {
      return 0;
    } else {
      uint256 left = (tau - dur) as uint256;
      var scaled = mul(left, #RAY);
      uint256 ratio = scaled / tau;
      var out = rmul(top, ratio);
      return out;
    }
  }

  function rely(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 1;
  }

  function tau() external returns (uint256) {
    return tau;
  }

  function wards(address arg0) external returns (uint256) {
    return wards[arg0];
  }
}

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.LinearDecrease.contract := by rfl

end Benchmarks.Dss.LinearDecrease.Syntax
