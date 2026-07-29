import Benchmarks.Dss.StairstepExponentialDecrease.Spec
import Solm.Notation

/-!
# StairstepExponentialDecrease spec in the Solidity-faithful Solm frontend

The whole `abaci.sol` `StairstepExponentialDecrease` spec (including the `rpow` while-loop and
the two-way `file`) written with `solidity%` and proven definitionally equal to the AST spec in
`Spec.lean`.  Checked-math helpers are inlined; `"cut"`/`"step"` are big-endian `bytes32`
literals; `#RAY` is the spec's `RAY` constant.  Transition order matches `contract.transitions`.
-/

open Solm Solm.Notation Benchmarks.Dss.StairstepExponentialDecrease

namespace Benchmarks.Dss.StairstepExponentialDecrease.Syntax

def contractSyntax : ContractDecl := solidity% contract StairstepExponentialDecrease {
  mapping(address => uint256) wards;
  uint256 step;
  uint256 cut;

  constructor() {
    wards[msg.sender] = 1;
  }

  function rmul(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x * y) as uint256;
    require(y == 0 || z / y == x);
    z = z / #RAY;
    return z;
  }

  function rpow(uint256 x, uint256 n, uint256 b) internal returns (uint256) {
    if (n == 0) {
      return b;
    } else {
      if (x == 0) {
        return 0;
      } else {
        uint256 z = n % 2 == 0 ? b : x;
        uint256 half = b / 2;
        n = n / 2;
        while (n != 0) {
          uint256 xx = (x * x) as uint256;
          require(x == 0 || xx / x == x);
          uint256 xxRound = (xx + half) as uint256;
          require(xxRound >= xx);
          x = xxRound / b;
          if (n % 2 != 0) {
            uint256 zx = (z * x) as uint256;
            require(x == 0 || zx / x == z);
            uint256 zxRound = (zx + half) as uint256;
            require(zxRound >= zx);
            z = zxRound / b;
          }
          n = n / 2;
        }
        return z;
      }
    }
  }

  function cut() external returns (uint256) {
    return cut;
  }

  function deny(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 0;
  }

  function file(bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x6375740000000000000000000000000000000000000000000000000000000000)) {
      cut = data;
      require(data <= #RAY);
    } else {
      if (what == bytes32(0x7374657000000000000000000000000000000000000000000000000000000000)) {
        step = data;
      } else {
        require(false);
      }
    }
  }

  function price(uint256 top, uint256 dur) external returns (uint256) {
    uint256 n = dur / step;
    var pow = rpow(cut, n, #RAY);
    var out = rmul(top, pow);
    return out;
  }

  function rely(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 1;
  }

  function step() external returns (uint256) {
    return step;
  }

  function wards(address arg0) external returns (uint256) {
    return wards[arg0];
  }
}

theorem contractSyntax_eq :
    contractSyntax = Benchmarks.Dss.StairstepExponentialDecrease.contract := by rfl

end Benchmarks.Dss.StairstepExponentialDecrease.Syntax
