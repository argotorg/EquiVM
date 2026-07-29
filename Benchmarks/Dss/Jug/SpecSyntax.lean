import Benchmarks.Dss.Jug.Spec
import Solm.Notation

/-!
# Jug spec in the Solidity-faithful Solm frontend

The whole `jug.sol` spec written with `solidity%` and proven definitionally equal to the AST spec
in `Spec.lean`.  Checked-math helpers are inlined; the assembly `_rpow` loop is the structural
while-loop; `drip`'s wrapping age subtraction is the explicit ternary; `extCodeSize` guards on
the storage `vat` receiver use the `${…}` escape (the surface `x.code.length` builtin only
resolves locals).  Transition order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation Benchmarks.Dss.Jug

namespace Benchmarks.Dss.Jug.Syntax

def contractSyntax : ContractDecl := solidity% contract Jug {
  struct Ilk {
    uint256 duty;
    uint256 rho;
  }

  mapping(address => uint256) wards;
  mapping(bytes32 => Ilk) ilks;
  address vat;
  address vow;
  uint256 base;

  constructor(address vat_) {
    wards[msg.sender] = 1;
    vat = vat_;
  }

  function _add(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x + y) as uint256;
    require(z >= x);
    return z;
  }

  function _diff(uint256 x, uint256 y) internal returns (int256) {
    int256 z = (x - y) as int256;
    require(x <= #maxInt256);
    require(y <= #maxInt256);
    return z;
  }

  function _rmul(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x * y) as uint256;
    require(y == 0 || z / y == x);
    z = z / #one;
    return z;
  }

  function _rpow(uint256 x, uint256 n, uint256 b) internal returns (uint256) {
    if (x == 0) {
      if (n == 0) {
        return b;
      } else {
        return 0;
      }
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

  function base() external returns (uint256) {
    return base;
  }

  function deny(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 0;
  }

  function drip(bytes32 ilk) external returns (uint256) {
    require(block.timestamp >= ilks[ilk].rho);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var vatIlk = vat.ilks(ilk);
    uint256 prev = ${Expr.tupleGet (.var "vatIlk") 1};
    var fee = _add(base, ilks[ilk].duty);
    var pow = _rpow(fee, ilks[ilk].rho <= block.timestamp ? (block.timestamp - ilks[ilk].rho) as uint256 : (#(Int.ofNat Ethereum.UInt256.size) + block.timestamp - ilks[ilk].rho) as uint256, #one);
    var rate = _rmul(pow, prev);
    var delta = _diff(rate, prev);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _foldRet = vat.fold(ilk, vow, delta);
    ilks[ilk].rho = block.timestamp;
    return rate;
  }

  function file(bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x6261736500000000000000000000000000000000000000000000000000000000)) {
      base = data;
    } else {
      require(false);
    }
  }

  function file(bytes32 ilk, bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    require(block.timestamp == ilks[ilk].rho);
    if (what == bytes32(0x6475747900000000000000000000000000000000000000000000000000000000)) {
      ilks[ilk].duty = data;
    } else {
      require(false);
    }
  }

  function file(bytes32 what, address data) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x766f770000000000000000000000000000000000000000000000000000000000)) {
      vow = data;
    } else {
      require(false);
    }
  }

  function ilks(bytes32 arg0) external returns (uint256, uint256) {
    return (ilks[arg0].duty, ilks[arg0].rho);
  }

  function init(bytes32 ilk) external {
    require(wards[msg.sender] == 1);
    require(ilks[ilk].duty == 0);
    ilks[ilk].duty = #one;
    ilks[ilk].rho = block.timestamp;
  }

  function rely(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 1;
  }

  function vat() external returns (address) {
    return vat;
  }

  function vow() external returns (address) {
    return vow;
  }

  function wards(address arg0) external returns (uint256) {
    return wards[arg0];
  }
}

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Jug.contract := by rfl

end Benchmarks.Dss.Jug.Syntax
