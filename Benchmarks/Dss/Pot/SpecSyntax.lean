import Benchmarks.Dss.Pot.Spec
import Solm.Notation

/-!
# Pot spec in the Solidity-faithful Solm frontend

The whole `pot.sol` spec written with `solidity%` and proven definitionally equal to the AST spec
in `Spec.lean`.  Checked-math helpers are inlined (`_rmul` keeps its `_mul` internal call, as in
the AST); the assembly `_rpow` loop is the structural while-loop; `extCodeSize` guards on the
storage `vat` receiver use the `${…}` escape.  Transition order matches `contract.transitions`
(selector order).
-/

open Solm Solm.Notation Benchmarks.Dss.Pot

namespace Benchmarks.Dss.Pot.Syntax

def contractSyntax : ContractDecl := solidity% contract Pot {
  mapping(address => uint256) wards;
  mapping(address => uint256) pie;
  uint256 Pie;
  uint256 dsr;
  uint256 chi;
  address vat;
  address vow;
  uint256 rho;
  uint256 live;

  constructor(address vat_) {
    wards[msg.sender] = 1;
    vat = vat_;
    dsr = #one;
    chi = #one;
    rho = block.timestamp;
    live = 1;
  }

  function _add(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x + y) as uint256;
    require(z >= x);
    return z;
  }

  function _sub(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x - y) as uint256;
    require(z <= x);
    return z;
  }

  function _mul(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x * y) as uint256;
    require(y == 0 || z / y == x);
    return z;
  }

  function _rmul(uint256 x, uint256 y) internal returns (uint256) {
    var z = _mul(x, y);
    z = z / #one;
    return z;
  }

  function _rpow(uint256 x, uint256 n, uint256 base) internal returns (uint256) {
    if (x == 0) {
      if (n == 0) {
        return base;
      } else {
        return 0;
      }
    } else {
      uint256 z = n % 2 == 0 ? base : x;
      uint256 half = base / 2;
      n = n / 2;
      while (n != 0) {
        uint256 xx = (x * x) as uint256;
        require(x == 0 || xx / x == x);
        uint256 xxRound = (xx + half) as uint256;
        require(xxRound >= xx);
        x = xxRound / base;
        if (n % 2 != 0) {
          uint256 zx = (z * x) as uint256;
          require(x == 0 || zx / x == z);
          uint256 zxRound = (zx + half) as uint256;
          require(zxRound >= zx);
          z = zxRound / base;
        }
        n = n / 2;
      }
      return z;
    }
  }

  function Pie() external returns (uint256) {
    return Pie;
  }

  function cage() external {
    require(wards[msg.sender] == 1);
    live = 0;
    dsr = #one;
  }

  function chi() external returns (uint256) {
    return chi;
  }

  function deny(address guy) external {
    require(wards[msg.sender] == 1);
    wards[guy] = 0;
  }

  function drip() external returns (uint256) {
    require(block.timestamp >= rho);
    var pow = _rpow(dsr, (block.timestamp - rho) as uint256, #one);
    var tmp = _rmul(pow, chi);
    var chi_ = _sub(tmp, chi);
    chi = tmp;
    rho = block.timestamp;
    var rad = _mul(Pie, chi_);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _suckRet = vat.suck(vow, address(this), rad);
    return tmp;
  }

  function dsr() external returns (uint256) {
    return dsr;
  }

  function exit(uint256 wad) external {
    uint256 pieNew = (pie[msg.sender] - wad) as uint256;
    require(pieNew <= pie[msg.sender]);
    pie[msg.sender] = pieNew;
    uint256 PieNew = (Pie - wad) as uint256;
    require(PieNew <= Pie);
    Pie = PieNew;
    var rad = _mul(chi, wad);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _moveRet = vat.move(address(this), msg.sender, rad);
  }

  function file(bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    require(block.timestamp == rho);
    if (what == bytes32(0x6473720000000000000000000000000000000000000000000000000000000000)) {
      dsr = data;
    } else {
      require(false);
    }
  }

  function file(bytes32 what, address addr) external {
    require(wards[msg.sender] == 1);
    if (what == bytes32(0x766f770000000000000000000000000000000000000000000000000000000000)) {
      vow = addr;
    } else {
      require(false);
    }
  }

  function join(uint256 wad) external {
    require(block.timestamp == rho);
    uint256 pieNew = (pie[msg.sender] + wad) as uint256;
    require(pieNew >= pie[msg.sender]);
    pie[msg.sender] = pieNew;
    uint256 PieNew = (Pie + wad) as uint256;
    require(PieNew >= Pie);
    Pie = PieNew;
    var rad = _mul(chi, wad);
    require(${Expr.extCodeSize (.storage vatRef)} > 0);
    var _moveRet = vat.move(msg.sender, address(this), rad);
  }

  function live() external returns (uint256) {
    return live;
  }

  function pie(address arg0) external returns (uint256) {
    return pie[arg0];
  }

  function rely(address guy) external {
    require(wards[msg.sender] == 1);
    wards[guy] = 1;
  }

  function rho() external returns (uint256) {
    return rho;
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

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Pot.contract := by rfl

end Benchmarks.Dss.Pot.Syntax
