import Benchmarks.Dss.Cure.Spec
import Solm.Notation

/-!
# Cure spec in the Solidity-faithful Solm frontend

The whole `cure.sol` spec written with `solidity%` and proven definitionally equal to the AST
spec in `Spec.lean`.  Checked-math helpers (`_add`/`_sub`) and the checked external call in
`load` are inlined; `"wait"` is the big-endian `bytes32` literal; the unchecked `lCount++` is the
explicit `% #wordModulus` wrap.  Transition order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation Benchmarks.Dss.Cure

namespace Benchmarks.Dss.Cure.Syntax

def contractSyntax : ContractDecl := solidity% contract Cure {
  mapping(address => uint256) wards;
  uint256 live;
  address[] srcs;
  uint256 wait;
  uint256 when;
  mapping(address => uint256) pos;
  mapping(address => uint256) amt;
  mapping(address => uint256) loaded;
  uint256 lCount;
  uint256 say;

  constructor() {
    live = 1;
    wards[msg.sender] = 1;
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

  function amt(address arg0) external returns (uint256) {
    return amt[arg0];
  }

  function cage() external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    live = 0;
    var when_ = _add(block.timestamp, wait);
    when = when_;
  }

  function deny(address usr) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    wards[usr] = 0;
  }

  function drop(address src) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    uint256 pos_ = pos[src];
    require(pos_ > 0);
    uint256 last = srcs.length;
    if (pos_ < last) {
      uint256 lastIndex = (last - 1) as uint256;
      address move = srcs[lastIndex];
      uint256 dstIndex = (pos_ - 1) as uint256;
      srcs[dstIndex] = move;
      pos[move] = pos_;
    }
    srcs.pop();
    delete pos[src];
    delete amt[src];
  }

  function file(bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    if (what == bytes32(0x7761697400000000000000000000000000000000000000000000000000000000)) {
      wait = data;
    } else {
      require(false);
    }
  }

  function lCount() external returns (uint256) {
    return lCount;
  }

  function lift(address src) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    require(pos[src] == 0);
    srcs.push(src);
    pos[src] = srcs.length;
  }

  function list() external returns (address[]) {
    return srcs;
  }

  function live() external returns (uint256) {
    return live;
  }

  function load(address src) external {
    require(live == 0);
    require(pos[src] > 0);
    uint256 oldAmt_ = amt[src];
    require(src.code.length > 0);
    var newAmt_ = src.cure{view}();
    amt[src] = newAmt_;
    var withoutOld = _sub(say, oldAmt_);
    var sayNew = _add(withoutOld, newAmt_);
    say = sayNew;
    if (loaded[src] == 0) {
      loaded[src] = 1;
      lCount = (lCount + 1) % #wordModulus;
    }
  }

  function loaded(address arg0) external returns (uint256) {
    return loaded[arg0];
  }

  function pos(address arg0) external returns (uint256) {
    return pos[arg0];
  }

  function rely(address usr) external {
    require(wards[msg.sender] == 1);
    require(live == 1);
    wards[usr] = 1;
  }

  function say() external returns (uint256) {
    return say;
  }

  function srcs(uint256 arg0) external returns (address) {
    return srcs[arg0];
  }

  function tCount() external returns (uint256) {
    return srcs.length;
  }

  function tell() external returns (uint256) {
    require(live == 0 && (lCount == srcs.length || block.timestamp >= when));
    return say;
  }

  function wait() external returns (uint256) {
    return wait;
  }

  function wards(address arg0) external returns (uint256) {
    return wards[arg0];
  }

  function when() external returns (uint256) {
    return when;
  }
}

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Cure.contract := by rfl

end Benchmarks.Dss.Cure.Syntax
