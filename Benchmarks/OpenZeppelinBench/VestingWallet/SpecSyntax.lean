import Benchmarks.OpenZeppelinBench.VestingWallet.Spec
import Solm.Notation

/-!
# VestingWallet spec in the Solidity-faithful Solm frontend

The whole `VestingWalletBench` spec, written with `solidity%` and proven definitionally equal to
the AST spec in `Benchmarks/OpenZeppelinBench/VestingWallet/Spec.lean`.

Notes mirroring the AST spec:
* The constructor is `payable` (no callvalue guard) and only sets `_owner`/`_released`.
* `vestedAmount`/`releasable`/`release` inline the vesting schedule ternary with start `0` and
  duration `31536000`; the on-entry timestamp is the `uint64` wrap `block.timestamp % 2^64`
  (`#uint64Modulus`).
* ERC20 `balanceOf` reads are static calls, written `token.balanceOf{view}(address(this))`.
* `SafeERC20.safeTransfer` is the raw call plus the returndata-length / decoded-bool check.
* `end` is a Lean keyword, written `«end»`.  Transition order matches `contract.transitions`.
-/

open Solm Solm.Notation

namespace OpenZeppelinBench.VestingWallet.Syntax

def contractSyntax : ContractDecl := solidity% contract VestingWalletBench {
  address _owner;
  uint256 _released;
  mapping(address => uint256) _erc20Released;

  constructor() payable {
    _owner = msg.sender;
    _released = 0;
  }

  function duration() external returns (uint256) {
    return 31536000;
  }

  function «end»() external returns (uint256) {
    return 0 + 31536000;
  }

  function owner() external returns (address) {
    return _owner;
  }

  function releasable() external returns (uint256) {
    uint256 vested = block.timestamp % #uint64Modulus < 0 ? 0 :
      (block.timestamp % #uint64Modulus >= 0 + 31536000
        ? ((address(this).balance + _released) as uint256)
        : ((((address(this).balance + _released) as uint256)
            * (block.timestamp % #uint64Modulus - 0)) as uint256) / 31536000);
    return (vested - _released) as uint256;
  }

  function releasable(address token) external returns (uint256) {
    var tokenBalance = token.balanceOf{view}(address(this));
    uint256 vested = block.timestamp % #uint64Modulus < 0 ? 0 :
      (block.timestamp % #uint64Modulus >= 0 + 31536000
        ? ((tokenBalance + _erc20Released[token]) as uint256)
        : ((((tokenBalance + _erc20Released[token]) as uint256)
            * (block.timestamp % #uint64Modulus - 0)) as uint256) / 31536000);
    return (vested - _erc20Released[token]) as uint256;
  }

  function release() external {
    uint256 vested = block.timestamp % #uint64Modulus < 0 ? 0 :
      (block.timestamp % #uint64Modulus >= 0 + 31536000
        ? ((address(this).balance + _released) as uint256)
        : ((((address(this).balance + _released) as uint256)
            * (block.timestamp % #uint64Modulus - 0)) as uint256) / 31536000);
    uint256 amount = (vested - _released) as uint256;
    _released = (_released + amount) as uint256;
    require(address(this).balance >= amount);
    (bool success, bytes memory _data) = _owner.call{value: amount}(new bytes(0));
    require(success);
  }

  function release(address token) external {
    var tokenBalance = token.balanceOf{view}(address(this));
    uint256 vested = block.timestamp % #uint64Modulus < 0 ? 0 :
      (block.timestamp % #uint64Modulus >= 0 + 31536000
        ? ((tokenBalance + _erc20Released[token]) as uint256)
        : ((((tokenBalance + _erc20Released[token]) as uint256)
            * (block.timestamp % #uint64Modulus - 0)) as uint256) / 31536000);
    uint256 amount = (vested - _erc20Released[token]) as uint256;
    _erc20Released[token] = (_erc20Released[token] + amount) as uint256;
    bytes memory transferData = abi.encodeWithSelector(transfer, _owner, amount);
    (bool transferSuccess, bytes memory transferReturndata) = token.call(transferData);
    require(transferSuccess);
    if (transferReturndata.length == 0) {
      require(token.code.length > 0);
    } else {
      bool transferReturndata_ok = abi.decode(transferReturndata, (bool));
      require(transferReturndata_ok);
    }
  }

  function released() external returns (uint256) {
    return _released;
  }

  function released(address token) external returns (uint256) {
    return _erc20Released[token];
  }

  function renounceOwnership() external {
    require(_owner == msg.sender);
    _owner = address(0);
  }

  function start() external returns (uint256) {
    return 0;
  }

  function transferOwnership(address newOwner) external {
    require(_owner == msg.sender);
    require(newOwner != address(0));
    _owner = newOwner;
  }

  function vestedAmount(address token, uint64 timestamp) external returns (uint256) {
    var tokenBalance = token.balanceOf{view}(address(this));
    return timestamp < 0 ? 0 :
      (timestamp >= 0 + 31536000
        ? ((tokenBalance + _erc20Released[token]) as uint256)
        : ((((tokenBalance + _erc20Released[token]) as uint256)
            * (timestamp - 0)) as uint256) / 31536000);
  }

  function vestedAmount(uint64 timestamp) external returns (uint256) {
    return timestamp < 0 ? 0 :
      (timestamp >= 0 + 31536000
        ? ((address(this).balance + _released) as uint256)
        : ((((address(this).balance + _released) as uint256)
            * (timestamp - 0)) as uint256) / 31536000);
  }

  receive() external payable { }
}

theorem contractSyntax_eq : contractSyntax = OpenZeppelinBench.VestingWallet.contract := by rfl

end OpenZeppelinBench.VestingWallet.Syntax
