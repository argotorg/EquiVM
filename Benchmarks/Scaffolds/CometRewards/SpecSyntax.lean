import Benchmarks.Scaffolds.CometRewards.Spec
import Solm.Notation

/-!
# CometRewards spec in the Solidity-faithful Solm frontend

The whole CometRewards benchmark spec, written with `solidity%` and proven definitionally equal
to the AST spec in `Benchmarks/CompoundIII/CometRewards/Spec.lean`.

Notes mirroring the AST spec:
* Every external entry point opens with the spec's calldata-size guard
  (`bytes __calldata = msg.data; require(__calldata.length < …)`), after the auto-inserted
  callvalue guard.
* Int constants (`maxUint64`, `factorScale`, `calldataSizeLimit`) splice via `#`.
* View externals (`baseTrackingAccrued`, `baseAccrualScale`, `decimals`, `hasPermission`)
  are marked `{view}` (perm := false); `accrueAccount`/`transfer` are permanent.
* `getRewardOwed` returns the `RewardOwed` struct as the surface ABI tuple type
  `((address, uint256))`; the tuple result is built with `tuple(token, owed)`.
* Transition and internal-function order match `contract.transitions`/`contract.functions`.
-/

open Solm Solm.Notation

namespace Benchmarks.CompoundIII.CometRewards.Syntax

def contractSyntax : ContractDecl := solidity% contract CometRewards {
  struct RewardConfig {
    address token;
    uint64 rescaleFactor;
    bool shouldUpscale;
    uint256 multiplier;
  }

  address governor;
  mapping(address => RewardConfig) rewardConfig;
  mapping(address => mapping(address => uint256)) rewardsClaimed;

  constructor(address governor_) {
    governor = governor_;
  }

  function safe64(uint256 n) internal returns (uint64) {
    require(n <= #maxUint64);
    return n as uint64;
  }

  function pow10(uint8 n) internal returns (uint256) {
    require(n <= 77);
    return (10 ** n) as uint256;
  }

  function getRewardAccrued(address comet, address account, uint64 rescaleFactor,
      bool shouldUpscale, uint256 multiplier) internal returns (uint256) {
    var accrued = comet.baseTrackingAccrued{view}(account);
    if (shouldUpscale) {
      accrued = (accrued * rescaleFactor) as uint256;
    } else {
      accrued = accrued / rescaleFactor;
    }
    uint256 scaled = (accrued * multiplier) as uint256;
    return scaled / #factorScale;
  }

  function doTransferOut(address token, address «to», uint256 amount) internal {
    var success = token.transfer(«to», amount);
    require(success);
  }

  function setRewardConfigWithMultiplierBody(address comet, address token,
      uint256 multiplier) internal {
    require(msg.sender == governor);
    require(rewardConfig[comet].token == address(0));
    var accrualScale = comet.baseAccrualScale{view}();
    var tokenDecimals = token.decimals{view}();
    var tokenScale256 = pow10(tokenDecimals);
    var tokenScale = safe64(tokenScale256);
    if (accrualScale > tokenScale) {
      rewardConfig[comet].token = token;
      rewardConfig[comet].rescaleFactor = accrualScale / tokenScale;
      rewardConfig[comet].shouldUpscale = false;
      rewardConfig[comet].multiplier = multiplier;
    } else {
      rewardConfig[comet].token = token;
      rewardConfig[comet].rescaleFactor = tokenScale / accrualScale;
      rewardConfig[comet].shouldUpscale = true;
      rewardConfig[comet].multiplier = multiplier;
    }
  }

  function claimInternal(address comet, address src, address «to», bool shouldAccrue) internal {
    address token = rewardConfig[comet].token;
    uint64 rescaleFactor = rewardConfig[comet].rescaleFactor;
    bool shouldUpscale = rewardConfig[comet].shouldUpscale;
    uint256 multiplier = rewardConfig[comet].multiplier;
    require(token != address(0));
    if (shouldAccrue) {
      require(comet.code.length > 0);
      var _accrued = comet.accrueAccount(src);
    }
    uint256 claimed = rewardsClaimed[comet][src];
    var accrued = getRewardAccrued(comet, src, rescaleFactor, shouldUpscale, multiplier);
    if (accrued > claimed) {
      uint256 owed = accrued - claimed;
      rewardsClaimed[comet][src] = accrued;
      var _sent = doTransferOut(token, «to», owed);
    }
  }

  function claim(address comet, address src, bool shouldAccrue) external {
    bytes __calldata = msg.data;
    require(__calldata.length < #calldataSizeLimit);
    var _claim = claimInternal(comet, src, src, shouldAccrue);
  }

  function claimTo(address comet, address src, address «to», bool shouldAccrue) external {
    bytes __calldata = msg.data;
    require(__calldata.length < #calldataSizeLimit);
    var permitted = comet.hasPermission{view}(src, msg.sender);
    require(permitted);
    var _claim = claimInternal(comet, src, «to», shouldAccrue);
  }

  function getRewardOwed(address comet, address account) external
      returns ((address, uint256)) {
    bytes __calldata = msg.data;
    require(__calldata.length < #calldataSizeLimit);
    address token = rewardConfig[comet].token;
    uint64 rescaleFactor = rewardConfig[comet].rescaleFactor;
    bool shouldUpscale = rewardConfig[comet].shouldUpscale;
    uint256 multiplier = rewardConfig[comet].multiplier;
    require(token != address(0));
    require(comet.code.length > 0);
    var _accrued = comet.accrueAccount(account);
    uint256 claimed = rewardsClaimed[comet][account];
    var accrued = getRewardAccrued(comet, account, rescaleFactor, shouldUpscale, multiplier);
    uint256 owed = accrued > claimed ? accrued - claimed : 0;
    return tuple(token, owed);
  }

  function governor() external returns (address) {
    bytes __calldata = msg.data;
    require(__calldata.length < #calldataSizeLimit);
    return governor;
  }

  function rewardConfig(address arg0) external returns (address, uint64, bool, uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < #calldataSizeLimit);
    return (rewardConfig[arg0].token, rewardConfig[arg0].rescaleFactor,
      rewardConfig[arg0].shouldUpscale, rewardConfig[arg0].multiplier);
  }

  function rewardsClaimed(address arg0, address arg1) external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < #calldataSizeLimit);
    return rewardsClaimed[arg0][arg1];
  }

  function setRewardConfig(address comet, address token) external {
    bytes __calldata = msg.data;
    require(__calldata.length < #calldataSizeLimit);
    var _set = setRewardConfigWithMultiplierBody(comet, token, #factorScale);
  }

  function setRewardConfigWithMultiplier(address comet, address token, uint256 multiplier) external {
    bytes __calldata = msg.data;
    require(__calldata.length < #calldataSizeLimit);
    var _set = setRewardConfigWithMultiplierBody(comet, token, multiplier);
  }

  function setRewardsClaimed(address comet, address[] calldata users,
      uint256[] calldata claimedAmounts) external {
    bytes __calldata = msg.data;
    require(__calldata.length < #calldataSizeLimit);
    require(msg.sender == governor);
    require(users.length == claimedAmounts.length);
    uint256 i = 0;
    while (i < users.length) {
      rewardsClaimed[comet][users[i]] = claimedAmounts[i];
      i = i + 1;
    }
  }

  function transferGovernor(address newGovernor) external {
    bytes __calldata = msg.data;
    require(__calldata.length < #calldataSizeLimit);
    require(msg.sender == governor);
    governor = newGovernor;
  }

  function withdrawToken(address token, address «to», uint256 amount) external {
    bytes __calldata = msg.data;
    require(__calldata.length < #calldataSizeLimit);
    require(msg.sender == governor);
    var _sent = doTransferOut(token, «to», amount);
  }
}

theorem contractSyntax_eq :
    contractSyntax = Benchmarks.CompoundIII.CometRewards.contract := by rfl

end Benchmarks.CompoundIII.CometRewards.Syntax
