import Benchmarks.Scaffolds.Comet.Spec
import Solm.Notation

/-!
# Comet spec in the Solidity-faithful Solm frontend

The whole `CometWithExtendedAssetList` benchmark spec, written with `solidity%` and proven
definitionally equal to the AST spec in `Benchmarks/CompoundIII/Comet/Spec.lean`.

Notes mirroring the AST spec:
* The 25 immutable reads splice the spec's `Immutables` exprs (`${Immutables.governor v}`, …);
  Int constants (`maxUint40`, `baseIndexScale`, `factorScale`, `10 ^ 15`) splice via `#`.
* Principal/present-value math and the interest-rate kink formulas are written out in surface
  form (`(…) as uint256` for the spec's `u256`/`u104`/`u64`/`u40`/`u8` range wraps).
* `getAssetInfo`/`getAssetInfoByAddress` return the `AssetInfo` struct as the surface ABI
  tuple type `((uint8, address, address, uint64, uint64, uint64, uint64, uint128))`; the
  results are built with `tuple(…)`.
* The constructor's `config` param is the surface ABI tuple type (with a nested tuple-array
  postfix `(…)[]`), mirroring the spec's `ConstructorDecl` param exactly.
* The fallback delegatecalls the extension delegate (an `Expr`-valued immutable receiver, so the
  statement is spliced); it carries no callvalue guard in the spec, hence `payable`, and it
  declares its `bytes` return type with the surface `returns (bytes)` clause.
* Lean-keyword param names are guillemet-escaped («from», «to»).
* Transition order matches `contract.transitions` (selector order); no internal functions.
-/

open Solm Solm.Notation
open Benchmarks.CompoundIII.Comet.Immutables (CometImmutables)

namespace Benchmarks.CompoundIII.Comet.Syntax

def contractSyntax (v : CometImmutables) : ContractDecl :=
  solidity% contract CometWithExtendedAssetList {
    struct LiquidatorPoints {
      uint32 numAbsorbs;
      uint64 numAbsorbed;
      uint128 approxSpend;
      uint32 _reserved;
    }

    struct TotalsCollateral {
      uint128 totalSupplyAsset;
      uint128 _reserved;
    }

    struct UserBasic {
      int104 principal;
      uint64 baseTrackingIndex;
      uint64 baseTrackingAccrued;
      uint16 assetsIn;
      uint8 _reserved;
    }

    struct UserCollateral {
      uint128 balance;
      uint128 _reserved;
    }

    uint64 baseSupplyIndex;
    uint64 baseBorrowIndex;
    uint64 trackingSupplyIndex;
    uint64 trackingBorrowIndex;
    uint104 totalSupplyBase;
    uint104 totalBorrowBase;
    uint40 lastAccrualTime;
    uint8 pauseFlags;
    mapping(address => TotalsCollateral) totalsCollateral;
    mapping(address => mapping(address => bool)) isAllowed;
    mapping(address => uint256) userNonce;
    mapping(address => UserBasic) userBasic;
    mapping(address => mapping(address => UserCollateral)) userCollateral;
    mapping(address => LiquidatorPoints) liquidatorPoints;

    constructor((address, address, address, address, address,
        uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64,
        uint64, uint104, uint104, uint104,
        (address, address, uint8, uint64, uint64, uint64, uint128)[]) config) {
      var imm_governor = config.0;
      var imm_pauseGuardian = config.1;
      var imm_baseToken = config.2;
      var imm_baseTokenPriceFeed = config.3;
      var imm_extensionDelegate = config.4;
      var imm_storeFrontPriceFactor = config.13;
      var imm_trackingIndexScale = config.14;
      var imm_baseMinForRewards = config.17;
      var imm_baseTrackingSupplySpeed = config.15;
      var imm_baseTrackingBorrowSpeed = config.16;
      var imm_baseBorrowMin = config.18;
      var imm_targetReserves = config.19;
      var imm_supplyKink = config.5;
      var imm_borrowKink = config.9;
      var imm_supplyPerSecondInterestRateSlopeLow = config.6 / 31536000;
      var imm_supplyPerSecondInterestRateSlopeHigh = config.7 / 31536000;
      var imm_supplyPerSecondInterestRateBase = config.8 / 31536000;
      var imm_borrowPerSecondInterestRateSlopeLow = config.10 / 31536000;
      var imm_borrowPerSecondInterestRateSlopeHigh = config.11 / 31536000;
      var imm_borrowPerSecondInterestRateBase = config.12 / 31536000;
      var imm_decimals = imm_baseToken.decimals{view}();
      var imm_baseScale = 10 ** imm_decimals;
      var imm_accrualDescaleFactor = imm_baseScale / #(10 ^ 15);
      var imm_numAssets = 0;
      var imm_assetList = imm_extensionDelegate.createAssetList();
    }

    fallback(bytes calldata) external payable returns (bytes) {
      ${[Stmt.delegateCall (Immutables.extensionDelegate v) (.var "calldata") "ok" "returndata"]}
      require(${Expr.var "ok"});
      return ${Expr.var "returndata"};
    }

    function absorb(address absorber, address[] accounts) external { }

    function accrueAccount(address account) external { }

    function approveThis(address manager, address asset, uint256 amount) external { }

    function assetList() external returns (address) {
      return ${Immutables.assetList v};
    }

    function balanceOf(address account) external returns (uint256) {
      int104 principal = userBasic[account].principal;
      return principal > 0 ?
        (((principal * baseSupplyIndex) as uint256) / #baseIndexScale) as uint256 : 0;
    }

    function baseBorrowMin() external returns (uint256) {
      return ${Immutables.baseBorrowMin v};
    }

    function baseMinForRewards() external returns (uint256) {
      return ${Immutables.baseMinForRewards v};
    }

    function baseScale() external returns (uint256) {
      return ${Immutables.baseScale v};
    }

    function baseToken() external returns (address) {
      return ${Immutables.baseToken v};
    }

    function baseTokenPriceFeed() external returns (address) {
      return ${Immutables.baseTokenPriceFeed v};
    }

    function baseTrackingBorrowSpeed() external returns (uint256) {
      return ${Immutables.baseTrackingBorrowSpeed v};
    }

    function baseTrackingSupplySpeed() external returns (uint256) {
      return ${Immutables.baseTrackingSupplySpeed v};
    }

    function borrowBalanceOf(address account) external returns (uint256) {
      int104 principal = userBasic[account].principal;
      return principal < 0 ?
        (((((-principal) as uint104) * baseBorrowIndex) as uint256) / #baseIndexScale) as uint256 :
        0;
    }

    function borrowKink() external returns (uint256) {
      return ${Immutables.borrowKink v};
    }

    function borrowPerSecondInterestRateBase() external returns (uint256) {
      return ${Immutables.borrowPerSecondInterestRateBase v};
    }

    function borrowPerSecondInterestRateSlopeHigh() external returns (uint256) {
      return ${Immutables.borrowPerSecondInterestRateSlopeHigh v};
    }

    function borrowPerSecondInterestRateSlopeLow() external returns (uint256) {
      return ${Immutables.borrowPerSecondInterestRateSlopeLow v};
    }

    function buyCollateral(address asset, uint256 minAmount, uint256 baseAmount,
        address recipient) external { }

    function decimals() external returns (uint8) {
      return ${Immutables.decimals v};
    }

    function extensionDelegate() external returns (address) {
      return ${Immutables.extensionDelegate v};
    }

    function getAssetInfo(uint8 i) external
        returns ((uint8, address, address, uint64, uint64, uint64, uint64, uint128)) {
      return tuple(0, address(0), address(0), 0, 0, 0, 0, 0);
    }

    function getAssetInfoByAddress(address asset) external
        returns ((uint8, address, address, uint64, uint64, uint64, uint64, uint128)) {
      return tuple(0, address(0), address(0), 0, 0, 0, 0, 0);
    }

    function getBorrowRate(uint256 utilization) external returns (uint64) {
      return (utilization <= ${Immutables.borrowKink v} ?
          (${Immutables.borrowPerSecondInterestRateBase v} +
            (((${Immutables.borrowPerSecondInterestRateSlopeLow v} * utilization) as uint256) /
              #factorScale)) as uint256 :
          (((${Immutables.borrowPerSecondInterestRateBase v} +
              (((${Immutables.borrowPerSecondInterestRateSlopeLow v} *
                ${Immutables.borrowKink v}) as uint256) / #factorScale)) as uint256) +
            (((${Immutables.borrowPerSecondInterestRateSlopeHigh v} *
              ((utilization - ${Immutables.borrowKink v}) as uint256)) as uint256) /
              #factorScale)) as uint256) as uint64;
    }

    function getCollateralReserves(address asset) external returns (uint256) {
      return 0;
    }

    function getPrice(address priceFeed) external returns (uint256) {
      return 0;
    }

    function getReserves() external returns (int256) {
      return 0;
    }

    function getSupplyRate(uint256 utilization) external returns (uint64) {
      return (utilization <= ${Immutables.supplyKink v} ?
          (${Immutables.supplyPerSecondInterestRateBase v} +
            (((${Immutables.supplyPerSecondInterestRateSlopeLow v} * utilization) as uint256) /
              #factorScale)) as uint256 :
          (((${Immutables.supplyPerSecondInterestRateBase v} +
              (((${Immutables.supplyPerSecondInterestRateSlopeLow v} *
                ${Immutables.supplyKink v}) as uint256) / #factorScale)) as uint256) +
            (((${Immutables.supplyPerSecondInterestRateSlopeHigh v} *
              ((utilization - ${Immutables.supplyKink v}) as uint256)) as uint256) /
              #factorScale)) as uint256) as uint64;
    }

    function getUtilization() external returns (uint256) {
      uint256 totalSupply_ =
        (((totalSupplyBase * baseSupplyIndex) as uint256) / #baseIndexScale) as uint256;
      uint256 totalBorrow_ =
        (((totalBorrowBase * baseBorrowIndex) as uint256) / #baseIndexScale) as uint256;
      return totalSupply_ == 0 ? 0 :
        ((totalBorrow_ * #factorScale) as uint256) / totalSupply_;
    }

    function governor() external returns (address) {
      return ${Immutables.governor v};
    }

    function hasPermission(address owner, address manager) external returns (bool) {
      return owner == manager || isAllowed[owner][manager];
    }

    function initializeStorage() external {
      require(lastAccrualTime == 0);
      require(block.timestamp <= #maxUint40);
      lastAccrualTime = (block.timestamp) as uint40;
      baseSupplyIndex = #baseIndexScale;
      baseBorrowIndex = #baseIndexScale;
    }

    function isAbsorbPaused() external returns (bool) {
      return (pauseFlags & (1 << 3)) != 0;
    }

    function isAllowed(address arg0, address arg1) external returns (bool) {
      return isAllowed[arg0][arg1];
    }

    function isBorrowCollateralized(address account) external returns (bool) {
      return false;
    }

    function isBuyPaused() external returns (bool) {
      return (pauseFlags & (1 << 4)) != 0;
    }

    function isLiquidatable(address account) external returns (bool) {
      return false;
    }

    function isSupplyPaused() external returns (bool) {
      return (pauseFlags & (1 << 0)) != 0;
    }

    function isTransferPaused() external returns (bool) {
      return (pauseFlags & (1 << 1)) != 0;
    }

    function isWithdrawPaused() external returns (bool) {
      return (pauseFlags & (1 << 2)) != 0;
    }

    function liquidatorPoints(address arg0) external returns (uint32, uint64, uint128, uint32) {
      return (liquidatorPoints[arg0].numAbsorbs, liquidatorPoints[arg0].numAbsorbed,
        liquidatorPoints[arg0].approxSpend, liquidatorPoints[arg0]._reserved);
    }

    function numAssets() external returns (uint8) {
      return ${Immutables.numAssets v};
    }

    function pause(bool supplyPaused, bool transferPaused, bool withdrawPaused,
        bool absorbPaused, bool buyPaused) external {
      require(msg.sender == ${Immutables.governor v} ||
        msg.sender == ${Immutables.pauseGuardian v});
      pauseFlags = (((supplyPaused ? 1 : 0) << 0) |
        (((transferPaused ? 1 : 0) << 1) |
          (((withdrawPaused ? 1 : 0) << 2) |
            (((absorbPaused ? 1 : 0) << 3) |
              ((buyPaused ? 1 : 0) << 4))))) as uint8;
    }

    function pauseGuardian() external returns (address) {
      return ${Immutables.pauseGuardian v};
    }

    function quoteCollateral(address asset, uint256 baseAmount) external returns (uint256) {
      return 0;
    }

    function storeFrontPriceFactor() external returns (uint256) {
      return ${Immutables.storeFrontPriceFactor v};
    }

    function supply(address asset, uint256 amount) external { }

    function supplyFrom(address «from», address dst, address asset, uint256 amount) external { }

    function supplyKink() external returns (uint256) {
      return ${Immutables.supplyKink v};
    }

    function supplyPerSecondInterestRateBase() external returns (uint256) {
      return ${Immutables.supplyPerSecondInterestRateBase v};
    }

    function supplyPerSecondInterestRateSlopeHigh() external returns (uint256) {
      return ${Immutables.supplyPerSecondInterestRateSlopeHigh v};
    }

    function supplyPerSecondInterestRateSlopeLow() external returns (uint256) {
      return ${Immutables.supplyPerSecondInterestRateSlopeLow v};
    }

    function supplyTo(address dst, address asset, uint256 amount) external { }

    function targetReserves() external returns (uint256) {
      return ${Immutables.targetReserves v};
    }

    function totalBorrow() external returns (uint256) {
      return (((totalBorrowBase * baseBorrowIndex) as uint256) / #baseIndexScale) as uint256;
    }

    function totalSupply() external returns (uint256) {
      return (((totalSupplyBase * baseSupplyIndex) as uint256) / #baseIndexScale) as uint256;
    }

    function totalsCollateral(address arg0) external returns (uint128, uint128) {
      return (totalsCollateral[arg0].totalSupplyAsset, totalsCollateral[arg0]._reserved);
    }

    function trackingIndexScale() external returns (uint256) {
      return ${Immutables.trackingIndexScale v};
    }

    function transfer(address dst, uint256 amount) external returns (bool) {
      return false;
    }

    function transferAsset(address dst, address asset, uint256 amount) external { }

    function transferAssetFrom(address src, address dst, address asset,
        uint256 amount) external { }

    function transferFrom(address src, address dst, uint256 amount) external returns (bool) {
      return false;
    }

    function userBasic(address arg0) external returns (int104, uint64, uint64, uint16, uint8) {
      return (userBasic[arg0].principal, userBasic[arg0].baseTrackingIndex,
        userBasic[arg0].baseTrackingAccrued, userBasic[arg0].assetsIn, userBasic[arg0]._reserved);
    }

    function userCollateral(address arg0, address arg1) external returns (uint128, uint128) {
      return (userCollateral[arg0][arg1].balance, userCollateral[arg0][arg1]._reserved);
    }

    function userNonce(address arg0) external returns (uint256) {
      return userNonce[arg0];
    }

    function withdraw(address asset, uint256 amount) external { }

    function withdrawFrom(address src, address «to», address asset, uint256 amount) external { }

    function withdrawReserves(address «to», uint256 amount) external { }

    function withdrawTo(address «to», address asset, uint256 amount) external { }
  }

theorem contractSyntax_eq (v : CometImmutables) :
    contractSyntax v = Benchmarks.CompoundIII.Comet.contract v := by rfl

end Benchmarks.CompoundIII.Comet.Syntax
