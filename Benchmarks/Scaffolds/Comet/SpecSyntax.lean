import Benchmarks.Scaffolds.Comet.Spec
import Solm.Notation

/-!
# Comet spec in the Solidity-faithful Solm frontend

The whole `CometWithExtendedAssetList` benchmark spec, written with `solidity%` and proven
definitionally equal to the AST spec in `Benchmarks/CompoundIII/Comet/Spec.lean`.

Notes mirroring the AST spec:
* The 25 immutables are declared and assigned as in Solidity and read by name (`governor`, …);
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

namespace Benchmarks.CompoundIII.Comet.Syntax

def contractSyntax : ContractDecl :=
  solidity% contract CometWithExtendedAssetList {
  address immutable governor;
  address immutable pauseGuardian;
  address immutable baseToken;
  address immutable baseTokenPriceFeed;
  address immutable extensionDelegate;
  uint256 immutable supplyKink;
  uint256 immutable supplyPerSecondInterestRateSlopeLow;
  uint256 immutable supplyPerSecondInterestRateSlopeHigh;
  uint256 immutable supplyPerSecondInterestRateBase;
  uint256 immutable borrowKink;
  uint256 immutable borrowPerSecondInterestRateSlopeLow;
  uint256 immutable borrowPerSecondInterestRateSlopeHigh;
  uint256 immutable borrowPerSecondInterestRateBase;
  uint256 immutable storeFrontPriceFactor;
  uint256 immutable baseScale;
  uint256 immutable trackingIndexScale;
  uint256 immutable baseTrackingSupplySpeed;
  uint256 immutable baseTrackingBorrowSpeed;
  uint256 immutable baseMinForRewards;
  uint256 immutable baseBorrowMin;
  uint256 immutable targetReserves;
  uint8 immutable decimals;
  uint8 immutable numAssets;
  uint256 immutable accrualDescaleFactor;
  address immutable assetList;
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
      governor = config.0;
      pauseGuardian = config.1;
      baseToken = config.2;
      baseTokenPriceFeed = config.3;
      extensionDelegate = config.4;
      storeFrontPriceFactor = config.13;
      trackingIndexScale = config.14;
      baseMinForRewards = config.17;
      baseTrackingSupplySpeed = config.15;
      baseTrackingBorrowSpeed = config.16;
      baseBorrowMin = config.18;
      targetReserves = config.19;
      supplyKink = config.5;
      borrowKink = config.9;
      supplyPerSecondInterestRateSlopeLow = config.6 / 31536000;
      supplyPerSecondInterestRateSlopeHigh = config.7 / 31536000;
      supplyPerSecondInterestRateBase = config.8 / 31536000;
      borrowPerSecondInterestRateSlopeLow = config.10 / 31536000;
      borrowPerSecondInterestRateSlopeHigh = config.11 / 31536000;
      borrowPerSecondInterestRateBase = config.12 / 31536000;
      ${[Stmt.externalCall (.immutable "baseToken") "decimals" (.intLit 0) [] "decimals_"
          (perm := false)]}
      decimals = ${.var "decimals_"};
      baseScale = 10 ** decimals;
      accrualDescaleFactor = baseScale / #(10 ^ 15);
      numAssets = 0;
      ${[Stmt.externalCall (.immutable "extensionDelegate") "createAssetList" (.intLit 0) []
          "assetList_"]}
      assetList = ${.var "assetList_"};
    }

    fallback(bytes calldata) external payable returns (bytes) {
      ${[Stmt.delegateCall (.immutable "extensionDelegate") (.var "calldata") "ok" "returndata"]}
      require(${Expr.var "ok"});
      return ${Expr.var "returndata"};
    }

    function absorb(address absorber, address[] accounts) external { }

    function accrueAccount(address account) external { }

    function approveThis(address manager, address asset, uint256 amount) external { }

    function assetList() external returns (address) {
      return assetList;
    }

    function balanceOf(address account) external returns (uint256) {
      int104 principal = userBasic[account].principal;
      return principal > 0 ?
        (((principal * baseSupplyIndex) as uint256) / #baseIndexScale) as uint256 : 0;
    }

    function baseBorrowMin() external returns (uint256) {
      return baseBorrowMin;
    }

    function baseMinForRewards() external returns (uint256) {
      return baseMinForRewards;
    }

    function baseScale() external returns (uint256) {
      return baseScale;
    }

    function baseToken() external returns (address) {
      return baseToken;
    }

    function baseTokenPriceFeed() external returns (address) {
      return baseTokenPriceFeed;
    }

    function baseTrackingBorrowSpeed() external returns (uint256) {
      return baseTrackingBorrowSpeed;
    }

    function baseTrackingSupplySpeed() external returns (uint256) {
      return baseTrackingSupplySpeed;
    }

    function borrowBalanceOf(address account) external returns (uint256) {
      int104 principal = userBasic[account].principal;
      return principal < 0 ?
        (((((-principal) as uint104) * baseBorrowIndex) as uint256) / #baseIndexScale) as uint256 :
        0;
    }

    function borrowKink() external returns (uint256) {
      return borrowKink;
    }

    function borrowPerSecondInterestRateBase() external returns (uint256) {
      return borrowPerSecondInterestRateBase;
    }

    function borrowPerSecondInterestRateSlopeHigh() external returns (uint256) {
      return borrowPerSecondInterestRateSlopeHigh;
    }

    function borrowPerSecondInterestRateSlopeLow() external returns (uint256) {
      return borrowPerSecondInterestRateSlopeLow;
    }

    function buyCollateral(address asset, uint256 minAmount, uint256 baseAmount,
        address recipient) external { }

    function decimals() external returns (uint8) {
      return decimals;
    }

    function extensionDelegate() external returns (address) {
      return extensionDelegate;
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
      return (utilization <= borrowKink ?
          (borrowPerSecondInterestRateBase +
            (((borrowPerSecondInterestRateSlopeLow * utilization) as uint256) /
              #factorScale)) as uint256 :
          (((borrowPerSecondInterestRateBase +
              (((borrowPerSecondInterestRateSlopeLow *
                borrowKink) as uint256) / #factorScale)) as uint256) +
            (((borrowPerSecondInterestRateSlopeHigh *
              ((utilization - borrowKink) as uint256)) as uint256) /
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
      return (utilization <= supplyKink ?
          (supplyPerSecondInterestRateBase +
            (((supplyPerSecondInterestRateSlopeLow * utilization) as uint256) /
              #factorScale)) as uint256 :
          (((supplyPerSecondInterestRateBase +
              (((supplyPerSecondInterestRateSlopeLow *
                supplyKink) as uint256) / #factorScale)) as uint256) +
            (((supplyPerSecondInterestRateSlopeHigh *
              ((utilization - supplyKink) as uint256)) as uint256) /
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
      return governor;
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
      return (pauseFlags &[uint8] (1 <<[uint8] 3)) != 0;
    }

    function isAllowed(address arg0, address arg1) external returns (bool) {
      return isAllowed[arg0][arg1];
    }

    function isBorrowCollateralized(address account) external returns (bool) {
      return false;
    }

    function isBuyPaused() external returns (bool) {
      return (pauseFlags &[uint8] (1 <<[uint8] 4)) != 0;
    }

    function isLiquidatable(address account) external returns (bool) {
      return false;
    }

    function isSupplyPaused() external returns (bool) {
      return (pauseFlags &[uint8] (1 <<[uint8] 0)) != 0;
    }

    function isTransferPaused() external returns (bool) {
      return (pauseFlags &[uint8] (1 <<[uint8] 1)) != 0;
    }

    function isWithdrawPaused() external returns (bool) {
      return (pauseFlags &[uint8] (1 <<[uint8] 2)) != 0;
    }

    function liquidatorPoints(address arg0) external returns (uint32, uint64, uint128, uint32) {
      return (liquidatorPoints[arg0].numAbsorbs, liquidatorPoints[arg0].numAbsorbed,
        liquidatorPoints[arg0].approxSpend, liquidatorPoints[arg0]._reserved);
    }

    function numAssets() external returns (uint8) {
      return numAssets;
    }

    function pause(bool supplyPaused, bool transferPaused, bool withdrawPaused,
        bool absorbPaused, bool buyPaused) external {
      require(msg.sender == governor ||
        msg.sender == pauseGuardian);
      pauseFlags = (((supplyPaused ? 1 : 0) <<[uint8] 0) |[uint8]
        (((transferPaused ? 1 : 0) <<[uint8] 1) |[uint8]
          (((withdrawPaused ? 1 : 0) <<[uint8] 2) |[uint8]
            (((absorbPaused ? 1 : 0) <<[uint8] 3) |[uint8]
              ((buyPaused ? 1 : 0) <<[uint8] 4))))) as uint8;
    }

    function pauseGuardian() external returns (address) {
      return pauseGuardian;
    }

    function quoteCollateral(address asset, uint256 baseAmount) external returns (uint256) {
      return 0;
    }

    function storeFrontPriceFactor() external returns (uint256) {
      return storeFrontPriceFactor;
    }

    function supply(address asset, uint256 amount) external { }

    function supplyFrom(address «from», address dst, address asset, uint256 amount) external { }

    function supplyKink() external returns (uint256) {
      return supplyKink;
    }

    function supplyPerSecondInterestRateBase() external returns (uint256) {
      return supplyPerSecondInterestRateBase;
    }

    function supplyPerSecondInterestRateSlopeHigh() external returns (uint256) {
      return supplyPerSecondInterestRateSlopeHigh;
    }

    function supplyPerSecondInterestRateSlopeLow() external returns (uint256) {
      return supplyPerSecondInterestRateSlopeLow;
    }

    function supplyTo(address dst, address asset, uint256 amount) external { }

    function targetReserves() external returns (uint256) {
      return targetReserves;
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
      return trackingIndexScale;
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

theorem contractSyntax_eq :
    contractSyntax = Benchmarks.CompoundIII.Comet.contract := by rfl

end Benchmarks.CompoundIII.Comet.Syntax
