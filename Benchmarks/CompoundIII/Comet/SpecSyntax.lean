import Solm.Notation

/-!
# CometWithExtendedAssetList specification

Drafted by `scripts/sol2solm.py`; assembly effects and ABI adapters are explicit below.

Source contract `CometWithExtendedAssetList`, solc 0.8.15, via-IR; linearisation: CometWithExtendedAssetList → CometMainInterface → CometCore → CometMath → CometStorage → CometConfiguration.
Transitions are in selector order (the dispatcher order).

Translator notes (reviewed as the specification is completed):
  - constant BASE_INDEX_SCALE = 1000000000000000 inlined
  - `basic` copies a struct from storage in one read; check the bytecode's field read order — src 11474:43:5
  - constant FACTOR_SCALE = 1000000000000000000 inlined
  - constant PAUSE_SUPPLY_OFFSET = 0 inlined
  - constant PAUSE_TRANSFER_OFFSET = 1 inlined
  - constant PAUSE_WITHDRAW_OFFSET = 2 inlined
  - constant PAUSE_ABSORB_OFFSET = 3 inlined
  - constant PAUSE_BUY_OFFSET = 4 inlined
  - `points` copies a struct from storage in one read; check the bytecode's field read order — src 41802:59:5
  - constant MAX_BASE_DECIMALS = 18 inlined
  - constant MAX_ASSETS_FOR_ASSET_LIST = 24 inlined
  - constant PRICE_FEED_DECIMALS = 8 inlined
  - constant BASE_ACCRUAL_SCALE = 1000000 inlined
  - constant SECONDS_PER_YEAR = 31536000 inlined
  - `accountUser` copies a struct from storage in one read; check the bytecode's field read order — src 42298:49:5
  - constant REENTRANCY_GUARD_FLAG_SLOT = bytes32(keccak256("comet.reentrancy.guard")) inlined
  - constant REENTRANCY_GUARD_ENTERED = 1 inlined
  - `dstUser` copies a struct from storage in one read; check the bytecode's field read order — src 30282:41:5
  - `totals` copies a struct from storage in one read; check the bytecode's field read order — src 31268:56:5
  - `srcUser` copies a struct from storage in one read; check the bytecode's field read order — src 34465:41:5
  - `dstUser` copies a struct from storage in one read; check the bytecode's field read order — src 34516:41:5
  - `srcUser` copies a struct from storage in one read; check the bytecode's field read order — src 39083:41:5

External calls (for the spec's `ExternalCallABI`):
  - getAssetInfo(uint8) view returns (AssetInfo)
  - latestRoundData() view returns (uint80, int256, uint256, uint256, uint80)
  - balanceOf(address) view returns (uint256)
  - approve(address, uint256) returns ()
  - decimals() view returns (uint8)
  - assetListFactory() view returns (address)
  - createAssetList(AssetConfig) returns (address)
  - transferFrom(address, address, uint256) returns ()
  - transfer(address, uint256) returns ()
-/

open Solm Solm.Notation

namespace Benchmarks.CompoundIII.Comet.Syntax

def contractSyntax : ContractDecl := solidity% contract CometWithExtendedAssetList {
  struct ExtConfiguration {
    bytes32 name32;
    bytes32 symbol32;
  }

  struct Configuration {
    address governor;
    address pauseGuardian;
    address baseToken;
    address baseTokenPriceFeed;
    address extensionDelegate;
    uint64 supplyKink;
    uint64 supplyPerYearInterestRateSlopeLow;
    uint64 supplyPerYearInterestRateSlopeHigh;
    uint64 supplyPerYearInterestRateBase;
    uint64 borrowKink;
    uint64 borrowPerYearInterestRateSlopeLow;
    uint64 borrowPerYearInterestRateSlopeHigh;
    uint64 borrowPerYearInterestRateBase;
    uint64 storeFrontPriceFactor;
    uint64 trackingIndexScale;
    uint64 baseTrackingSupplySpeed;
    uint64 baseTrackingBorrowSpeed;
    uint104 baseMinForRewards;
    uint104 baseBorrowMin;
    uint104 targetReserves;
    AssetConfig[] assetConfigs;
  }

  struct AssetConfig {
    address asset;
    address priceFeed;
    uint8 decimals;
    uint64 borrowCollateralFactor;
    uint64 liquidateCollateralFactor;
    uint64 liquidationFactor;
    uint128 supplyCap;
  }

  struct TotalsBasic {
    uint64 baseSupplyIndex;
    uint64 baseBorrowIndex;
    uint64 trackingSupplyIndex;
    uint64 trackingBorrowIndex;
    uint104 totalSupplyBase;
    uint104 totalBorrowBase;
    uint40 lastAccrualTime;
    uint8 pauseFlags;
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

  struct LiquidatorPoints {
    uint32 numAbsorbs;
    uint64 numAbsorbed;
    uint128 approxSpend;
    uint32 _reserved;
  }

  struct PriceRound {
    uint80 roundId;
    int256 answer;
    uint256 startedAt;
    uint256 updatedAt;
    uint80 answeredInRound;
  }

  struct AssetInfo {
    uint8 offset;
    address asset;
    address priceFeed;
    uint64 scale;
    uint64 borrowCollateralFactor;
    uint64 liquidateCollateralFactor;
    uint64 liquidationFactor;
    uint128 supplyCap;
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
  -- Unused symbolic padding places the assembly-only flag at keccak256("comet.reentrancy.guard").
  -- The ordinary Solidity declarations occupy slots 0 through 7. No statement reads this array.
  uint256[91163063775796598582698250372395185889154745920815755245223157833676084630436] __slotPadding;
  uint256 __reentrancyGuard;
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

  event Supply(address indexed «from», address indexed dst, uint256 amount);
  event Transfer(address indexed «from», address indexed «to», uint256 amount);
  event Withdraw(address indexed src, address indexed «to», uint256 amount);
  event SupplyCollateral(address indexed «from», address indexed dst, address indexed asset, uint256 amount);
  event TransferCollateral(address indexed «from», address indexed «to», address indexed asset, uint256 amount);
  event WithdrawCollateral(address indexed src, address indexed «to», address indexed asset, uint256 amount);
  event AbsorbDebt(address indexed absorber, address indexed borrower, uint256 basePaidOut, uint256 usdValue);
  event AbsorbCollateral(address indexed absorber, address indexed borrower, address indexed asset, uint256 collateralAbsorbed, uint256 usdValue);
  event BuyCollateral(address indexed buyer, address indexed asset, uint256 baseAmount, uint256 collateralAmount);
  event PauseAction(bool supplyPaused, bool transferPaused, bool withdrawPaused, bool absorbPaused, bool buyPaused);
  event WithdrawReserves(address indexed «to», uint256 amount);

  constructor(Configuration memory configTuple) {
    Configuration memory config = Configuration({
      governor: configTuple.0,
      pauseGuardian: configTuple.1,
      baseToken: configTuple.2,
      baseTokenPriceFeed: configTuple.3,
      extensionDelegate: configTuple.4,
      supplyKink: configTuple.5,
      supplyPerYearInterestRateSlopeLow: configTuple.6,
      supplyPerYearInterestRateSlopeHigh: configTuple.7,
      supplyPerYearInterestRateBase: configTuple.8,
      borrowKink: configTuple.9,
      borrowPerYearInterestRateSlopeLow: configTuple.10,
      borrowPerYearInterestRateSlopeHigh: configTuple.11,
      borrowPerYearInterestRateBase: configTuple.12,
      storeFrontPriceFactor: configTuple.13,
      trackingIndexScale: configTuple.14,
      baseTrackingSupplySpeed: configTuple.15,
      baseTrackingBorrowSpeed: configTuple.16,
      baseMinForRewards: configTuple.17,
      baseBorrowMin: configTuple.18,
      targetReserves: configTuple.19,
      assetConfigs: configTuple.20
    });
    var decimals_ = config.baseToken.decimals{view}();
    require(decimals_ <= 18);
    require(config.storeFrontPriceFactor <= 1000000000000000000);
    require(config.assetConfigs.length <= 24);
    require(config.baseMinForRewards != 0);
    var __c1 = config.baseTokenPriceFeed.decimals{view}();
    require(__c1 == 8);
    governor = config.governor;
    pauseGuardian = config.pauseGuardian;
    baseToken = config.baseToken;
    baseTokenPriceFeed = config.baseTokenPriceFeed;
    extensionDelegate = config.extensionDelegate;
    storeFrontPriceFactor = config.storeFrontPriceFactor;
    decimals = decimals_;
    baseScale = uint64(uint256(10 ** decimals_));
    trackingIndexScale = config.trackingIndexScale;
    require(baseScale >= 1000000);
    accrualDescaleFactor = baseScale / 1000000;
    baseMinForRewards = config.baseMinForRewards;
    baseTrackingSupplySpeed = config.baseTrackingSupplySpeed;
    baseTrackingBorrowSpeed = config.baseTrackingBorrowSpeed;
    baseBorrowMin = config.baseBorrowMin;
    targetReserves = config.targetReserves;
    supplyKink = config.supplyKink;
    supplyPerSecondInterestRateSlopeLow = config.supplyPerYearInterestRateSlopeLow / 31536000;
    supplyPerSecondInterestRateSlopeHigh = config.supplyPerYearInterestRateSlopeHigh / 31536000;
    supplyPerSecondInterestRateBase = config.supplyPerYearInterestRateBase / 31536000;
    borrowKink = config.borrowKink;
    borrowPerSecondInterestRateSlopeLow = config.borrowPerYearInterestRateSlopeLow / 31536000;
    borrowPerSecondInterestRateSlopeHigh = config.borrowPerYearInterestRateSlopeHigh / 31536000;
    borrowPerSecondInterestRateBase = config.borrowPerYearInterestRateBase / 31536000;
    numAssets = uint8(config.assetConfigs.length);
    address delegate = extensionDelegate;
    var __c2 = delegate.assetListFactory{view}();
    var __c3 = createAssetList_call(__c2, config.assetConfigs);
    assetList = __c3;
  }

  function createAssetList_call(address factory, AssetConfig[] memory assets) internal returns (address) {
    bytes payload = abi.encodePacked(bytes4(bytes4(0xba15b9d1)), uint256(32), uint256(assets.length));
    uint256 index = 0;
    while (index < assets.length) {
      var entry = assets[index];
      payload = abi.encodePacked(bytes(payload), uint256(uint256(entry.0)),
        uint256(uint256(entry.1)), uint256(entry.2), uint256(entry.3),
        uint256(entry.4), uint256(entry.5), uint256(entry.6));
      index = index + 1;
    }
    (bool ok, bytes memory result) = factory.call(payload);
    require(ok);
    address resultAddress = abi.decode(result, (address));
    return resultAddress;
  }

  function getNowInternal() internal returns (uint40) {
    require(block.timestamp < 1099511627776);
    return uint40(block.timestamp);
  }

  function getAssetInfo_body(uint8 i) internal returns (AssetInfo) {
    address receiver = assetList;
    bytes payload = abi.encodePacked(bytes4(bytes4(0xc8c7fe6b)), uint256(i));
    (bool ok, bytes memory result) = receiver.staticcall(payload);
    require(ok);
    var decoded = abi.decode(result, (AssetInfo));
    return AssetInfo({offset: decoded.0, asset: decoded.1, priceFeed: decoded.2, scale: decoded.3, borrowCollateralFactor: decoded.4, liquidateCollateralFactor: decoded.5, liquidationFactor: decoded.6, supplyCap: decoded.7});
  }

  function accrueInternal() internal {
    var now_ = getNowInternal();
    uint256 timeElapsed = uint256(((now_ - lastAccrualTime) as uint40));
    if (timeElapsed > 0) {
      var __c1 = accruedInterestIndices(timeElapsed);
      baseSupplyIndex = __c1.0;
      baseBorrowIndex = __c1.1;
      if (totalSupplyBase >= baseMinForRewards) {
        var __c2 = divBaseWei(((baseTrackingSupplySpeed * timeElapsed) as uint256), totalSupplyBase);
        var __c3 = safe64(__c2);
        trackingSupplyIndex = ((trackingSupplyIndex + __c3) as uint64);
      }
      if (totalBorrowBase >= baseMinForRewards) {
        var __c4 = divBaseWei(((baseTrackingBorrowSpeed * timeElapsed) as uint256), totalBorrowBase);
        var __c5 = safe64(__c4);
        trackingBorrowIndex = ((trackingBorrowIndex + __c5) as uint64);
      }
      lastAccrualTime = now_;
    }
  }

  function updateBasePrincipal(address account, UserBasic memory basic, int104 principalNew) internal {
    int104 principal = basic.principal;
    basic.principal = principalNew;
    if (principal >= 0) {
      uint256 indexDelta = uint256(((trackingSupplyIndex - basic.baseTrackingIndex) as uint64));
      var __c0 = safe64(((((uint104(principal) * indexDelta) as uint256) / trackingIndexScale) / accrualDescaleFactor));
      basic.baseTrackingAccrued = ((basic.baseTrackingAccrued + __c0) as uint64);
    } else {
      uint256 indexDelta = uint256(((trackingBorrowIndex - basic.baseTrackingIndex) as uint64));
      var __c1 = safe64(((((uint104(((0 - principal) as int104)) * indexDelta) as uint256) / trackingIndexScale) / accrualDescaleFactor));
      basic.baseTrackingAccrued = ((basic.baseTrackingAccrued + __c1) as uint64);
    }
    if (principalNew >= 0) {
      basic.baseTrackingIndex = trackingSupplyIndex;
    } else {
      basic.baseTrackingIndex = trackingBorrowIndex;
    }
    userBasic[account] = basic;
  }

  function safe64(uint256 n) internal returns (uint64) {
    require(n <= type(uint64).max);
    return uint64(n);
  }

  function mulFactor(uint256 n, uint256 factor) internal returns (uint256) {
    return ((n * factor) as uint256) / 1000000000000000000;
  }

  function presentValueSupply(uint64 baseSupplyIndex_, uint104 principalValue_) internal returns (uint256) {
    return ((uint256(principalValue_) * baseSupplyIndex_) as uint256) / 1000000000000000;
  }

  function presentValueBorrow(uint64 baseBorrowIndex_, uint104 principalValue_) internal returns (uint256) {
    return ((uint256(principalValue_) * baseBorrowIndex_) as uint256) / 1000000000000000;
  }

  function accruedInterestIndices(uint256 timeElapsed) internal returns (uint64, uint64) {
    uint64 baseSupplyIndex_ = baseSupplyIndex;
    uint64 baseBorrowIndex_ = baseBorrowIndex;
    if (timeElapsed > 0) {
      var utilization = getUtilization_body();
      var supplyRate = getSupplyRate_body(utilization);
      var borrowRate = getBorrowRate_body(utilization);
      var __c3 = mulFactor(baseSupplyIndex_, ((supplyRate * timeElapsed) as uint256));
      var __c4 = safe64(__c3);
      baseSupplyIndex_ = ((baseSupplyIndex_ + __c4) as uint64);
      var __c5 = mulFactor(baseBorrowIndex_, ((borrowRate * timeElapsed) as uint256));
      var __c6 = safe64(__c5);
      baseBorrowIndex_ = ((baseBorrowIndex_ + __c6) as uint64);
    }
    return (baseSupplyIndex_, baseBorrowIndex_);
  }

  function signed256(uint256 n) internal returns (int256) {
    require(n <= uint256(type(int256).max));
    return int256(n);
  }

  function signedMulPrice(int256 n, uint256 price, uint64 fromScale) internal returns (int256) {
    var __c0 = signed256(price);
    return sdiv(((n * __c0) as int256), int256(uint256(fromScale)));
  }

  function presentValue(int104 principalValue_) internal returns (int256) {
    if (principalValue_ >= 0) {
      var __c0 = presentValueSupply(baseSupplyIndex, uint104(principalValue_));
      var __c1 = signed256(__c0);
      return __c1;
    } else {
      var __c2 = presentValueBorrow(baseBorrowIndex, uint104(((0 - principalValue_) as int104)));
      var __c3 = signed256(__c2);
      return (0 - __c3) as int256;
    }
  }

  function getPrice_body(address priceFeed) internal returns (uint256) {
    bytes payload = abi.encodePacked(bytes4(bytes4(0xfeaf968c)));
    (bool ok, bytes memory result) = priceFeed.staticcall(payload);
    require(ok);
    var __c0 = abi.decode(result, (PriceRound));
    int256 price = __c0.1;
    require(price > 0);
    return uint256(price);
  }

  function isInAsset(uint16 assetsIn, uint8 assetOffset, uint8 _reserved) internal returns (bool) {
    if (assetOffset < 16) {
      return (assetsIn &[uint16] (uint16(1) <<[uint16] assetOffset)) != 0;
    } else {
      if (assetOffset < 24) {
        return (_reserved &[uint8] (uint8(1) <<[uint8] ((assetOffset - 16) as uint8))) != 0;
      }
    }
    return false;
  }

  function mulPrice(uint256 n, uint256 price, uint64 fromScale) internal returns (uint256) {
    return ((n * price) as uint256) / fromScale;
  }

  function toUInt8(bool x) internal returns (uint8) {
    return x ? 1 : 0;
  }

  function toBool(uint8 x) internal returns (bool) {
    return x != 0;
  }

  function supplyInternal(address operator, address «from», address dst, address asset, uint256 amount) internal {
    var __c0 = nonReentrantBefore();
    var __c1 = isSupplyPaused_body();
    require(!__c1);
    var __c2 = hasPermission_body(«from», operator);
    require(__c2);
    if (asset == baseToken) {
      if (amount == type(uint256).max) {
        var __c3 = borrowBalanceOf_body(dst);
        amount = __c3;
      }
      var __c4 = supplyBase(«from», dst, amount);
    } else {
      var __c5 = safe128(amount);
      var __c6 = supplyCollateral(«from», dst, asset, __c5);
    }
    var __c7 = nonReentrantAfter();
  }

  function transferInternal(address operator, address src, address dst, address asset, uint256 amount) internal {
    var __c0 = nonReentrantBefore();
    var __c1 = isTransferPaused_body();
    require(!__c1);
    var __c2 = hasPermission_body(src, operator);
    require(__c2);
    require(src != dst);
    if (asset == baseToken) {
      if (amount == type(uint256).max) {
        var __c3 = balanceOf_body(src);
        amount = __c3;
      }
      var __c4 = transferBase(src, dst, amount);
    } else {
      var __c5 = safe128(amount);
      var __c6 = transferCollateral(src, dst, asset, __c5);
    }
    var __c7 = nonReentrantAfter();
  }

  function withdrawInternal(address operator, address src, address «to», address asset, uint256 amount) internal {
    var __c0 = nonReentrantBefore();
    var __c1 = isWithdrawPaused_body();
    require(!__c1);
    var __c2 = hasPermission_body(src, operator);
    require(__c2);
    if (asset == baseToken) {
      if (amount == type(uint256).max) {
        var __c3 = balanceOf_body(src);
        amount = __c3;
      }
      var __c4 = withdrawBase(src, «to», amount);
    } else {
      var __c5 = safe128(amount);
      var __c6 = withdrawCollateral(src, «to», asset, __c5);
    }
    var __c7 = nonReentrantAfter();
  }

  function isAbsorbPaused_body() internal returns (bool) {
    var __c0 = toBool((pauseFlags &[uint8] (uint8(1) <<[uint8] 3)));
    return __c0;
  }

  function absorbInternal(address absorber, address account) internal {
    var __c0 = isLiquidatable_body(account);
    require(__c0);
    UserBasic memory accountUser = userBasic[account];
    int104 oldPrincipal = accountUser.principal;
    var oldBalance = presentValue(oldPrincipal);
    uint16 assetsIn = accountUser.assetsIn;
    uint8 _reserved = accountUser._reserved;
    var basePrice = getPrice_body(baseTokenPriceFeed);
    uint256 deltaValue = 0;
    uint8 i = 0;
    while (i < numAssets) {
      var __c3 = isInAsset(assetsIn, i, _reserved);
      if (__c3) {
        var assetInfo = getAssetInfo_body(i);
        address asset = assetInfo.asset;
        uint128 seizeAmount = userCollateral[account][asset].balance;
        userCollateral[account][asset].balance = 0;
        totalsCollateral[asset].totalSupplyAsset = ((totalsCollateral[asset].totalSupplyAsset - seizeAmount) as uint128);
        var __c5 = getPrice_body(assetInfo.priceFeed);
        var value = mulPrice(seizeAmount, __c5, assetInfo.scale);
        var __c7 = mulFactor(value, assetInfo.liquidationFactor);
        deltaValue = ((deltaValue + __c7) as uint256);
        emit AbsorbCollateral(absorber, account, asset, seizeAmount, value);
      }
      i = uint8(i + 1);
    }
    var deltaBalance = divPrice(deltaValue, basePrice, uint64(baseScale));
    var __c9 = signed256(deltaBalance);
    int256 newBalance = (oldBalance + __c9) as int256;
    if (newBalance < 0) {
      newBalance = 0;
    }
    var newPrincipal = principalValue(newBalance);
    var __c11 = updateBasePrincipal(account, accountUser, newPrincipal);
    userBasic[account].assetsIn = 0;
    userBasic[account]._reserved = 0;
    var __c12 = repayAndSupplyAmount(oldPrincipal, newPrincipal);
    uint104 repayAmount = __c12.0;
    uint104 supplyAmount = __c12.1;
    totalSupplyBase = ((totalSupplyBase + supplyAmount) as uint104);
    totalBorrowBase = ((totalBorrowBase - repayAmount) as uint104);
    var basePaidOut = unsigned256(((newBalance - oldBalance) as int256));
    var valueOfBasePaidOut = mulPrice(basePaidOut, basePrice, uint64(baseScale));
    emit AbsorbDebt(absorber, account, basePaidOut, valueOfBasePaidOut);
    if (newPrincipal > 0) {
      var __c15 = unsigned104(newPrincipal);
      var __c16 = presentValueSupply(baseSupplyIndex, __c15);
      emit Transfer(address(0), account, __c16);
    }
  }

  function safe128(uint256 n) internal returns (uint128) {
    require(n <= type(uint128).max);
    return uint128(n);
  }

  function nonReentrantBefore() internal {
    uint256 status = __reentrancyGuard;
    require(status != 1);
    __reentrancyGuard = 1;
  }

  function isBuyPaused_body() internal returns (bool) {
    var __c0 = toBool((pauseFlags &[uint8] (uint8(1) <<[uint8] 4)));
    return __c0;
  }

  function getReserves_body() internal returns (int256) {
    var __c0 = getNowInternal();
    var __c1 = accruedInterestIndices(((__c0 - lastAccrualTime) as uint40));
    uint64 baseSupplyIndex_ = __c1.0;
    uint64 baseBorrowIndex_ = __c1.1;
    address token = baseToken;
    var balance = token.balanceOf{view}(address(this));
    var totalSupply_ = presentValueSupply(baseSupplyIndex_, totalSupplyBase);
    var totalBorrow_ = presentValueBorrow(baseBorrowIndex_, totalBorrowBase);
    var __c5 = signed256(balance);
    var __c6 = signed256(totalSupply_);
    var __c7 = signed256(totalBorrow_);
    return (((__c5 - __c6) as int256) + __c7) as int256;
  }

  function doTransferIn(address asset, address «from», uint256 amount) internal returns (uint256) {
    var preTransferBalance = asset.balanceOf{view}(address(this));
    require(asset.code.length > 0);
    (bool ok, bytes memory data) = asset.call(
      abi.encodeWithSelector(transferFrom, «from», address(this), amount));
    require(ok);
    var checked = checkTransferReturn(data);
    var postTransferBalance = asset.balanceOf{view}(address(this));
    return (postTransferBalance - preTransferBalance) as uint256;
  }

  function quoteCollateral_body(address asset, uint256 baseAmount) internal returns (uint256) {
    var assetInfo = getAssetInfoByAddress_body(asset);
    var assetPrice = getPrice_body(assetInfo.priceFeed);
    var discountFactor = mulFactor(storeFrontPriceFactor, ((1000000000000000000 - assetInfo.liquidationFactor) as uint64));
    var assetPriceDiscounted = mulFactor(assetPrice, ((1000000000000000000 - discountFactor) as uint256));
    var basePrice = getPrice_body(baseTokenPriceFeed);
    return (((((basePrice * baseAmount) as uint256) * assetInfo.scale) as uint256) / assetPriceDiscounted) / baseScale;
  }

  function getCollateralReserves_body(address asset) internal returns (uint256) {
    var __c0 = asset.balanceOf{view}(address(this));
    return (__c0 - totalsCollateral[asset].totalSupplyAsset) as uint256;
  }

  function doTransferOut(address asset, address «to», uint256 amount) internal {
    require(asset.code.length > 0);
    (bool ok, bytes memory data) = asset.call(abi.encodeWithSelector(transfer, «to», amount));
    require(ok);
    var checked = checkTransferReturn(data);
  }

  function checkTransferReturn(bytes memory data) internal {
    if (data.length != 0) {
      require(data.length == 32);
      uint256 result = abi.decode(data, (uint256));
      require(result != 0);
    }
  }

  function nonReentrantAfter() internal {
    __reentrancyGuard = 0;
  }

  function unsigned256(int256 n) internal returns (uint256) {
    require(n >= 0);
    return uint256(n);
  }

  function unsigned104(int104 n) internal returns (uint104) {
    require(n >= 0);
    return uint104(n);
  }

  function divBaseWei(uint256 n, uint256 baseWei) internal returns (uint256) {
    return ((n * baseScale) as uint256) / baseWei;
  }

  function getUtilization_body() internal returns (uint256) {
    var totalSupply_ = presentValueSupply(baseSupplyIndex, totalSupplyBase);
    var totalBorrow_ = presentValueBorrow(baseBorrowIndex, totalBorrowBase);
    if (totalSupply_ == 0) {
      return 0;
    } else {
      return ((totalBorrow_ * 1000000000000000000) as uint256) / totalSupply_;
    }
  }

  function getSupplyRate_body(uint256 utilization) internal returns (uint64) {
    if (utilization <= supplyKink) {
      var __c0 = mulFactor(supplyPerSecondInterestRateSlopeLow, utilization);
      var __c1 = safe64(((supplyPerSecondInterestRateBase + __c0) as uint256));
      return __c1;
    } else {
      var __c2 = mulFactor(supplyPerSecondInterestRateSlopeLow, supplyKink);
      var __c3 = mulFactor(supplyPerSecondInterestRateSlopeHigh, ((utilization - supplyKink) as uint256));
      var __c4 = safe64(((((supplyPerSecondInterestRateBase + __c2) as uint256) + __c3) as uint256));
      return __c4;
    }
  }

  function getBorrowRate_body(uint256 utilization) internal returns (uint64) {
    if (utilization <= borrowKink) {
      var __c0 = mulFactor(borrowPerSecondInterestRateSlopeLow, utilization);
      var __c1 = safe64(((borrowPerSecondInterestRateBase + __c0) as uint256));
      return __c1;
    } else {
      var __c2 = mulFactor(borrowPerSecondInterestRateSlopeLow, borrowKink);
      var __c3 = mulFactor(borrowPerSecondInterestRateSlopeHigh, ((utilization - borrowKink) as uint256));
      var __c4 = safe64(((((borrowPerSecondInterestRateBase + __c2) as uint256) + __c3) as uint256));
      return __c4;
    }
  }

  function isSupplyPaused_body() internal returns (bool) {
    var __c0 = toBool((pauseFlags &[uint8] (uint8(1) <<[uint8] 0)));
    return __c0;
  }

  function hasPermission_body(address owner, address manager) internal returns (bool) {
    return (owner == manager) || isAllowed[owner][manager];
  }

  function borrowBalanceOf_body(address account) internal returns (uint256) {
    var __c0 = getNowInternal();
    var __c1 = accruedInterestIndices(((__c0 - lastAccrualTime) as uint40));
    uint64 baseBorrowIndex_ = __c1.1;
    int104 principal = userBasic[account].principal;
    if (principal < 0) {
      var __c2 = unsigned104(((0 - principal) as int104));
      var __c3 = presentValueBorrow(baseBorrowIndex_, __c2);
      return __c3;
    }
    return 0;
  }

  function supplyBase(address «from», address dst, uint256 amount) internal {
    var __c0 = doTransferIn(baseToken, «from», amount);
    amount = __c0;
    var __c1 = accrueInternal();
    UserBasic memory dstUser = userBasic[dst];
    int104 dstPrincipal = dstUser.principal;
    var __c2 = presentValue(dstPrincipal);
    var __c3 = signed256(amount);
    int256 dstBalance = (__c2 + __c3) as int256;
    var dstPrincipalNew = principalValue(dstBalance);
    var __c5 = repayAndSupplyAmount(dstPrincipal, dstPrincipalNew);
    uint104 repayAmount = __c5.0;
    uint104 supplyAmount = __c5.1;
    totalSupplyBase = ((totalSupplyBase + supplyAmount) as uint104);
    totalBorrowBase = ((totalBorrowBase - repayAmount) as uint104);
    var __c6 = updateBasePrincipal(dst, dstUser, dstPrincipalNew);
    emit Supply(«from», dst, amount);
    if (supplyAmount > 0) {
      var __c7 = presentValueSupply(baseSupplyIndex, supplyAmount);
      emit Transfer(address(0), dst, __c7);
    }
  }

  function supplyCollateral(address «from», address dst, address asset, uint128 amount) internal {
    var __c0 = doTransferIn(asset, «from», amount);
    var __c1 = safe128(__c0);
    amount = __c1;
    var assetInfo = getAssetInfoByAddress_body(asset);
    TotalsCollateral memory totals = totalsCollateral[asset];
    totals.totalSupplyAsset = ((totals.totalSupplyAsset + amount) as uint128);
    require(totals.totalSupplyAsset <= assetInfo.supplyCap);
    uint128 dstCollateral = userCollateral[dst][asset].balance;
    uint128 dstCollateralNew = (dstCollateral + amount) as uint128;
    totalsCollateral[asset] = totals;
    userCollateral[dst][asset].balance = dstCollateralNew;
    var __c3 = updateAssetsIn(dst, assetInfo, dstCollateral, dstCollateralNew);
    emit SupplyCollateral(«from», dst, asset, amount);
  }

  function isTransferPaused_body() internal returns (bool) {
    var __c0 = toBool((pauseFlags &[uint8] (uint8(1) <<[uint8] 1)));
    return __c0;
  }

  function balanceOf_body(address account) internal returns (uint256) {
    var __c0 = getNowInternal();
    var __c1 = accruedInterestIndices(((__c0 - lastAccrualTime) as uint40));
    uint64 baseSupplyIndex_ = __c1.0;
    int104 principal = userBasic[account].principal;
    if (principal > 0) {
      var __c2 = unsigned104(principal);
      var __c3 = presentValueSupply(baseSupplyIndex_, __c2);
      return __c3;
    }
    return 0;
  }

  function transferBase(address src, address dst, uint256 amount) internal {
    var __c0 = accrueInternal();
    UserBasic memory srcUser = userBasic[src];
    UserBasic memory dstUser = userBasic[dst];
    int104 srcPrincipal = srcUser.principal;
    int104 dstPrincipal = dstUser.principal;
    var __c1 = presentValue(srcPrincipal);
    var __c2 = signed256(amount);
    int256 srcBalance = (__c1 - __c2) as int256;
    var __c3 = presentValue(dstPrincipal);
    var __c4 = signed256(amount);
    int256 dstBalance = (__c3 + __c4) as int256;
    var srcPrincipalNew = principalValue(srcBalance);
    var dstPrincipalNew = principalValue(dstBalance);
    var __c7 = withdrawAndBorrowAmount(srcPrincipal, srcPrincipalNew);
    uint104 withdrawAmount = __c7.0;
    uint104 borrowAmount = __c7.1;
    var __c8 = repayAndSupplyAmount(dstPrincipal, dstPrincipalNew);
    uint104 repayAmount = __c8.0;
    uint104 supplyAmount = __c8.1;
    totalSupplyBase = (((totalSupplyBase + supplyAmount) as uint104) - withdrawAmount) as uint104;
    totalBorrowBase = (((totalBorrowBase + borrowAmount) as uint104) - repayAmount) as uint104;
    var __c9 = updateBasePrincipal(src, srcUser, srcPrincipalNew);
    var __c10 = updateBasePrincipal(dst, dstUser, dstPrincipalNew);
    if (srcBalance < 0) {
      require(uint256(((0 - srcBalance) as int256)) >= baseBorrowMin);
      var __c11 = isBorrowCollateralized_body(src);
      require(__c11);
    }
    if (withdrawAmount > 0) {
      var __c12 = presentValueSupply(baseSupplyIndex, withdrawAmount);
      emit Transfer(src, address(0), __c12);
    }
    if (supplyAmount > 0) {
      var __c13 = presentValueSupply(baseSupplyIndex, supplyAmount);
      emit Transfer(address(0), dst, __c13);
    }
  }

  function transferCollateral(address src, address dst, address asset, uint128 amount) internal {
    uint128 srcCollateral = userCollateral[src][asset].balance;
    uint128 dstCollateral = userCollateral[dst][asset].balance;
    uint128 srcCollateralNew = (srcCollateral - amount) as uint128;
    uint128 dstCollateralNew = (dstCollateral + amount) as uint128;
    userCollateral[src][asset].balance = srcCollateralNew;
    userCollateral[dst][asset].balance = dstCollateralNew;
    var assetInfo = getAssetInfoByAddress_body(asset);
    var __c1 = updateAssetsIn(src, assetInfo, srcCollateral, srcCollateralNew);
    var __c2 = updateAssetsIn(dst, assetInfo, dstCollateral, dstCollateralNew);
    var __c3 = isBorrowCollateralized_body(src);
    require(__c3);
    emit TransferCollateral(src, dst, asset, amount);
  }

  function isWithdrawPaused_body() internal returns (bool) {
    var __c0 = toBool((pauseFlags &[uint8] (uint8(1) <<[uint8] 2)));
    return __c0;
  }

  function withdrawBase(address src, address «to», uint256 amount) internal {
    var __c0 = accrueInternal();
    UserBasic memory srcUser = userBasic[src];
    int104 srcPrincipal = srcUser.principal;
    var __c1 = presentValue(srcPrincipal);
    var __c2 = signed256(amount);
    int256 srcBalance = (__c1 - __c2) as int256;
    var srcPrincipalNew = principalValue(srcBalance);
    var __c4 = withdrawAndBorrowAmount(srcPrincipal, srcPrincipalNew);
    uint104 withdrawAmount = __c4.0;
    uint104 borrowAmount = __c4.1;
    totalSupplyBase = ((totalSupplyBase - withdrawAmount) as uint104);
    totalBorrowBase = ((totalBorrowBase + borrowAmount) as uint104);
    var __c5 = updateBasePrincipal(src, srcUser, srcPrincipalNew);
    if (srcBalance < 0) {
      require(uint256(((0 - srcBalance) as int256)) >= baseBorrowMin);
      var __c6 = isBorrowCollateralized_body(src);
      require(__c6);
    }
    var __c7 = doTransferOut(baseToken, «to», amount);
    emit Withdraw(src, «to», amount);
    if (withdrawAmount > 0) {
      var __c8 = presentValueSupply(baseSupplyIndex, withdrawAmount);
      emit Transfer(src, address(0), __c8);
    }
  }

  function withdrawCollateral(address src, address «to», address asset, uint128 amount) internal {
    uint128 srcCollateral = userCollateral[src][asset].balance;
    uint128 srcCollateralNew = (srcCollateral - amount) as uint128;
    totalsCollateral[asset].totalSupplyAsset = ((totalsCollateral[asset].totalSupplyAsset - amount) as uint128);
    userCollateral[src][asset].balance = srcCollateralNew;
    var assetInfo = getAssetInfoByAddress_body(asset);
    var __c1 = updateAssetsIn(src, assetInfo, srcCollateral, srcCollateralNew);
    var __c2 = isBorrowCollateralized_body(src);
    require(__c2);
    var __c3 = doTransferOut(asset, «to», amount);
    emit WithdrawCollateral(src, «to», asset, amount);
  }

  function isLiquidatable_body(address account) internal returns (bool) {
    int104 principal = userBasic[account].principal;
    if (principal >= 0) {
      return false;
    }
    uint16 assetsIn = userBasic[account].assetsIn;
    uint8 _reserved = userBasic[account]._reserved;
    var __c0 = presentValue(principal);
    var __c1 = getPrice_body(baseTokenPriceFeed);
    var liquidity = signedMulPrice(__c0, __c1, uint64(baseScale));
    uint8 i = 0;
    while (i < numAssets) {
      var __c3 = isInAsset(assetsIn, i, _reserved);
      if (__c3) {
        if (liquidity >= 0) {
          return false;
        }
        var asset = getAssetInfo_body(i);
        var __c5 = getPrice_body(asset.priceFeed);
        var newAmount = mulPrice(userCollateral[account][asset.asset].balance, __c5, asset.scale);
        var __c7 = mulFactor(newAmount, asset.liquidateCollateralFactor);
        var __c8 = signed256(__c7);
        liquidity = ((liquidity + __c8) as int256);
      }
      i = uint8(i + 1);
    }
    return liquidity < 0;
  }

  function divPrice(uint256 n, uint256 price, uint64 toScale) internal returns (uint256) {
    return ((n * toScale) as uint256) / price;
  }

  function principalValue(int256 presentValue_) internal returns (int104) {
    if (presentValue_ >= 0) {
      var __c0 = principalValueSupply(baseSupplyIndex, uint256(presentValue_));
      var __c1 = signed104(__c0);
      return __c1;
    } else {
      var __c2 = principalValueBorrow(baseBorrowIndex, uint256(((0 - presentValue_) as int256)));
      var __c3 = signed104(__c2);
      return (0 - __c3) as int104;
    }
  }

  function repayAndSupplyAmount(int104 oldPrincipal, int104 newPrincipal) internal returns (uint104, uint104) {
    if (newPrincipal < oldPrincipal) {
      return (0, 0);
    }
    if (newPrincipal <= 0) {
      return (uint104(((newPrincipal - oldPrincipal) as int104)), 0);
    } else {
      if (oldPrincipal >= 0) {
        return (0, uint104(((newPrincipal - oldPrincipal) as int104)));
      } else {
        return (uint104(((0 - oldPrincipal) as int104)), uint104(newPrincipal));
      }
    }
  }

  function getAssetInfoByAddress_body(address asset) internal returns ((uint8, address, address, uint64, uint64, uint64, uint64, uint128)) {
    uint8 i = 0;
    while (i < numAssets) {
      var assetInfo = getAssetInfo_body(i);
      if (assetInfo.asset == asset) {
        return assetInfo;
      }
      i = uint8(i + 1);
    }
    require(false);
  }

  function updateAssetsIn(address account, AssetInfo memory assetInfo, uint128 initialUserBalance, uint128 finalUserBalance) internal {
    if ((initialUserBalance == 0) && (finalUserBalance != 0)) {
      if (assetInfo.offset < 16) {
        userBasic[account].assetsIn = (userBasic[account].assetsIn |[uint16] (uint16(1) <<[uint16] assetInfo.offset));
      } else {
        if (assetInfo.offset < 24) {
          userBasic[account]._reserved = (userBasic[account]._reserved |[uint8] (uint8(1) <<[uint8] ((assetInfo.offset - 16) as uint8)));
        }
      }
    } else {
      if ((initialUserBalance != 0) && (finalUserBalance == 0)) {
        if (assetInfo.offset < 16) {
          userBasic[account].assetsIn = (userBasic[account].assetsIn &[uint16] (~[uint16] (uint16(1) <<[uint16] assetInfo.offset)));
        } else {
          if (assetInfo.offset < 24) {
            userBasic[account]._reserved = (userBasic[account]._reserved &[uint8] (~[uint8] (uint8(1) <<[uint8] ((assetInfo.offset - 16) as uint8))));
          }
        }
      }
    }
  }

  function withdrawAndBorrowAmount(int104 oldPrincipal, int104 newPrincipal) internal returns (uint104, uint104) {
    if (newPrincipal > oldPrincipal) {
      return (0, 0);
    }
    if (newPrincipal >= 0) {
      return (uint104(((oldPrincipal - newPrincipal) as int104)), 0);
    } else {
      if (oldPrincipal <= 0) {
        return (0, uint104(((oldPrincipal - newPrincipal) as int104)));
      } else {
        return (uint104(oldPrincipal), uint104(((0 - newPrincipal) as int104)));
      }
    }
  }

  function isBorrowCollateralized_body(address account) internal returns (bool) {
    int104 principal = userBasic[account].principal;
    if (principal >= 0) {
      return true;
    }
    uint16 assetsIn = userBasic[account].assetsIn;
    uint8 _reserved = userBasic[account]._reserved;
    var __c0 = presentValue(principal);
    var __c1 = getPrice_body(baseTokenPriceFeed);
    var liquidity = signedMulPrice(__c0, __c1, uint64(baseScale));
    uint8 i = 0;
    while (i < numAssets) {
      var __c3 = isInAsset(assetsIn, i, _reserved);
      if (__c3) {
        if (liquidity >= 0) {
          return true;
        }
        var asset = getAssetInfo_body(i);
        var __c5 = getPrice_body(asset.priceFeed);
        var newAmount = mulPrice(userCollateral[account][asset.asset].balance, __c5, asset.scale);
        var __c7 = mulFactor(newAmount, asset.borrowCollateralFactor);
        var __c8 = signed256(__c7);
        liquidity = ((liquidity + __c8) as int256);
      }
      i = uint8(i + 1);
    }
    return liquidity >= 0;
  }

  function signed104(uint104 n) internal returns (int104) {
    require(n <= uint104(type(int104).max));
    return int104(n);
  }

  function principalValueSupply(uint64 baseSupplyIndex_, uint256 presentValue_) internal returns (uint104) {
    var __c0 = safe104((((presentValue_ * 1000000000000000) as uint256) / baseSupplyIndex_));
    return __c0;
  }

  function principalValueBorrow(uint64 baseBorrowIndex_, uint256 presentValue_) internal returns (uint104) {
    var __c0 = safe104((((((((presentValue_ * 1000000000000000) as uint256) + baseBorrowIndex_) as uint256) - 1) as uint256) / baseBorrowIndex_));
    return __c0;
  }

  function safe104(uint256 n) internal returns (uint104) {
    require(n <= type(uint104).max);
    return uint104(n);
  }

  function isLiquidatable(address account) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var result = isLiquidatable_body(account);
    return result;
  }

  function getReserves() external returns (int256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __r = getReserves_body();
    return __r;
  }

  function isSupplyPaused() external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var result = isSupplyPaused_body();
    return result;
  }

  function governor() external returns (address) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return governor;
  }

  function totalSupply() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = getNowInternal();
    var __c1 = accruedInterestIndices(((__c0 - lastAccrualTime) as uint40));
    uint64 baseSupplyIndex_ = __c1.0;
    var __c2 = presentValueSupply(baseSupplyIndex_, totalSupplyBase);
    return __c2;
  }

  function baseTrackingSupplySpeed() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return baseTrackingSupplySpeed;
  }

  function initializeStorage() external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(lastAccrualTime == 0);
    var __c0 = getNowInternal();
    lastAccrualTime = __c0;
    baseSupplyIndex = 1000000000000000;
    baseBorrowIndex = 1000000000000000;
  }

  function storeFrontPriceFactor() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return storeFrontPriceFactor;
  }

  function transferFrom(address src, address dst, uint256 amount) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = transferInternal(msg.sender, src, dst, baseToken, amount);
    return true;
  }

  function pauseGuardian() external returns (address) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return pauseGuardian;
  }

  function withdrawFrom(address src, address «to», address asset, uint256 amount) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = withdrawInternal(msg.sender, src, «to», asset, amount);
    return;
  }

  function borrowPerSecondInterestRateSlopeHigh() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return borrowPerSecondInterestRateSlopeHigh;
  }

  function userCollateral(address arg0, address arg1) external returns (uint128, uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return (userCollateral[arg0][arg1].balance, userCollateral[arg0][arg1]._reserved);
  }

  function borrowPerSecondInterestRateSlopeLow() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return borrowPerSecondInterestRateSlopeLow;
  }

  function userNonce(address arg0) external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return userNonce[arg0];
  }

  function baseBorrowMin() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return baseBorrowMin;
  }

  function decimals() external returns (uint8) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return decimals;
  }

  function targetReserves() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return targetReserves;
  }

  function borrowBalanceOf(address account) external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var result = borrowBalanceOf_body(account);
    return result;
  }

  function isBorrowCollateralized(address account) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var result = isBorrowCollateralized_body(account);
    return result;
  }

  function getAssetInfoByAddress(address asset) external returns ((uint8, address, address, uint64, uint64, uint64, uint64, uint128)) {
    var info = getAssetInfoByAddress_body(asset);
    return tuple(info.offset, info.asset, info.priceFeed, info.scale, info.borrowCollateralFactor, info.liquidateCollateralFactor, info.liquidationFactor, info.supplyCap);
  }

  function getPrice(address priceFeed) external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __r = getPrice_body(priceFeed);
    return __r;
  }

  function supplyTo(address dst, address asset, uint256 amount) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = supplyInternal(msg.sender, msg.sender, dst, asset, amount);
    return;
  }

  function transferAsset(address dst, address asset, uint256 amount) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = transferInternal(msg.sender, msg.sender, dst, asset, amount);
    return;
  }

  function baseScale() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return baseScale;
  }

  function pause(bool supplyPaused, bool transferPaused, bool withdrawPaused, bool absorbPaused, bool buyPaused) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(!(((msg.sender != governor) && (msg.sender != pauseGuardian))));
    var __c0 = toUInt8(supplyPaused);
    var __c1 = toUInt8(transferPaused);
    var __c2 = toUInt8(withdrawPaused);
    var __c3 = toUInt8(absorbPaused);
    var __c4 = toUInt8(buyPaused);
    pauseFlags = ((((uint8(0) |[uint8] (__c0 <<[uint8] 0)) |[uint8] (__c1 <<[uint8] 1)) |[uint8] (__c2 <<[uint8] 2)) |[uint8] (__c3 <<[uint8] 3)) |[uint8] (__c4 <<[uint8] 4);
    emit PauseAction(supplyPaused, transferPaused, withdrawPaused, absorbPaused, buyPaused);
  }

  function extensionDelegate() external returns (address) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return extensionDelegate;
  }

  function totalsCollateral(address arg0) external returns (uint128, uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return (totalsCollateral[arg0].totalSupplyAsset, totalsCollateral[arg0]._reserved);
  }

  function supplyPerSecondInterestRateSlopeLow() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return supplyPerSecondInterestRateSlopeLow;
  }

  function isWithdrawPaused() external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var result = isWithdrawPaused_body();
    return result;
  }

  function balanceOf(address account) external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var result = balanceOf_body(account);
    return result;
  }

  function borrowPerSecondInterestRateBase() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return borrowPerSecondInterestRateBase;
  }

  function quoteCollateral(address asset, uint256 baseAmount) external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __r = quoteCollateral_body(asset, baseAmount);
    return __r;
  }

  function getUtilization() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var result = getUtilization_body();
    return result;
  }

  function supplyPerSecondInterestRateSlopeHigh() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return supplyPerSecondInterestRateSlopeHigh;
  }

  function totalBorrow() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = getNowInternal();
    var __c1 = accruedInterestIndices(((__c0 - lastAccrualTime) as uint40));
    uint64 baseBorrowIndex_ = __c1.1;
    var __c2 = presentValueBorrow(baseBorrowIndex_, totalBorrowBase);
    return __c2;
  }

  function isAbsorbPaused() external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var result = isAbsorbPaused_body();
    return result;
  }

  function supplyFrom(address «from», address dst, address asset, uint256 amount) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = supplyInternal(msg.sender, «from», dst, asset, amount);
    return;
  }

  function absorb(address absorber, address[] calldata accounts) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = isAbsorbPaused_body();
    require(!__c0);
    uint256 startGas = gasleft();
    var __c1 = accrueInternal();
    uint256 i = 0;
    while (i < accounts.length) {
      var __c2 = absorbInternal(absorber, accounts[i]);
      i = uint256(i + 1);
    }
    uint256 endGas = gasleft();
    uint256 gasUsed = ((startGas - endGas) as uint256);
    LiquidatorPoints memory points = liquidatorPoints[absorber];
    points.numAbsorbs = ((points.numAbsorbs + 1) as uint32);
    var __c3 = safe64(accounts.length);
    points.numAbsorbed = ((points.numAbsorbed + __c3) as uint64);
    var __c4 = safe128(((gasUsed * block.basefee) as uint256));
    points.approxSpend = ((points.approxSpend + __c4) as uint128);
    liquidatorPoints[absorber] = points;
  }

  function borrowKink() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return borrowKink;
  }

  function baseMinForRewards() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return baseMinForRewards;
  }

  function supplyPerSecondInterestRateBase() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return supplyPerSecondInterestRateBase;
  }

  function baseTrackingBorrowSpeed() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return baseTrackingBorrowSpeed;
  }

  function getBorrowRate(uint256 utilization) external returns (uint64) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var result = getBorrowRate_body(utilization);
    return result;
  }

  function getCollateralReserves(address asset) external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __r = getCollateralReserves_body(asset);
    return __r;
  }

  function isAllowed(address arg0, address arg1) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return isAllowed[arg0][arg1];
  }

  function isTransferPaused() external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var result = isTransferPaused_body();
    return result;
  }

  function numAssets() external returns (uint8) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return numAssets;
  }

  function supplyKink() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return supplyKink;
  }

  function transfer(address dst, uint256 amount) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = transferInternal(msg.sender, msg.sender, dst, baseToken, amount);
    return true;
  }

  function trackingIndexScale() external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return trackingIndexScale;
  }

  function approveThis(address manager, address asset, uint256 amount) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(msg.sender == governor);
    require(asset.code.length > 0);
    var __c0 = asset.approve(manager, amount);
  }

  function accrueAccount(address account) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = accrueInternal();
    UserBasic memory basic = userBasic[account];
    var __c1 = updateBasePrincipal(account, basic, basic.principal);
  }

  function transferAssetFrom(address src, address dst, address asset, uint256 amount) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = transferInternal(msg.sender, src, dst, asset, amount);
    return;
  }

  function withdrawTo(address «to», address asset, uint256 amount) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = withdrawInternal(msg.sender, msg.sender, «to», asset, amount);
    return;
  }

  function baseToken() external returns (address) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return baseToken;
  }

  function liquidatorPoints(address arg0) external returns (uint32, uint64, uint128, uint32) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return (liquidatorPoints[arg0].numAbsorbs, liquidatorPoints[arg0].numAbsorbed, liquidatorPoints[arg0].approxSpend, liquidatorPoints[arg0]._reserved);
  }

  function getAssetInfo(uint8 i) external returns ((uint8, address, address, uint64, uint64, uint64, uint64, uint128)) {
    var info = getAssetInfo_body(i);
    return tuple(info.offset, info.asset, info.priceFeed, info.scale, info.borrowCollateralFactor, info.liquidateCollateralFactor, info.liquidationFactor, info.supplyCap);
  }

  function hasPermission(address owner, address manager) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var result = hasPermission_body(owner, manager);
    return result;
  }

  function isBuyPaused() external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var result = isBuyPaused_body();
    return result;
  }

  function getSupplyRate(uint256 utilization) external returns (uint64) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var result = getSupplyRate_body(utilization);
    return result;
  }

  function userBasic(address arg0) external returns (int104, uint64, uint64, uint16, uint8) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return (userBasic[arg0].principal, userBasic[arg0].baseTrackingIndex, userBasic[arg0].baseTrackingAccrued, userBasic[arg0].assetsIn, userBasic[arg0]._reserved);
  }

  function assetList() external returns (address) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return assetList;
  }

  function withdrawReserves(address «to», uint256 amount) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(msg.sender == governor);
    var reserves = getReserves_body();
    var __c1 = unsigned256(reserves);
    require(!(((reserves < 0) || (amount > __c1))));
    var __c2 = doTransferOut(baseToken, «to», amount);
    emit WithdrawReserves(«to», amount);
  }

  function buyCollateral(address asset, uint256 minAmount, uint256 baseAmount, address recipient) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = nonReentrantBefore();
    var __c1 = isBuyPaused_body();
    require(!__c1);
    var reserves = getReserves_body();
    require(!(((reserves >= 0) && (uint256(reserves) >= targetReserves))));
    var __c3 = doTransferIn(baseToken, msg.sender, baseAmount);
    baseAmount = __c3;
    var collateralAmount = quoteCollateral_body(asset, baseAmount);
    require(collateralAmount >= minAmount);
    var __c5 = getCollateralReserves_body(asset);
    require(collateralAmount <= __c5);
    var __c6 = safe128(collateralAmount);
    var __c7 = doTransferOut(asset, recipient, __c6);
    emit BuyCollateral(msg.sender, asset, baseAmount, collateralAmount);
    var __c8 = nonReentrantAfter();
  }

  function baseTokenPriceFeed() external returns (address) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return baseTokenPriceFeed;
  }

  function supply(address asset, uint256 amount) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = supplyInternal(msg.sender, msg.sender, msg.sender, asset, amount);
    return;
  }

  function withdraw(address asset, uint256 amount) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = withdrawInternal(msg.sender, msg.sender, msg.sender, asset, amount);
    return;
  }

  fallback(bytes calldata data) external payable returns (bytes) {
    address delegate = extensionDelegate;
    (bool ok, bytes memory result) = delegate.delegatecall(data);
    require(ok);
    return result;
  }

}

end Benchmarks.CompoundIII.Comet.Syntax
