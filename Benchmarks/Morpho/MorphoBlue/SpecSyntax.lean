import Solm.Notation
import Solm.Semantics
import Solm.MetaSolidityLayout

/-!
# Morpho specification

Written from the pinned Morpho v1.0.0 sources and the deployment bytecode report.
ABI structs are tuples at call boundaries; storage structs retain their named fields.
`rawSlots` is an alias for the complete physical storage space, used only by `extSloads`.
-/

open Solm Solm.Notation

namespace Benchmarks.Morpho.MorphoBlue.Syntax

def contractSyntax : ContractDecl := solidity% contract Morpho {
  struct MarketParams {
    address loanToken;
    address collateralToken;
    address oracle;
    address irm;
    uint256 lltv;
  }
  struct Position {
    uint256 supplyShares;
    uint128 borrowShares;
    uint128 collateral;
  }
  struct Market {
    uint128 totalSupplyAssets;
    uint128 totalSupplyShares;
    uint128 totalBorrowAssets;
    uint128 totalBorrowShares;
    uint128 lastUpdate;
    uint128 fee;
  }
  struct Authorization {
    address authorizer;
    address authorized;
    bool isAuthorized;
    uint256 nonce;
    uint256 deadline;
  }
  struct Signature {
    uint8 v;
    bytes32 r;
    bytes32 s;
  }

  bytes32 immutable DOMAIN_SEPARATOR;
  address owner;
  address feeRecipient;
  mapping(bytes32 => mapping(address => Position)) position;
  mapping(bytes32 => Market) market;
  mapping(address => bool) isIrmEnabled;
  mapping(uint256 => bool) isLltvEnabled;
  mapping(address => mapping(address => bool)) isAuthorized;
  mapping(address => uint256) nonce;
  mapping(bytes32 => MarketParams) idToMarketParams;

  -- This final declaration allocates no protocol field; its backend addresses slots directly.
  mapping(uint256 => bytes32) rawSlots;

  constructor(address newOwner) {
    require(newOwner != address(0));
    DOMAIN_SEPARATOR = keccak256(abi.encodePacked(
      bytes32(keccak256("EIP712Domain(uint256 chainId,address verifyingContract)")),
      uint256(block.chainid), uint256(uint256(address(this)))));
    owner = newOwner;
    emit SetOwner(newOwner);
  }

  function MarketParamsLib_id(MarketParams memory marketParams) internal returns (bytes32) {
    return keccak256(abi.encodePacked(
      uint256(uint256(marketParams.0)), uint256(uint256(marketParams.1)),
      uint256(uint256(marketParams.2)), uint256(uint256(marketParams.3)),
      uint256(marketParams.4)));
  }

  function _accrueInterest(MarketParams memory marketParams, bytes32 id) internal {
    uint256 elapsed = (block.timestamp - market[id].lastUpdate) as uint256;
    if (elapsed == 0) {
      return;
    }
    if (marketParams.3 != address(0)) {
      address irm = marketParams.3;
      var marketState = tuple(market[id].totalSupplyAssets, market[id].totalSupplyShares,
        market[id].totalBorrowAssets, market[id].totalBorrowShares,
        market[id].lastUpdate, market[id].fee);
      var borrowRate = irm.borrowRate(marketParams, marketState);
      var __c1 = MathLib_wTaylorCompounded(borrowRate, elapsed);
      var interest = MathLib_wMulDown(market[id].totalBorrowAssets, __c1);
      var __c3 = UtilsLib_toUint128(interest);
      market[id].totalBorrowAssets = ((market[id].totalBorrowAssets + __c3) as uint128);
      var __c4 = UtilsLib_toUint128(interest);
      market[id].totalSupplyAssets = ((market[id].totalSupplyAssets + __c4) as uint128);
      uint256 feeShares = 0;
      if (market[id].fee != 0) {
        var feeAmount = MathLib_wMulDown(interest, market[id].fee);
        var __c6 = SharesMathLib_toSharesDown(feeAmount,
            ((market[id].totalSupplyAssets - feeAmount) as uint256), market[id].totalSupplyShares);
        feeShares = __c6;
        position[id][feeRecipient].supplyShares =
            ((position[id][feeRecipient].supplyShares + feeShares) as uint256);
        var __c7 = UtilsLib_toUint128(feeShares);
        market[id].totalSupplyShares = ((market[id].totalSupplyShares + __c7) as uint128);
      }
      emit AccrueInterest(id, borrowRate, interest, feeShares);
    }
    market[id].lastUpdate = uint128(block.timestamp);
  }

  function UtilsLib_exactlyOneZero(uint256 x, uint256 y) internal returns (bool) {
    return (x == 0) != (y == 0);
  }

  function SharesMathLib_toSharesDown(uint256 assets, uint256 totalAssets,
      uint256 totalShares) internal returns (uint256) {
    var __c0 = MathLib_mulDivDown(assets, ((totalShares + 1000000) as uint256),
        ((totalAssets + 1) as uint256));
    return __c0;
  }

  function SharesMathLib_toAssetsUp(uint256 shares, uint256 totalAssets,
      uint256 totalShares) internal returns (uint256) {
    var __c0 = MathLib_mulDivUp(shares, ((totalAssets + 1) as uint256),
        ((totalShares + 1000000) as uint256));
    return __c0;
  }

  function UtilsLib_toUint128(uint256 x) internal returns (uint128) {
    require(x <= type(uint128).max);
    return uint128(x);
  }

  function _isSenderAuthorized(address onBehalf) internal returns (bool) {
    if (msg.sender == onBehalf) { return true; }
    return isAuthorized[onBehalf][msg.sender];
  }

  function SharesMathLib_toSharesUp(uint256 assets, uint256 totalAssets,
      uint256 totalShares) internal returns (uint256) {
    var __c0 = MathLib_mulDivUp(assets, ((totalShares + 1000000) as uint256),
        ((totalAssets + 1) as uint256));
    return __c0;
  }

  function SharesMathLib_toAssetsDown(uint256 shares, uint256 totalAssets,
      uint256 totalShares) internal returns (uint256) {
    var __c0 = MathLib_mulDivDown(shares, ((totalAssets + 1) as uint256),
        ((totalShares + 1000000) as uint256));
    return __c0;
  }

  function _isHealthy(MarketParams memory marketParams, bytes32 id,
      address borrower) internal returns (bool) {
    if (position[id][borrower].borrowShares == 0) {
      return true;
    }
    address oracle = marketParams.2;
    var collateralPrice = oracle.price{view}();
    var __c1 = _isHealthyWithPrice(marketParams, id, borrower, collateralPrice);
    return __c1;
  }

  function _isHealthyWithPrice(MarketParams memory marketParams, bytes32 id, address borrower,
      uint256 collateralPrice) internal returns (bool) {
    var borrowed = SharesMathLib_toAssetsUp(uint256(position[id][borrower].borrowShares),
      market[id].totalBorrowAssets, market[id].totalBorrowShares);
    var collateralValue = MathLib_mulDivDown(uint256(position[id][borrower].collateral),
      collateralPrice, 1000000000000000000000000000000000000);
    var maxBorrow = MathLib_wMulDown(collateralValue, marketParams.4);
    return maxBorrow >= borrowed;
  }

  function UtilsLib_min(uint256 x, uint256 y) internal returns (uint256) {
    return x < y ? x : y;
  }

  function MathLib_wDivDown(uint256 x, uint256 y) internal returns (uint256) {
    var __c0 = MathLib_mulDivDown(x, 1000000000000000000, y);
    return __c0;
  }

  function MathLib_wMulDown(uint256 x, uint256 y) internal returns (uint256) {
    var __c0 = MathLib_mulDivDown(x, y, 1000000000000000000);
    return __c0;
  }

  function MathLib_mulDivUp(uint256 x, uint256 y, uint256 d) internal returns (uint256) {
    return ((((x * y) as uint256) + ((d - 1) as uint256)) as uint256) / d;
  }

  function MathLib_mulDivDown(uint256 x, uint256 y, uint256 d) internal returns (uint256) {
    return ((x * y) as uint256) / d;
  }

  function MathLib_wTaylorCompounded(uint256 x, uint256 n) internal returns (uint256) {
    uint256 firstTerm = (x * n) as uint256;
    var secondTerm = MathLib_mulDivDown(firstTerm, firstTerm,
        ((2 * 1000000000000000000) as uint256));
    var thirdTerm = MathLib_mulDivDown(secondTerm, firstTerm,
        ((3 * 1000000000000000000) as uint256));
    return (((firstTerm + secondTerm) as uint256) + thirdTerm) as uint256;
  }

  function UtilsLib_zeroFloorSub(uint256 x, uint256 y) internal returns (uint256) {
    return x > y ? x - y : 0;
  }

  function MathLib_wDivUp(uint256 x, uint256 y) internal returns (uint256) {
    var result = MathLib_mulDivUp(x, 1000000000000000000, y);
    return result;
  }

  function SafeTransferLib_safeTransfer(address token, address «to», uint256 value) internal {
    require(token.code.length > 0);
    (bool success, bytes memory returndata) = token.call(
      abi.encodeWithSelector(transfer, «to», value));
    require(success);
    if (returndata.length != 0) {
      require(abi.decode(returndata, (bool)));
    }
  }

  function SafeTransferLib_safeTransferFrom(address token, address «from», address «to»,
      uint256 value) internal {
    require(token.code.length > 0);
    (bool success, bytes memory returndata) = token.call(
      abi.encodeWithSelector(transferFrom, «from», «to», value));
    require(success);
    if (returndata.length != 0) {
      require(abi.decode(returndata, (bool)));
    }
  }

  function setOwner(address newOwner) external {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    require(msg.sender == owner);
    require(newOwner != owner);
    owner = newOwner;
    emit SetOwner(newOwner);
  }

  function accrueInterest(MarketParams memory marketParams) external {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    var id = MarketParamsLib_id(marketParams);
    require(market[id].lastUpdate != 0);
    var __c1 = _accrueInterest(marketParams, id);
  }

  function repay(MarketParams memory marketParams, uint256 assets, uint256 shares,
      address onBehalf, bytes calldata data) external returns (uint256, uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    var id = MarketParamsLib_id(marketParams);
    require(market[id].lastUpdate != 0);
    var __c1 = UtilsLib_exactlyOneZero(assets, shares);
    require(__c1);
    require(onBehalf != address(0));
    var __c2 = _accrueInterest(marketParams, id);
    if (assets > 0) {
      var __c3 = SharesMathLib_toSharesDown(assets, market[id].totalBorrowAssets,
          market[id].totalBorrowShares);
      shares = __c3;
    } else {
      var __c4 = SharesMathLib_toAssetsUp(shares, market[id].totalBorrowAssets,
          market[id].totalBorrowShares);
      assets = __c4;
    }
    var __c5 = UtilsLib_toUint128(shares);
    position[id][onBehalf].borrowShares = ((position[id][onBehalf].borrowShares - __c5) as uint128);
    var __c6 = UtilsLib_toUint128(shares);
    market[id].totalBorrowShares = ((market[id].totalBorrowShares - __c6) as uint128);
    var debtRemaining = UtilsLib_zeroFloorSub(market[id].totalBorrowAssets, assets);
    var __c7 = UtilsLib_toUint128(debtRemaining);
    market[id].totalBorrowAssets = __c7;
    emit Repay(id, msg.sender, onBehalf, assets, shares);
    if (data.length > 0) {
      address callback = msg.sender;
      require(callback.code.length > 0);
      var __c8 = callback.onMorphoRepay(assets, data);
    }
    var __c9 = SafeTransferLib_safeTransferFrom(marketParams.0, msg.sender, address(this), assets);
    return (assets, shares);
  }

  function supplyCollateral(MarketParams memory marketParams, uint256 assets, address onBehalf,
      bytes calldata data) external {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    var id = MarketParamsLib_id(marketParams);
    require(market[id].lastUpdate != 0);
    require(assets != 0);
    require(onBehalf != address(0));
    var __c1 = UtilsLib_toUint128(assets);
    position[id][onBehalf].collateral = ((position[id][onBehalf].collateral + __c1) as uint128);
    emit SupplyCollateral(id, msg.sender, onBehalf, assets);
    if (data.length > 0) {
      address callback = msg.sender;
      require(callback.code.length > 0);
      var __c2 = callback.onMorphoSupplyCollateral(assets, data);
    }
    var __c3 = SafeTransferLib_safeTransferFrom(marketParams.1, msg.sender, address(this), assets);
  }

  function setFee(MarketParams memory marketParams, uint256 newFee) external {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    require(msg.sender == owner);
    var id = MarketParamsLib_id(marketParams);
    require(market[id].lastUpdate != 0);
    require(newFee != market[id].fee);
    require(newFee <= 250000000000000000);
    var __c1 = _accrueInterest(marketParams, id);
    market[id].fee = uint128(newFee);
    emit SetFee(id, newFee);
  }

  function DOMAIN_SEPARATOR() external returns (bytes32) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    return DOMAIN_SEPARATOR;
  }

  function feeRecipient() external returns (address) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    return feeRecipient;
  }

  function enableLltv(uint256 lltv) external {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    require(msg.sender == owner);
    require(!(isLltvEnabled[lltv]));
    require(lltv < 1000000000000000000);
    isLltvEnabled[lltv] = true;
    emit EnableLltv(lltv);
  }

  function borrow(MarketParams memory marketParams, uint256 assets, uint256 shares,
      address onBehalf, address receiver) external returns (uint256, uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    var id = MarketParamsLib_id(marketParams);
    require(market[id].lastUpdate != 0);
    var __c1 = UtilsLib_exactlyOneZero(assets, shares);
    require(__c1);
    require(receiver != address(0));
    var __c2 = _isSenderAuthorized(onBehalf);
    require(__c2);
    var __c3 = _accrueInterest(marketParams, id);
    if (assets > 0) {
      var __c4 = SharesMathLib_toSharesUp(assets, market[id].totalBorrowAssets,
          market[id].totalBorrowShares);
      shares = __c4;
    } else {
      var __c5 = SharesMathLib_toAssetsDown(shares, market[id].totalBorrowAssets,
          market[id].totalBorrowShares);
      assets = __c5;
    }
    var __c6 = UtilsLib_toUint128(shares);
    position[id][onBehalf].borrowShares = ((position[id][onBehalf].borrowShares + __c6) as uint128);
    var __c7 = UtilsLib_toUint128(shares);
    market[id].totalBorrowShares = ((market[id].totalBorrowShares + __c7) as uint128);
    var __c8 = UtilsLib_toUint128(assets);
    market[id].totalBorrowAssets = ((market[id].totalBorrowAssets + __c8) as uint128);
    var __c9 = _isHealthy(marketParams, id, onBehalf);
    require(__c9);
    require(market[id].totalBorrowAssets <= market[id].totalSupplyAssets);
    emit Borrow(id, msg.sender, onBehalf, receiver, assets, shares);
    var __c10 = SafeTransferLib_safeTransfer(marketParams.0, receiver, assets);
    return (assets, shares);
  }

  function enableIrm(address irm) external {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    require(msg.sender == owner);
    require(!(isIrmEnabled[irm]));
    isIrmEnabled[irm] = true;
    emit EnableIrm(irm);
  }

  function withdraw(MarketParams memory marketParams, uint256 assets, uint256 shares,
      address onBehalf, address receiver) external returns (uint256, uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    var id = MarketParamsLib_id(marketParams);
    require(market[id].lastUpdate != 0);
    var __c1 = UtilsLib_exactlyOneZero(assets, shares);
    require(__c1);
    require(receiver != address(0));
    var __c2 = _isSenderAuthorized(onBehalf);
    require(__c2);
    var __c3 = _accrueInterest(marketParams, id);
    if (assets > 0) {
      var __c4 = SharesMathLib_toSharesUp(assets, market[id].totalSupplyAssets,
          market[id].totalSupplyShares);
      shares = __c4;
    } else {
      var __c5 = SharesMathLib_toAssetsDown(shares, market[id].totalSupplyAssets,
          market[id].totalSupplyShares);
      assets = __c5;
    }
    position[id][onBehalf].supplyShares =
        ((position[id][onBehalf].supplyShares - shares) as uint256);
    var __c6 = UtilsLib_toUint128(shares);
    market[id].totalSupplyShares = ((market[id].totalSupplyShares - __c6) as uint128);
    var __c7 = UtilsLib_toUint128(assets);
    market[id].totalSupplyAssets = ((market[id].totalSupplyAssets - __c7) as uint128);
    require(market[id].totalBorrowAssets <= market[id].totalSupplyAssets);
    emit Withdraw(id, msg.sender, onBehalf, receiver, assets, shares);
    var __c8 = SafeTransferLib_safeTransfer(marketParams.0, receiver, assets);
    return (assets, shares);
  }

  function isAuthorized(address arg0, address arg1) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    return isAuthorized[arg0][arg1];
  }

  function position(bytes32 arg0, address arg1) external returns (uint256, uint128, uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    return (position[arg0][arg1].supplyShares, position[arg0][arg1].borrowShares,
        position[arg0][arg1].collateral);
  }

  function nonce(address arg0) external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    return nonce[arg0];
  }

  function extSloads(bytes32[] calldata slots) external returns (bytes32[]) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    uint256 nSlots = slots.length;
    -- PCs 14371 and 11535: array-size and free-memory-pointer allocation guards.
    require(nSlots <= 2 ** 64 - 1);
    require(128 + 32 * (nSlots + 1) <= 2 ** 64 - 1);
    bytes32[] memory res = new bytes32[](nSlots);
    uint256 i = 0;
    while (i < nSlots) {
      bytes32 slot = slots[i];
      uint256 index = i;
      i = (i + 1) as uint256;
      res[index] = rawSlots[uint256(slot)];
    }
    return res;
  }

  -- The compiler delays validating signature.v until after the nonce SSTORE (pc 6060).
  -- A raw entry preserves that order, including StaticModeViolation for a dirty v.
  fallback(bytes calldata __calldata) external returns (bytes) {
    require(__calldata.length >= 4);
    require(__calldata[0] == bytes1(0x80));
    require(__calldata[1] == bytes1(0x69));
    require(__calldata[2] == bytes1(0x21));
    require(__calldata[3] == bytes1(0x8f));
    require(__calldata.length < (2 ** 255 + 4));
    require(__calldata.length >= 164);
    var authorization = abi.decode(__calldata[4:164], (Authorization));
    require(__calldata.length >= 260);
    require(block.timestamp <= authorization.4);
    uint256 usedNonce = nonce[authorization.0];
    nonce[authorization.0] = (usedNonce + 1) as uint256;
    require(authorization.3 == usedNonce);
    -- AUTHORIZATION_TYPEHASH from ConstantsLib, embedded at runtime pc 6129.
    bytes32 hashStruct = keccak256(abi.encodePacked(
      bytes32(bytes32(0x81d0284fb0e2cde18d0553b06189d6f7613c96a01bb5b5e7828eade6a0dcac91)),
      uint256(uint256(authorization.0)), uint256(uint256(authorization.1)),
      uint256(authorization.2 ? 1 : 0), uint256(authorization.3), uint256(authorization.4)));
    bytes32 digest = keccak256(abi.encodePacked(bytes2(bytes2(0x1901)),
      bytes32(DOMAIN_SEPARATOR), bytes32(hashStruct)));
    var signature = abi.decode(__calldata[164:260], (Signature));
    address precompile = address(1);
    (bool success, bytes memory recovered) = precompile.staticcall(abi.encodePacked(
      bytes32(digest), uint256(signature.0), bytes32(signature.1), bytes32(signature.2)));
    require(success);
    address signatory = address(0);
    if (recovered.length != 0) {
      signatory = abi.decode(recovered, (address));
    }
    require(signatory != address(0));
    require(authorization.0 == signatory);
    emit IncrementNonce(msg.sender, authorization.0, authorization.3);
    isAuthorized[authorization.0][authorization.1] = authorization.2;
    emit SetAuthorization(msg.sender, authorization.0, authorization.1, authorization.2);
    return __calldata[0:0];
  }

  function withdrawCollateral(MarketParams memory marketParams, uint256 assets, address onBehalf,
      address receiver) external {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    var id = MarketParamsLib_id(marketParams);
    require(market[id].lastUpdate != 0);
    require(assets != 0);
    require(receiver != address(0));
    var __c1 = _isSenderAuthorized(onBehalf);
    require(__c1);
    var __c2 = _accrueInterest(marketParams, id);
    var __c3 = UtilsLib_toUint128(assets);
    position[id][onBehalf].collateral = ((position[id][onBehalf].collateral - __c3) as uint128);
    var __c4 = _isHealthy(marketParams, id, onBehalf);
    require(__c4);
    emit WithdrawCollateral(id, msg.sender, onBehalf, receiver, assets);
    var __c5 = SafeTransferLib_safeTransfer(marketParams.1, receiver, assets);
  }

  function createMarket(MarketParams memory marketParams) external {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    var id = MarketParamsLib_id(marketParams);
    require(isIrmEnabled[marketParams.3]);
    require(isLltvEnabled[marketParams.4]);
    require(market[id].lastUpdate == 0);
    market[id].lastUpdate = uint128(block.timestamp);
    idToMarketParams[id] = MarketParams({loanToken: marketParams.0,
      collateralToken: marketParams.1, oracle: marketParams.2,
      irm: marketParams.3, lltv: marketParams.4});
    emit CreateMarket(id, marketParams);
    if (marketParams.3 != address(0)) {
      address irm = marketParams.3;
      var marketState = tuple(market[id].totalSupplyAssets, market[id].totalSupplyShares,
        market[id].totalBorrowAssets, market[id].totalBorrowShares,
        market[id].lastUpdate, market[id].fee);
      var __c1 = irm.borrowRate(marketParams, marketState);
    }
  }

  function owner() external returns (address) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    return owner;
  }

  function idToMarketParams(bytes32 arg0) external returns (address, address, address, address,
      uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    return (idToMarketParams[arg0].loanToken, idToMarketParams[arg0].collateralToken,
        idToMarketParams[arg0].oracle, idToMarketParams[arg0].irm, idToMarketParams[arg0].lltv);
  }

  function supply(MarketParams memory marketParams, uint256 assets, uint256 shares,
      address onBehalf, bytes calldata data) external returns (uint256, uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    var id = MarketParamsLib_id(marketParams);
    require(market[id].lastUpdate != 0);
    var __c1 = UtilsLib_exactlyOneZero(assets, shares);
    require(__c1);
    require(onBehalf != address(0));
    var __c2 = _accrueInterest(marketParams, id);
    if (assets > 0) {
      var __c3 = SharesMathLib_toSharesDown(assets, market[id].totalSupplyAssets,
          market[id].totalSupplyShares);
      shares = __c3;
    } else {
      var __c4 = SharesMathLib_toAssetsUp(shares, market[id].totalSupplyAssets,
          market[id].totalSupplyShares);
      assets = __c4;
    }
    position[id][onBehalf].supplyShares =
        ((position[id][onBehalf].supplyShares + shares) as uint256);
    var __c5 = UtilsLib_toUint128(shares);
    market[id].totalSupplyShares = ((market[id].totalSupplyShares + __c5) as uint128);
    var __c6 = UtilsLib_toUint128(assets);
    market[id].totalSupplyAssets = ((market[id].totalSupplyAssets + __c6) as uint128);
    emit Supply(id, msg.sender, onBehalf, assets, shares);
    if (data.length > 0) {
      address callback = msg.sender;
      require(callback.code.length > 0);
      var __c7 = callback.onMorphoSupply(assets, data);
    }
    var __c8 = SafeTransferLib_safeTransferFrom(marketParams.0, msg.sender, address(this), assets);
    return (assets, shares);
  }

  function isLltvEnabled(uint256 arg0) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    return isLltvEnabled[arg0];
  }

  function liquidate(MarketParams memory marketParams, address borrower, uint256 seizedAssets,
      uint256 repaidShares, bytes calldata data) external returns (uint256, uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    var id = MarketParamsLib_id(marketParams);
    require(market[id].lastUpdate != 0);
    var __c1 = UtilsLib_exactlyOneZero(seizedAssets, repaidShares);
    require(__c1);
    var __c2 = _accrueInterest(marketParams, id);
    address oracle = marketParams.2;
    var collateralPrice = oracle.price{view}();
    var __c4 = _isHealthyWithPrice(marketParams, id, borrower, collateralPrice);
    require(!(__c4));
    var __c5 = MathLib_wMulDown(300000000000000000,
        ((1000000000000000000 - marketParams.4) as uint256));
    var __c6 = MathLib_wDivDown(1000000000000000000, ((1000000000000000000 - __c5) as uint256));
    var liquidationIncentiveFactor = UtilsLib_min(1150000000000000000, __c6);
    if (seizedAssets > 0) {
      var seizedAssetsQuoted = MathLib_mulDivUp(seizedAssets, collateralPrice,
          (1000000000000000000000000000000000000));
      var quotedAssets = MathLib_wDivUp(seizedAssetsQuoted, liquidationIncentiveFactor);
      var __c9 = SharesMathLib_toSharesUp(quotedAssets, market[id].totalBorrowAssets,
          market[id].totalBorrowShares);
      repaidShares = __c9;
    } else {
      var debtAssets = SharesMathLib_toAssetsDown(repaidShares,
        market[id].totalBorrowAssets, market[id].totalBorrowShares);
      var incentivized = MathLib_wMulDown(debtAssets, liquidationIncentiveFactor);
      var __c10 = MathLib_mulDivDown(incentivized,
        1000000000000000000000000000000000000, collateralPrice);
      seizedAssets = __c10;
    }
    var repaidAssets = SharesMathLib_toAssetsUp(repaidShares, market[id].totalBorrowAssets,
        market[id].totalBorrowShares);
    var __c12 = UtilsLib_toUint128(repaidShares);
    position[id][borrower].borrowShares =
        ((position[id][borrower].borrowShares - __c12) as uint128);
    var __c13 = UtilsLib_toUint128(repaidShares);
    market[id].totalBorrowShares = ((market[id].totalBorrowShares - __c13) as uint128);
    var debtRemaining = UtilsLib_zeroFloorSub(market[id].totalBorrowAssets, repaidAssets);
    var __c14 = UtilsLib_toUint128(debtRemaining);
    market[id].totalBorrowAssets = __c14;
    var __c15 = UtilsLib_toUint128(seizedAssets);
    position[id][borrower].collateral = ((position[id][borrower].collateral - __c15) as uint128);
    uint256 badDebtShares = 0;
    uint256 badDebtAssets = 0;
    if (position[id][borrower].collateral == 0) {
      badDebtShares = position[id][borrower].borrowShares;
      var __c16 = SharesMathLib_toAssetsUp(badDebtShares, market[id].totalBorrowAssets,
          market[id].totalBorrowShares);
      var __c17 = UtilsLib_min(market[id].totalBorrowAssets, __c16);
      badDebtAssets = __c17;
      var __c18 = UtilsLib_toUint128(badDebtAssets);
      market[id].totalBorrowAssets = ((market[id].totalBorrowAssets - __c18) as uint128);
      var __c19 = UtilsLib_toUint128(badDebtAssets);
      market[id].totalSupplyAssets = ((market[id].totalSupplyAssets - __c19) as uint128);
      var __c20 = UtilsLib_toUint128(badDebtShares);
      market[id].totalBorrowShares = ((market[id].totalBorrowShares - __c20) as uint128);
      position[id][borrower].borrowShares = 0;
    }
    emit Liquidate(id, msg.sender, borrower, repaidAssets, repaidShares, seizedAssets,
        badDebtAssets, badDebtShares);
    var __c21 = SafeTransferLib_safeTransfer(marketParams.1, msg.sender, seizedAssets);
    if (data.length > 0) {
      address callback = msg.sender;
      require(callback.code.length > 0);
      var __c22 = callback.onMorphoLiquidate(repaidAssets, data);
    }
    var __c23 = SafeTransferLib_safeTransferFrom(marketParams.0, msg.sender, address(this),
        repaidAssets);
    return (seizedAssets, repaidAssets);
  }

  function flashLoan(address token, uint256 assets, bytes calldata data) external {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    require(assets != 0);
    emit FlashLoan(msg.sender, token, assets);
    var __c0 = SafeTransferLib_safeTransfer(token, msg.sender, assets);
    address callback = msg.sender;
      require(callback.code.length > 0);
    var __c1 = callback.onMorphoFlashLoan(assets, data);
    var __c2 = SafeTransferLib_safeTransferFrom(token, msg.sender, address(this), assets);
  }

  function market(bytes32 arg0) external returns (uint128, uint128, uint128, uint128, uint128,
      uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    return (market[arg0].totalSupplyAssets, market[arg0].totalSupplyShares,
        market[arg0].totalBorrowAssets, market[arg0].totalBorrowShares, market[arg0].lastUpdate,
        market[arg0].fee);
  }

  function setFeeRecipient(address newFeeRecipient) external {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    require(msg.sender == owner);
    require(newFeeRecipient != feeRecipient);
    feeRecipient = newFeeRecipient;
    emit SetFeeRecipient(newFeeRecipient);
  }

  function setAuthorization(address authorized, bool newIsAuthorized) external {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    require(newIsAuthorized != isAuthorized[msg.sender][authorized]);
    isAuthorized[msg.sender][authorized] = newIsAuthorized;
    emit SetAuthorization(msg.sender, msg.sender, authorized, newIsAuthorized);
  }

  function isIrmEnabled(address arg0) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < (2 ** 255 + 4));
    return isIrmEnabled[arg0];
  }

}

/- The synthetic raw-slot view comes last, leaving all nine Solidity roots at slots 0–8. -/
def declaredLayout : StorageLayout :=
  solidityLayout! [contractSyntax.structs] [contractSyntax.storage]

def modelLayout : StorageLayout := fun ref ↦
  match ref with
  | { base := "rawSlots", steps := [.mindex slot] } =>
      some (.leaf {
        slot := keyValueToWord slot
        offset := ⟨0, by decide⟩
        size := ⟨32, by decide⟩
        hbound := by decide
        type := .bytes ⟨31, by decide⟩ })
  | _ => declaredLayout ref

def modelStorageBackend : StorageBackend := solidityStorageBackend modelLayout

def uint256ABI : ABI.ABIType := .elem (.int (.uint ⟨256, by decide⟩))
def uint128ABI : ABI.ABIType := .elem (.int (.uint ⟨128, by decide⟩))
def addressABI : ABI.ABIType := .elem .address
def marketParamsABI : ABI.ABIType :=
  .tuple [addressABI, addressABI, addressABI, addressABI, uint256ABI]
def marketABI : ABI.ABIType := .tuple (List.replicate 6 uint128ABI)

-- These are the callees' signatures, including the tuple expansion prescribed by the ABI.
def externalSignature : String → Option ABI.Signature
  | "borrowRate" => some ⟨"borrowRate", [marketParamsABI, marketABI]⟩
  | "price" => some ⟨"price", []⟩
  | "transfer" => some ⟨"transfer", [addressABI, uint256ABI]⟩
  | "transferFrom" => some ⟨"transferFrom", [addressABI, addressABI, uint256ABI]⟩
  | "onMorphoSupply" => some ⟨"onMorphoSupply", [uint256ABI, .bytes]⟩
  | "onMorphoRepay" => some ⟨"onMorphoRepay", [uint256ABI, .bytes]⟩
  | "onMorphoSupplyCollateral" => some ⟨"onMorphoSupplyCollateral", [uint256ABI, .bytes]⟩
  | "onMorphoLiquidate" => some ⟨"onMorphoLiquidate", [uint256ABI, .bytes]⟩
  | "onMorphoFlashLoan" => some ⟨"onMorphoFlashLoan", [uint256ABI, .bytes]⟩
  | _ => none

def modelExternalABI : ExternalCallABI where
  encode? := fun name args ↦ do
    let sig ← externalSignature name
    let sel := (Ethereum.KEC (ABI.printSignature sig).toUTF8).extract 0 4
    ABI.encodeCallWithSelector? sel sig.paramTypes args
  decode? := fun name out ↦
    if name == "borrowRate" || name == "price" then
      (ABI.decodeReturnValueWithMode? .modern uint256ABI out).map (fun v ↦ [v])
    else if name == "transfer" || name == "transferFrom" then
      (ABI.decodeReturnValueWithMode? .modern (.elem .bool) out).map (fun v ↦ [v])
    else if ["onMorphoSupply", "onMorphoRepay", "onMorphoSupplyCollateral",
      "onMorphoLiquidate", "onMorphoFlashLoan"].contains name then some []
    else none

end Benchmarks.Morpho.MorphoBlue.Syntax
