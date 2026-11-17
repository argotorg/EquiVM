import Stele.Notation

/-!
# Midnight value-level specification

Source contract `Midnight`, solc 0.8.34, via-IR; linearisation: Midnight → IMidnight.
Transitions are in selector order (the dispatcher order).

The initial 22-hole translation report is retained in `Midnight.spec.json`.
The authored bodies below close those holes and restore conditional evaluation of
calls hoisted by the translator. The block audit and gas argument are recorded in HANDOFF.md.

NOTES:
  - constant WAD = 1000000000000000000 inlined
  - constant CBP = 1000000000000 inlined
  - constant MAX_CONTINUOUS_FEE = uint32((uint256(10000000000000000) / uint256(31536000))) inlined
  - constant CALLBACK_SUCCESS = keccak256("morpho.midnight.callbackSuccess") = 0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2 inlined
  - constant LIQUIDATION_LOCK_SLOT = uint256(keccak256("morpho.midnight.liquidationLocked")) inlined
  - constant MAX_COLLATERALS_PER_BORROWER = 16 inlined
  - `_collateralParam` is a value copy of a calldata struct, validated by the initial Market decode.
  - constant ORACLE_PRICE_SCALE = 1000000000000000000000000000000000000 inlined
  - constant TIME_TO_MAX_LIF = 3600 inlined
  - constant MAX_COLLATERALS = 128 inlined
  - constant DEFAULT_TICK_SPACING = 4 inlined
  - constant MAX_TICK = 6744 inlined
  - constant LN_ONE_PLUS_DELTA = 4987541511039073 inlined
  - constant PRICE_ROUNDING_STEP = 100000000000 inlined
  - `collateralParam` is a value copy of a decoded memory struct; it does not read persistent storage.

External calls (for the spec's `ExternalCallABI`):
  - isRatified(Offer, bytes, address) view returns (bytes32)
  - canIncreaseCredit(address) view returns (bool)
  - canIncreaseDebt(address) view returns (bool)
  - onBuy(bytes32, Market, uint256, uint256, uint256, address, bytes) returns (bytes32)
  - onSell(bytes32, Market, uint256, uint256, uint256, address, address, bytes) returns (bytes32)
  - onRepay(bytes32, Market, uint256, address, bytes) returns (bytes32)
  - price() view returns (uint256)
  - canLiquidate(address) view returns (bool)
  - onLiquidate(address, bytes32, Market, uint256, uint256, uint256, address, address, bytes, uint256) returns (bytes32)
  - onFlashLoan(address, address[], uint256[], bytes) returns (bytes32)
-/

open Stele Stele.Notation

namespace Benchmarks.Midnight.Syntax

def contractSyntax : ContractDecl := solidity% contract Midnight {
  struct Market {
    uint256 chainId;
    address midnight;
    address loanToken;
    CollateralParams[] collateralParams;
    uint256 maturity;
    uint256 rcfThreshold;
    address enterGate;
    address liquidatorGate;
  }

  struct CollateralParams {
    address token;
    uint256 lltv;
    uint256 liquidationCursor;
    address oracle;
  }

  struct Offer {
    Market market;
    bool buy;
    address maker;
    uint256 start;
    uint256 expiry;
    uint256 tick;
    bytes32 group;
    address callback;
    bytes callbackData;
    address receiverIfMakerIsSeller;
    address ratifier;
    bool reduceOnly;
    uint128 maxUnits;
    uint128 maxAssets;
    uint256 continuousFeeCap;
  }

  struct MarketState {
    uint128 totalUnits;
    uint128 lossFactor;
    uint128 withdrawable;
    uint128 continuousFeeCredit;
    uint16 settlementFeeCbp0;
    uint16 settlementFeeCbp1;
    uint16 settlementFeeCbp2;
    uint16 settlementFeeCbp3;
    uint16 settlementFeeCbp4;
    uint16 settlementFeeCbp5;
    uint16 settlementFeeCbp6;
    uint32 continuousFee;
    uint8 tickSpacing;
  }

  struct Position {
    uint128 credit;
    uint128 pendingFee;
    uint128 lastLossFactor;
    uint128 lastAccrual;
    uint128 debt;
    uint128 collateralBitmap;
    uint128[128] collateral;
  }

  mapping(bytes32 => mapping(address => Position)) position;
  mapping(bytes32 => MarketState) marketState;
  mapping(address => mapping(bytes32 => uint128)) consumed;
  mapping(address => mapping(address => bool)) isAuthorized;
  mapping(address => uint16[7]) defaultSettlementFeeCbp;
  mapping(address => uint32) defaultContinuousFee;
  mapping(address => uint256) claimableSettlementFee;
  mapping(uint256 => bool) isLltvEnabled;
  mapping(uint256 => bool) isLiquidationCursorEnabled;
  address configurator;
  address feeSetter;
  address feeClaimer;
  address tickSpacingSetter;

  -- UtilsLib hashes all three ABI words together, not Solidity's nested mapping hashes.
  -- The local configuration supplies that layout and reads the entire transient word.
  mapping(uint256 => mapping(bytes32 => mapping(address => uint256))) transient locks;

  constructor() {
    configurator = msg.sender;
    emit Constructor(msg.sender);
  }

  function maxSettlementFee(uint256 index) internal returns (uint256) {
    var fees = ${Expr.arrayLit ([14000000000000, 14000000000000, 98000000000000,
      417000000000000, 1250000000000000, 2500000000000000, 5000000000000000].map Expr.intLit)};
    return fees[index];
  }

  function SafeTransferLib_safeTransfer(address token, address «to», uint256 value) internal {
    require(token.code.length > 0);
    bytes payload = abi.encodeWithSelector(transfer, «to», value);
    (bool success, bytes returndata) = token.call(payload);
    require(returndata.length <= 18446744073709551615);
    if (!(success)) {
      require(false);
    }
    require((returndata.length == 0) || abi.decode(returndata, (bool)));
  }

  function touchMarket_body(Market memory market) internal returns (bytes32) {
    var id = IdLib_toId(market);
    if (marketState[id].tickSpacing == 0) {
      require(market.chainId == block.chainid);
      require(market.midnight == address(this));
      require(market.maturity <= ((block.timestamp + 3153600000) as uint256));
      require(market.collateralParams.length > 0);
      require(market.collateralParams.length <= 128);
      address previousCollateralToken = address(0);
      for (uint256 i = 0; i < market.collateralParams.length; i = ((i + 1) as uint256)) {
        address collateralToken = market.collateralParams[i].token;
        require(collateralToken > previousCollateralToken);
        uint256 lltv = market.collateralParams[i].lltv;
        require(isLltvEnabled[lltv]);
        uint256 liquidationCursor = market.collateralParams[i].liquidationCursor;
        require(isLiquidationCursorEnabled[liquidationCursor]);
        var _maxLif = maxLif(lltv, liquidationCursor);
        require(_maxLif <= ((2 * 1000000000000000000) as uint256));
        require((lltv == 1000000000000000000) ||
          (((lltv * _maxLif) as uint256) <= 999000000000000000000000000000000000));
        previousCollateralToken = collateralToken;
      }
      MarketState storage _marketState = marketState[id];
      _marketState.tickSpacing = 4;
      uint16[7] memory _defaultSettlementFeeCbp = defaultSettlementFeeCbp[market.loanToken];
      _marketState.settlementFeeCbp0 = _defaultSettlementFeeCbp[0];
      _marketState.settlementFeeCbp1 = _defaultSettlementFeeCbp[1];
      _marketState.settlementFeeCbp2 = _defaultSettlementFeeCbp[2];
      _marketState.settlementFeeCbp3 = _defaultSettlementFeeCbp[3];
      _marketState.settlementFeeCbp4 = _defaultSettlementFeeCbp[4];
      _marketState.settlementFeeCbp5 = _defaultSettlementFeeCbp[5];
      _marketState.settlementFeeCbp6 = _defaultSettlementFeeCbp[6];
      _marketState.continuousFee = defaultContinuousFee[market.loanToken];
      var __c2 = IdLib_storeInCode(market);
      emit MarketCreated(market, id);
    }
    return id;
  }

  function UtilsLib_toUint128(uint256 x) internal returns (uint128) {
    require(x <= type(uint128).max);
    return uint128(x);
  }

  function TickLib_tickToPrice(uint256 tick) internal returns (uint256) {
    require(tick <= 6744);
    var __c0 = TickLib_wExp(int256(4987541511039073 * (int256(int256((6744 / 2)) - int256(tick)))));
    var __c1 = TickLib_divHalfDownUnchecked(uint256(1000000000000000000000000000000000000), uint256(1000000000000000000 + __c0));
    var __c2 = TickLib_divHalfDownUnchecked(__c1, 100000000000);
    return uint256(__c2 * 100000000000);
  }

  function UtilsLib_zeroFloorSub(uint256 x, uint256 y) internal returns (uint256) {
    return (x > y) ? (x - y) : 0;
  }

  function settlementFee_body(bytes32 id, uint256 timeToMaturity) internal returns (uint256) {
    MarketState storage _marketState = marketState[id];
    require(_marketState.tickSpacing > 0);
    if (timeToMaturity >= 31104000) {
      return (_marketState.settlementFeeCbp6 * 1000000000000) as uint256;
    }
    uint256 start = 15552000;
    uint256 «end» = 31104000;
    uint256 feeLower = 0;
    uint256 feeUpper = 0;
    if (timeToMaturity < 86400) {
      start = 0;
      «end» = 86400;
      feeLower = _marketState.settlementFeeCbp0 * 1000000000000;
      feeUpper = _marketState.settlementFeeCbp1 * 1000000000000;
    } else if (timeToMaturity < 604800) {
      start = 86400;
      «end» = 604800;
      feeLower = _marketState.settlementFeeCbp1 * 1000000000000;
      feeUpper = _marketState.settlementFeeCbp2 * 1000000000000;
    } else if (timeToMaturity < 2592000) {
      start = 604800;
      «end» = 2592000;
      feeLower = _marketState.settlementFeeCbp2 * 1000000000000;
      feeUpper = _marketState.settlementFeeCbp3 * 1000000000000;
    } else if (timeToMaturity < 7776000) {
      start = 2592000;
      «end» = 7776000;
      feeLower = _marketState.settlementFeeCbp3 * 1000000000000;
      feeUpper = _marketState.settlementFeeCbp4 * 1000000000000;
    } else if (timeToMaturity < 15552000) {
      start = 7776000;
      «end» = 15552000;
      feeLower = _marketState.settlementFeeCbp4 * 1000000000000;
      feeUpper = _marketState.settlementFeeCbp5 * 1000000000000;
    } else {
      feeLower = _marketState.settlementFeeCbp5 * 1000000000000;
      feeUpper = _marketState.settlementFeeCbp6 * 1000000000000;
    }
    return ((((feeLower * ((«end» - timeToMaturity) as uint256)) as uint256) + ((feeUpper * ((timeToMaturity - start) as uint256)) as uint256)) as uint256) / ((«end» - start) as uint256);
  }

  function UtilsLib_mulDivDown(uint256 x, uint256 y, uint256 d) internal returns (uint256) {
    return ((x * y) as uint256) / d;
  }

  function UtilsLib_mulDivUp(uint256 x, uint256 y, uint256 d) internal returns (uint256) {
    return ((((x * y) as uint256) + ((d - 1) as uint256)) as uint256) / d;
  }

  function hasCredit(bytes32 id, address user) internal returns (bool) {
    return position[id][user].credit > 0;
  }

  function _updatePosition(Market memory market, bytes32 id, address user) internal returns (uint128, uint128, uint128) {
    Position storage _position = position[id][user];
    var __c0 = updatePositionView_body(market, id, user);
    uint128 newCredit = __c0.0;
    uint128 newPendingFee = __c0.1;
    uint128 accruedFee = __c0.2;
    uint128 creditDecrease = (_position.credit - newCredit) as uint128;
    uint128 pendingFeeDecrease = (_position.pendingFee - newPendingFee) as uint128;
    _position.credit = newCredit;
    _position.lastLossFactor = marketState[id].lossFactor;
    _position.pendingFee = newPendingFee;
    _position.lastAccrual = uint128(block.timestamp);
    var __c1 = UtilsLib_toUint128(accruedFee);
    marketState[id].continuousFeeCredit = ((marketState[id].continuousFeeCredit + __c1) as uint128);
    emit UpdatePosition(id, user, creditDecrease, pendingFeeDecrease, accruedFee);
    return (newCredit, newPendingFee, accruedFee);
  }

  function UtilsLib_min(uint256 x, uint256 y) internal returns (uint256) {
    return (y < x) ? y : x;
  }

  function UtilsLib_tExchange(uint256 baseSlot, bytes32 key1, address key2, bool value) internal returns (bool) {
    bool previous = locks[baseSlot][key1][key2] != 0;
    locks[baseSlot][key1][key2] = value ? 1 : 0;
    return previous;
  }

  function SafeTransferLib_safeTransferFrom(address token, address «from», address «to», uint256 value) internal {
    require(token.code.length > 0);
    bytes payload = abi.encodeWithSelector(transferFrom, «from», «to», value);
    (bool success, bytes returndata) = token.call(payload);
    require(returndata.length <= 18446744073709551615);
    if (!(success)) {
      require(false);
    }
    require((returndata.length == 0) || abi.decode(returndata, (bool)));
  }

  function liquidationLocked_body(bytes32 id, address user) internal returns (bool) {
    var __c0 = UtilsLib_tGet((uint256(keccak256("morpho.midnight.liquidationLocked"))), id, user);
    return __c0;
  }

  function isHealthy_body(Market memory market, bytes32 id, address borrower) internal returns (bool) {
    Position storage _position = position[id][borrower];
    uint256 _debt = _position.debt;
    uint256 maxDebt = 0;
    if (_debt > 0) {
      uint128 _collateralBitmap = _position.collateralBitmap;
      while (_collateralBitmap != 0) {
        var i = UtilsLib_msb(_collateralBitmap);
        CollateralParams memory collateralParam = market.collateralParams[i];
        var price = collateralParam.oracle.price{view}();
        var __c2 = UtilsLib_mulDivDown(_position.collateral[i], price, (1000000000000000000000000000000000000));
        var __c3 = UtilsLib_mulDivDown(__c2, collateralParam.lltv, 1000000000000000000);
        maxDebt = ((maxDebt + __c3) as uint256);
        var __c4 = UtilsLib_clearBit(_collateralBitmap, i);
        _collateralBitmap = __c4;
      }
    }
    return maxDebt >= _debt;
  }

  function UtilsLib_setBit(uint128 bitmap, uint256 bit) internal returns (uint128) {
    return uint128((bitmap |[uint256] (1 <<[uint256] bit)));
  }

  function UtilsLib_countBits(uint128 x) internal returns (uint256) {
    x = uint128(x - ((x >>[uint128] 1) &[uint128] 113427455640312821154458202477256070485));
    x = uint128((x &[uint128] 68056473384187692692674921486353642291) + ((x >>[uint128] 2) &[uint128] 68056473384187692692674921486353642291));
    x = (uint128(x + (x >>[uint128] 4))) &[uint128] 20016609818878733144904388672456953615;
    return (uint128(x * 1334440654591915542993625911497130241)) >>[uint128] 120;
  }

  function UtilsLib_clearBit(uint128 bitmap, uint256 bit) internal returns (uint128) {
    return uint128((bitmap &[uint256] (~[uint256] (1 <<[uint256] bit))));
  }

  function UtilsLib_msb(uint128 bitmap) internal returns (uint256) {
    -- sub(255, clz(bitmap)), including its wrapping zero-input result.
    uint256 res = type(uint256).max;
    uint256 bits = bitmap;
    while (bits != 0) {
      res = uint256(res + 1);
      bits = bits >>[uint256] 1;
    }
    return res;
  }

  function maxLif(uint256 lltv, uint256 liquidationCursor) internal returns (uint256) {
    var __c0 = UtilsLib_mulDivDown(liquidationCursor, ((1000000000000000000 - lltv) as uint256), 1000000000000000000);
    var __c1 = UtilsLib_mulDivDown(1000000000000000000, 1000000000000000000, ((1000000000000000000 - __c0) as uint256));
    return __c1;
  }

  function IdLib_toId(Market memory market) internal returns (bytes32) {
    bytes encoded = abi.encodeWithSelector(encodeMarket, market);
    bytes initcode = abi.encodePacked(bytes11(bytes11(0x600b380380600b5f395ff3)), bytes(encoded));
    return keccak256(abi.encodePacked(uint8(255), address(market.midnight), uint256(0),
      bytes32(keccak256(initcode))));
  }

  function IdLib_storeInCode(Market memory market) internal returns (address) {
    address create2Address = address(0);
    ${[Stmt.new "SSTORE2" (.intLit 0) [.var "market"] "create2Address"
      (some (.fixedBytesLit ⟨31, by decide⟩ (List.replicate 32 0)))]}
    require(create2Address != address(0));
    return create2Address;
  }

  function TickLib_divHalfDownUnchecked(uint256 x, uint256 d) internal returns (uint256) {
    return (uint256(x + ((uint256(d - 1)) / 2))) / d;
  }

  function TickLib_wExp(int256 x) internal returns (uint256) {
    if (x < 0) {
      var __c0 = TickLib_wExp(int256(0 - x));
      return 1000000000000000000000000000000000000 / __c0;
    } else {
      int256 ln2 = 693147180559945309;
      int256 offset = 322611214989459870;
      int256 q = sdiv((int256(x + offset)), ln2);
      int256 r = int256(x - int256(q * ln2));
      int256 secondTerm = sdiv(int256(r * r), 2000000000000000000);
      int256 thirdTerm = sdiv(int256(secondTerm * r), 3000000000000000000);
      int256 expR = int256(int256(int256(1000000000000000000 + r) + secondTerm) + thirdTerm);
      return uint256(expR) <<[uint256] uint256(q);
    }
  }

  function updatePositionView_body(Market memory market, bytes32 id, address user) internal returns (uint128, uint128, uint128) {
    Position storage _position = position[id][user];
    uint128 _credit = _position.credit;
    uint128 _lastLossFactor = _position.lastLossFactor;
    uint256 postSlashCredit = 0;
    if (_lastLossFactor < type(uint128).max) {
      var slashed = UtilsLib_mulDivDown(_credit,
        ((type(uint128).max - marketState[id].lossFactor) as uint128),
        ((type(uint128).max - _lastLossFactor) as uint128));
      postSlashCredit = slashed;
    }
    uint128 _pendingFee = _position.pendingFee;
    uint256 postSlashPendingFee = 0;
    if (_credit > 0) {
      var decrease = UtilsLib_mulDivUp(_pendingFee, ((_credit - postSlashCredit) as uint256), _credit);
      postSlashPendingFee = (_pendingFee - decrease) as uint256;
    }
    var accrualEnd = UtilsLib_min(block.timestamp, market.maturity);
    uint128 _lastAccrual = _position.lastAccrual;
    uint128 fee = 0;
    if (_lastAccrual < market.maturity) {
      var accrued = UtilsLib_mulDivDown(postSlashPendingFee,
        ((accrualEnd - _lastAccrual) as uint256), ((market.maturity - _lastAccrual) as uint256));
      fee = uint128(accrued);
    }
    return (((uint128(postSlashCredit) - fee) as uint128), ((uint128(postSlashPendingFee) - fee) as uint128), fee);
  }

  function UtilsLib_tGet(uint256 baseSlot, bytes32 key1, address key2) internal returns (bool) {
    return locks[baseSlot][key1][key2] != 0;
  }

  function liquidationLocked(bytes32 id, address user) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __r = liquidationLocked_body(id, user);
    return __r;
  }

  function setDefaultContinuousFee(address loanToken, uint256 newContinuousFee) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(msg.sender == feeSetter);
    require(newContinuousFee <= (uint32((uint256(10000000000000000) / uint256(31536000)))));
    defaultContinuousFee[loanToken] = uint32(newContinuousFee);
    emit SetDefaultContinuousFee(loanToken, newContinuousFee);
  }

  function defaultContinuousFee(address arg0) external returns (uint32) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return defaultContinuousFee[arg0];
  }

  function settlementFeeCbps(bytes32 id) external returns (uint16[7]) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return ${Expr.arrayLit ((List.range 7).map fun i ↦ .storage
      { base := "marketState", steps := [.mindex (.var "id"),
        .field ("settlementFeeCbp" ++ toString i)] })};
  }

  function claimSettlementFee(address token, uint256 amount, address receiver) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(msg.sender == feeClaimer);
    claimableSettlementFee[token] = ((claimableSettlementFee[token] - amount) as uint256);
    emit ClaimSettlementFee(msg.sender, token, amount, receiver);
    var __c0 = SafeTransferLib_safeTransfer(token, receiver, amount);
  }

  function configurator() external returns (address) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return configurator;
  }

  function supplyCollateral(Market memory market, uint256 collateralIndex, uint256 assets, address onBehalf) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require((onBehalf == msg.sender) || isAuthorized[onBehalf][msg.sender]);
    var id = touchMarket_body(market);
    address collateralToken = market.collateralParams[collateralIndex].token;
    Position storage _position = position[id][onBehalf];
    uint256 oldCollateral = _position.collateral[collateralIndex];
    if ((oldCollateral == 0) && (assets > 0)) {
      address oracle = market.collateralParams[collateralIndex].oracle;
      var __c1 = oracle.price{view}();
      var newCollateralBitmap = UtilsLib_setBit(_position.collateralBitmap, collateralIndex);
      _position.collateralBitmap = newCollateralBitmap;
      var __c3 = UtilsLib_countBits(newCollateralBitmap);
      require(__c3 <= 16);
    }
    var __c4 = UtilsLib_toUint128(((oldCollateral + assets) as uint256));
    _position.collateral[collateralIndex] = __c4;
    emit SupplyCollateral(msg.sender, id, collateralToken, assets, onBehalf);
    var __c5 = SafeTransferLib_safeTransferFrom(collateralToken, msg.sender, address(this), assets);
  }

  function setMarketContinuousFee(bytes32 id, uint256 newContinuousFee) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    MarketState storage _marketState = marketState[id];
    require(msg.sender == feeSetter);
    require(newContinuousFee <= (uint32((uint256(10000000000000000) / uint256(31536000)))));
    require(_marketState.tickSpacing > 0);
    _marketState.continuousFee = uint32(newContinuousFee);
    emit SetMarketContinuousFee(id, newContinuousFee);
  }

  function enableLltv(uint256 lltv) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(msg.sender == configurator);
    require(lltv <= 1000000000000000000);
    isLltvEnabled[lltv] = true;
    emit EnableLltv(lltv);
  }

  function flashLoan(address[] calldata tokens, uint256[] calldata assets, address callback, bytes calldata data) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(tokens.length == assets.length);
    emit FlashLoan(msg.sender, tokens, assets, callback);
    for (uint256 i = 0; i < tokens.length; i = ((i + 1) as uint256)) {
      var __c0 = SafeTransferLib_safeTransfer(tokens[i], callback, assets[i]);
    }
    var __c1 = callback.onFlashLoan(msg.sender, tokens, assets, data);
    require(__c1 == bytes32(0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2));
    for (uint256 i = 0; i < tokens.length; i = ((i + 1) as uint256)) {
      var __c2 = SafeTransferLib_safeTransferFrom(tokens[i], callback, address(this), assets[i]);
    }
  }

  function claimableSettlementFee(address arg0) external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return claimableSettlementFee[arg0];
  }

  function totalUnits(bytes32 id) external returns (uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return marketState[id].totalUnits;
  }

  function updatePosition(Market memory market, address user) external returns (uint128, uint128, uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var id = touchMarket_body(market);
    var __c1 = _updatePosition(market, id, user);
    return (__c1.0, __c1.1, __c1.2);
  }

  function lossFactor(bytes32 id) external returns (uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return marketState[id].lossFactor;
  }

  function claimContinuousFee(Market memory market, uint256 amount, address receiver) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var id = touchMarket_body(market);
    MarketState storage _marketState = marketState[id];
    require(msg.sender == feeClaimer);
    var __c1 = UtilsLib_toUint128(amount);
    _marketState.continuousFeeCredit = ((_marketState.continuousFeeCredit - __c1) as uint128);
    var __c2 = UtilsLib_toUint128(amount);
    _marketState.totalUnits = ((_marketState.totalUnits - __c2) as uint128);
    var __c3 = UtilsLib_toUint128(amount);
    _marketState.withdrawable = ((_marketState.withdrawable - __c3) as uint128);
    emit ClaimContinuousFee(msg.sender, id, amount, receiver);
    var __c4 = SafeTransferLib_safeTransfer(market.loanToken, receiver, amount);
  }

  function isHealthy(Market memory market, bytes32 id, address borrower) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __r = isHealthy_body(market, id, borrower);
    return __r;
  }

  function setDefaultSettlementFee(address loanToken, uint256 index, uint256 newSettlementFee) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(msg.sender == feeSetter);
    require(index <= 6);
    var __c0 = maxSettlementFee(index);
    require(newSettlementFee <= __c0);
    require((newSettlementFee % 1000000000000) == 0);
    defaultSettlementFeeCbp[loanToken][index] = uint16((newSettlementFee / 1000000000000));
    emit SetDefaultSettlementFee(loanToken, index, newSettlementFee);
  }

  function isAuthorized(address arg0, address arg1) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return isAuthorized[arg0][arg1];
  }

  function take(Offer memory offer, bytes memory ratifierData, uint256 units, address taker, address receiverIfTakerIsSeller, address takerCallback, bytes memory takerCallbackData) external returns (uint256, uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require((taker == msg.sender) || isAuthorized[taker][msg.sender]);
    var id = touchMarket_body(offer.market);
    MarketState storage _marketState = marketState[id];
    require(_marketState.lossFactor < type(uint128).max);
    require((offer.maxAssets == 0) != (offer.maxUnits == 0));
    require(_marketState.continuousFee <= offer.continuousFeeCap);
    require((offer.tick % _marketState.tickSpacing) == 0);
    require(block.timestamp >= offer.start);
    require(block.timestamp <= offer.expiry);
    require(offer.maker != taker);
    require(offer.buy ? (offer.receiverIfMakerIsSeller == address(0)) : (receiverIfTakerIsSeller == address(0)));
    require(isAuthorized[offer.maker][offer.ratifier]);
    var __c1 = offer.ratifier.isRatified{view}(offer, ratifierData, taker);
    require(__c1 == bytes32(0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2));
    var offerPrice = TickLib_tickToPrice(offer.tick);
    var timeToMaturity = UtilsLib_zeroFloorSub(offer.market.maturity, block.timestamp);
    var _settlementFee = settlementFee_body(id, timeToMaturity);
    uint256 sellerPrice = offer.buy ? ((offerPrice - _settlementFee) as uint256) : offerPrice;
    uint256 buyerPrice = (sellerPrice + _settlementFee) as uint256;
    uint256 buyerAssets = 0;
    uint256 sellerAssets = 0;
    if (offer.buy) {
      var bought = UtilsLib_mulDivDown(units, buyerPrice, 1000000000000000000);
      buyerAssets = bought;
      var sold = UtilsLib_mulDivDown(units, sellerPrice, 1000000000000000000);
      sellerAssets = sold;
    } else {
      var bought = UtilsLib_mulDivUp(units, buyerPrice, 1000000000000000000);
      buyerAssets = bought;
      var sold = UtilsLib_mulDivUp(units, sellerPrice, 1000000000000000000);
      sellerAssets = sold;
    }
    uint256 newConsumed = 0;
    if (offer.maxAssets > 0) {
      newConsumed = (consumed[offer.maker][offer.group] + (offer.buy ? buyerAssets : sellerAssets)) as uint256;
      require(newConsumed <= offer.maxAssets);
    } else {
      newConsumed = (consumed[offer.maker][offer.group] + units) as uint256;
      require(newConsumed <= offer.maxUnits);
    }
    address buyer = offer.buy ? offer.maker : taker;
    address seller = offer.buy ? taker : offer.maker;
    Position storage buyerPos = position[id][buyer];
    Position storage sellerPos = position[id][seller];
    var __c9 = hasCredit(id, buyer);
    if (__c9 || (units > buyerPos.debt)) {
      var __c10 = _updatePosition(offer.market, id, buyer);
    }
    var __c11 = hasCredit(id, seller);
    if (__c11) {
      var __c12 = _updatePosition(offer.market, id, seller);
    }
    var buyerCreditIncrease = UtilsLib_zeroFloorSub(units, buyerPos.debt);
    var sellerCreditDecrease = UtilsLib_min(units, sellerPos.credit);
    uint256 sellerDebtIncrease = (units - sellerCreditDecrease) as uint256;
    var __c15 = UtilsLib_mulDivDown(buyerCreditIncrease, ((_marketState.continuousFee * timeToMaturity) as uint256), 1000000000000000000);
    var buyerPendingFeeIncrease = UtilsLib_toUint128(__c15);
    uint128 sellerPendingFeeDecrease = 0;
    if (sellerPos.credit > 0) {
      var decrease = UtilsLib_mulDivUp(sellerPos.pendingFee, sellerCreditDecrease, sellerPos.credit);
      var checkedDecrease = UtilsLib_toUint128(decrease);
      sellerPendingFeeDecrease = checkedDecrease;
    }
    require((block.timestamp <= offer.market.maturity) || (sellerDebtIncrease == 0));
    require(!(offer.reduceOnly) || (offer.buy ? (buyerCreditIncrease == 0) : (sellerDebtIncrease == 0)));
    if ((offer.market.enterGate != address(0)) && (buyerCreditIncrease != 0)) {
      var allowed = offer.market.enterGate.canIncreaseCredit{view}(buyer);
      require(allowed);
    }
    if ((offer.market.enterGate != address(0)) && (sellerDebtIncrease != 0)) {
      var allowed = offer.market.enterGate.canIncreaseDebt{view}(seller);
      require(allowed);
    }
    var __c21 = UtilsLib_toUint128(((units - buyerCreditIncrease) as uint256));
    buyerPos.debt = ((buyerPos.debt - __c21) as uint128);
    buyerPos.pendingFee = ((buyerPos.pendingFee + buyerPendingFeeIncrease) as uint128);
    var __c22 = UtilsLib_toUint128(buyerCreditIncrease);
    buyerPos.credit = ((buyerPos.credit + __c22) as uint128);
    sellerPos.pendingFee = ((sellerPos.pendingFee - sellerPendingFeeDecrease) as uint128);
    var __c23 = UtilsLib_toUint128(sellerCreditDecrease);
    sellerPos.credit = ((sellerPos.credit - __c23) as uint128);
    var __c24 = UtilsLib_toUint128(sellerDebtIncrease);
    sellerPos.debt = ((sellerPos.debt + __c24) as uint128);
    var __c25 = UtilsLib_toUint128(((((_marketState.totalUnits + buyerCreditIncrease) as uint256) - sellerCreditDecrease) as uint256));
    _marketState.totalUnits = __c25;
    claimableSettlementFee[offer.market.loanToken] = ((claimableSettlementFee[offer.market.loanToken] + ((buyerAssets - sellerAssets) as uint256)) as uint256);
    consumed[offer.maker][offer.group] = uint128(newConsumed);
    address buyerCallback = offer.buy ? offer.callback : takerCallback;
    address sellerCallback = offer.buy ? takerCallback : offer.callback;
    address payer = (buyerCallback != address(0)) ? buyerCallback : (offer.buy ? buyer : msg.sender);
    address receiver = offer.buy ? receiverIfTakerIsSeller : offer.receiverIfMakerIsSeller;
    bytes encodedOffer = abi.encodeWithSelector(encodeOffer, offer);
    emit Take(msg.sender, keccak256(encodedOffer), id, offer.buy, offer.maker, offer.group,
      offer.ratifier, ratifierData, units, taker, buyerAssets, sellerAssets, newConsumed,
      buyerPendingFeeIncrease, sellerPendingFeeDecrease,
      ((int256(buyerCreditIncrease) - int256(sellerCreditDecrease)) as int256), receiver, payer);
    var wasLocked = UtilsLib_tExchange((uint256(keccak256("morpho.midnight.liquidationLocked"))), id, seller, true);
    if (buyerCallback != address(0)) {
      bytes memory buyerCallbackData = offer.buy ? offer.callbackData : takerCallbackData;
      var __c27 = buyerCallback.onBuy(id, offer.market, buyerAssets, units, buyerPendingFeeIncrease, buyer, buyerCallbackData);
      require(__c27 == bytes32(0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2));
    }
    var __c28 = SafeTransferLib_safeTransferFrom(offer.market.loanToken, payer, address(this), ((buyerAssets - sellerAssets) as uint256));
    var __c29 = SafeTransferLib_safeTransferFrom(offer.market.loanToken, payer, receiver, sellerAssets);
    if (sellerCallback != address(0)) {
      bytes memory sellerCallbackData = offer.buy ? takerCallbackData : offer.callbackData;
      var __c30 = sellerCallback.onSell(id, offer.market, sellerAssets, units, sellerPendingFeeDecrease, seller, receiver, sellerCallbackData);
      require(__c30 == bytes32(0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2));
    }
    if (!(wasLocked)) {
      var __c31 = UtilsLib_tExchange((uint256(keccak256("morpho.midnight.liquidationLocked"))), id, seller, false);
    }
    var locked = liquidationLocked_body(id, seller);
    if (!locked) {
      var healthy = isHealthy_body(offer.market, id, seller);
      require(healthy);
    }
    return (buyerAssets, sellerAssets);
  }

  function repay(Market memory market, uint256 units, address onBehalf, address callback, bytes calldata data) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require((onBehalf == msg.sender) || isAuthorized[onBehalf][msg.sender]);
    var id = touchMarket_body(market);
    var __c1 = UtilsLib_toUint128(units);
    position[id][onBehalf].debt = ((position[id][onBehalf].debt - __c1) as uint128);
    var __c2 = UtilsLib_toUint128(units);
    marketState[id].withdrawable = ((marketState[id].withdrawable + __c2) as uint128);
    address payer = (callback != address(0)) ? callback : msg.sender;
    emit Repay(msg.sender, id, units, onBehalf, payer);
    if (callback != address(0)) {
      var __c3 = callback.onRepay(id, market, units, onBehalf, data);
      require(__c3 == bytes32(0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2));
    }
    var __c4 = SafeTransferLib_safeTransferFrom(market.loanToken, payer, address(this), units);
  }

  function withdrawable(bytes32 id) external returns (uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return marketState[id].withdrawable;
  }

  function feeClaimer() external returns (address) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return feeClaimer;
  }

  function feeSetter() external returns (address) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return feeSetter;
  }

  function lastLossFactor(bytes32 id, address user) external returns (uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return position[id][user].lastLossFactor;
  }

  function isLiquidationCursorEnabled(uint256 arg0) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return isLiquidationCursorEnabled[arg0];
  }

  function enableLiquidationCursor(uint256 liquidationCursor) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(msg.sender == configurator);
    require(liquidationCursor < 1000000000000000000);
    isLiquidationCursorEnabled[liquidationCursor] = true;
    emit EnableLiquidationCursor(liquidationCursor);
  }

  function debt(bytes32 id, address user) external returns (uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return position[id][user].debt;
  }

  function position(bytes32 arg0, address arg1) external returns (uint128, uint128, uint128, uint128, uint128, uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return (position[arg0][arg1].credit, position[arg0][arg1].pendingFee, position[arg0][arg1].lastLossFactor, position[arg0][arg1].lastAccrual, position[arg0][arg1].debt, position[arg0][arg1].collateralBitmap);
  }

  function tickSpacingSetter() external returns (address) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return tickSpacingSetter;
  }

  function setMarketSettlementFee(bytes32 id, uint256 index, uint256 newSettlementFee) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    MarketState storage _marketState = marketState[id];
    require(msg.sender == feeSetter);
    require(index <= 6);
    var __c0 = maxSettlementFee(index);
    require(newSettlementFee <= __c0);
    require((newSettlementFee % 1000000000000) == 0);
    require(_marketState.tickSpacing > 0);
    uint16 newSettlementFeeCbp = uint16((newSettlementFee / 1000000000000));
    if (index == 0) {
      _marketState.settlementFeeCbp0 = newSettlementFeeCbp;
    } else {
      if (index == 1) {
        _marketState.settlementFeeCbp1 = newSettlementFeeCbp;
      } else {
        if (index == 2) {
          _marketState.settlementFeeCbp2 = newSettlementFeeCbp;
        } else {
          if (index == 3) {
            _marketState.settlementFeeCbp3 = newSettlementFeeCbp;
          } else {
            if (index == 4) {
              _marketState.settlementFeeCbp4 = newSettlementFeeCbp;
            } else {
              if (index == 5) {
                _marketState.settlementFeeCbp5 = newSettlementFeeCbp;
              } else {
                if (index == 6) {
                  _marketState.settlementFeeCbp6 = newSettlementFeeCbp;
                }
              }
            }
          }
        }
      }
    }
    emit SetMarketSettlementFee(id, index, newSettlementFee);
  }

  function liquidate(Market calldata market, uint256 collateralIndex, uint256 seizedAssets, uint256 repaidUnits, address borrower, bool postMaturityMode, address receiver, address callback, bytes calldata data) external returns (uint256, uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var id = touchMarket_body(market);
    MarketState storage _marketState = marketState[id];
    Position storage _position = position[id][borrower];
    require((repaidUnits == 0) || (seizedAssets == 0));
    require(_position.debt > 0);
    if (market.liquidatorGate != address(0)) {
      var allowed = market.liquidatorGate.canLiquidate{view}(msg.sender);
      require(allowed);
    }
    uint256 maxDebt = 0;
    uint256 liquidatedCollatPrice = 0;
    uint256 originalDebt = _position.debt;
    uint256 badDebt = originalDebt;
    uint128 _collateralBitmap = _position.collateralBitmap;
    while (_collateralBitmap != 0) {
      var i = UtilsLib_msb(_collateralBitmap);
      CollateralParams memory _collateralParam = market.collateralParams[i];
      var price = _collateralParam.oracle.price{view}();
      if (i == collateralIndex) {
        liquidatedCollatPrice = price;
      }
      uint256 _collateral = _position.collateral[i];
      var __c4 = UtilsLib_mulDivDown(_collateral, price, (1000000000000000000000000000000000000));
      var __c5 = UtilsLib_mulDivDown(__c4, _collateralParam.lltv, 1000000000000000000);
      maxDebt = ((maxDebt + __c5) as uint256);
      var __c6 = UtilsLib_mulDivUp(_collateral, price, (1000000000000000000000000000000000000));
      var __c7 = maxLif(_collateralParam.lltv, _collateralParam.liquidationCursor);
      var __c8 = UtilsLib_mulDivUp(__c6, 1000000000000000000, __c7);
      var __c9 = UtilsLib_zeroFloorSub(badDebt, __c8);
      badDebt = __c9;
      var __c10 = UtilsLib_clearBit(_collateralBitmap, i);
      _collateralBitmap = __c10;
    }
    var __c11 = liquidationLocked_body(id, borrower);
    require(!(__c11) && (postMaturityMode ? (block.timestamp > market.maturity) : (originalDebt > maxDebt)));
    if (badDebt > 0) {
      _position.debt = ((_position.debt - uint128(badDebt)) as uint128);
      uint256 _totalUnits = _marketState.totalUnits;
      uint256 _lossFactor = _marketState.lossFactor;
      var __c12 = UtilsLib_mulDivDown(((type(uint128).max - _lossFactor) as uint256), ((_totalUnits - badDebt) as uint256), _totalUnits);
      var __c13 = UtilsLib_toUint128(((type(uint128).max - __c12) as uint256));
      _marketState.lossFactor = __c13;
      var __c14 = UtilsLib_toUint128(badDebt);
      _marketState.totalUnits = ((_marketState.totalUnits - __c14) as uint128);
      uint128 remainingFees = 0;
      if (_lossFactor < type(uint128).max) {
        var amount = UtilsLib_mulDivDown(_marketState.continuousFeeCredit,
          ((type(uint128).max - _marketState.lossFactor) as uint128),
          ((type(uint128).max - _lossFactor) as uint256));
        var checkedAmount = UtilsLib_toUint128(amount);
        remainingFees = checkedAmount;
      }
      _marketState.continuousFeeCredit = remainingFees;
    }
    if ((repaidUnits > 0) || (seizedAssets > 0)) {
      uint256 lltv = market.collateralParams[collateralIndex].lltv;
      var _maxLif = maxLif(lltv, market.collateralParams[collateralIndex].liquidationCursor);
      uint256 lif = _maxLif;
      if (postMaturityMode) {
        var grown = UtilsLib_min(_maxLif,
          ((1000000000000000000 + (((((_maxLif - 1000000000000000000) as uint256) *
            ((block.timestamp - market.maturity) as uint256)) as uint256) / 3600)) as uint256));
        lif = grown;
      }
      if (seizedAssets > 0) {
        var __c19 = UtilsLib_mulDivUp(seizedAssets, liquidatedCollatPrice, (1000000000000000000000000000000000000));
        var __c20 = UtilsLib_mulDivUp(__c19, 1000000000000000000, lif);
        repaidUnits = __c20;
      } else {
        var __c21 = UtilsLib_mulDivDown(repaidUnits, lif, 1000000000000000000);
        var __c22 = UtilsLib_mulDivDown(__c21, (1000000000000000000000000000000000000), liquidatedCollatPrice);
        seizedAssets = __c22;
      }
      if (!(postMaturityMode) && (lltv < 1000000000000000000)) {
        var maxRepaid = UtilsLib_mulDivUp(((_position.debt - maxDebt) as uint256), ((1000000000000000000 * 1000000000000000000) as uint256), ((((1000000000000000000 * 1000000000000000000) as uint256) - ((lif * lltv) as uint256)) as uint256));
        if (repaidUnits > maxRepaid) {
          var value = UtilsLib_mulDivDown(_position.collateral[collateralIndex],
            liquidatedCollatPrice, 1000000000000000000000000000000000000);
          var repayable = UtilsLib_mulDivDown(value, 1000000000000000000, lif);
          var remainder = UtilsLib_zeroFloorSub(repayable, maxRepaid);
          require(remainder < market.rcfThreshold);
        }
      }
      var __c27 = UtilsLib_toUint128(seizedAssets);
      uint128 newCollateral = (_position.collateral[collateralIndex] - __c27) as uint128;
      _position.collateral[collateralIndex] = newCollateral;
      if ((newCollateral == 0) && (seizedAssets > 0)) {
        var __c28 = UtilsLib_clearBit(_position.collateralBitmap, collateralIndex);
        _position.collateralBitmap = __c28;
      }
      var __c29 = UtilsLib_toUint128(repaidUnits);
      _marketState.withdrawable = ((_marketState.withdrawable + __c29) as uint128);
      var __c30 = UtilsLib_toUint128(repaidUnits);
      _position.debt = ((_position.debt - __c30) as uint128);
    }
    address payer = (callback != address(0)) ? callback : msg.sender;
    emit Liquidate(msg.sender, id, market.collateralParams[collateralIndex].token, seizedAssets, repaidUnits, borrower, postMaturityMode, receiver, payer, badDebt, _marketState.lossFactor, _marketState.continuousFeeCredit);
    var __c31 = SafeTransferLib_safeTransfer(market.collateralParams[collateralIndex].token, receiver, seizedAssets);
    if (callback != address(0)) {
      var __c32 = callback.onLiquidate(msg.sender, id, market, collateralIndex, seizedAssets, repaidUnits, borrower, receiver, data, badDebt);
      require(__c32 == bytes32(0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2));
    }
    var __c33 = SafeTransferLib_safeTransferFrom(market.loanToken, payer, address(this), repaidUnits);
    return (seizedAssets, repaidUnits);
  }

  function setConfigurator(address newConfigurator) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(msg.sender == configurator);
    configurator = newConfigurator;
    emit SetConfigurator(newConfigurator);
  }

  function withdrawCollateral(Market memory market, uint256 collateralIndex, uint256 assets, address onBehalf, address receiver) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require((onBehalf == msg.sender) || isAuthorized[onBehalf][msg.sender]);
    var id = touchMarket_body(market);
    address collateralToken = market.collateralParams[collateralIndex].token;
    Position storage _position = position[id][onBehalf];
    uint256 newCollateral = (_position.collateral[collateralIndex] - assets) as uint256;
    var __c1 = UtilsLib_toUint128(newCollateral);
    _position.collateral[collateralIndex] = __c1;
    if ((newCollateral == 0) && (assets > 0)) {
      var __c2 = UtilsLib_clearBit(_position.collateralBitmap, collateralIndex);
      _position.collateralBitmap = __c2;
    }
    var __c3 = isHealthy_body(market, id, onBehalf);
    require(__c3);
    emit WithdrawCollateral(msg.sender, id, collateralToken, assets, onBehalf, receiver);
    var __c4 = SafeTransferLib_safeTransfer(collateralToken, receiver, assets);
  }

  function touchMarket(Market memory market) external returns (bytes32) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __r = touchMarket_body(market);
    return __r;
  }

  function withdraw(Market memory market, uint256 units, address onBehalf, address receiver) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require((onBehalf == msg.sender) || isAuthorized[onBehalf][msg.sender]);
    var id = touchMarket_body(market);
    MarketState storage _marketState = marketState[id];
    var __c1 = _updatePosition(market, id, onBehalf);
    Position storage _position = position[id][onBehalf];
    uint128 pendingFeeDecrease = 0;
    if (_position.credit > 0) {
      var __c2 = UtilsLib_mulDivUp(_position.pendingFee, units, _position.credit);
      var __c3 = UtilsLib_toUint128(__c2);
      pendingFeeDecrease = __c3;
      _position.pendingFee = ((_position.pendingFee - pendingFeeDecrease) as uint128);
    }
    var __c4 = UtilsLib_toUint128(units);
    _position.credit = ((_position.credit - __c4) as uint128);
    var __c5 = UtilsLib_toUint128(units);
    _marketState.withdrawable = ((_marketState.withdrawable - __c5) as uint128);
    var __c6 = UtilsLib_toUint128(units);
    _marketState.totalUnits = ((_marketState.totalUnits - __c6) as uint128);
    emit Withdraw(msg.sender, id, units, onBehalf, receiver, pendingFeeDecrease);
    var __c7 = SafeTransferLib_safeTransfer(market.loanToken, receiver, units);
  }

  function settlementFee(bytes32 id, uint256 timeToMaturity) external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __r = settlementFee_body(id, timeToMaturity);
    return __r;
  }

  function multicall(bytes[] calldata calls) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    for (uint256 i = 0; i < calls.length; i = ((i + 1) as uint256)) {
      address self = address(this);
      (bool success, bytes memory returnData) = self.delegatecall(calls[i]);
      require(returnData.length <= 18446744073709551615);
      if (!(success)) {
        require(false);
      }
    }
  }

  function setFeeSetter(address newFeeSetter) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(msg.sender == configurator);
    feeSetter = newFeeSetter;
    emit SetFeeSetter(newFeeSetter);
  }

  function isLltvEnabled(uint256 arg0) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return isLltvEnabled[arg0];
  }

  function collateralBitmap(bytes32 id, address user) external returns (uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return position[id][user].collateralBitmap;
  }

  function setIsAuthorized(address authorized, bool newIsAuthorized, address onBehalf) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require((onBehalf == msg.sender) || isAuthorized[onBehalf][msg.sender]);
    isAuthorized[onBehalf][authorized] = newIsAuthorized;
    emit SetIsAuthorized(msg.sender, authorized, newIsAuthorized, onBehalf);
  }

  function continuousFee(bytes32 id) external returns (uint32) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return marketState[id].continuousFee;
  }

  function defaultSettlementFeeCbp(address arg0, uint256 arg1) external returns (uint16) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return defaultSettlementFeeCbp[arg0][arg1];
  }

  function setFeeClaimer(address newFeeClaimer) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(msg.sender == configurator);
    feeClaimer = newFeeClaimer;
    emit SetFeeClaimer(newFeeClaimer);
  }

  function pendingFee(bytes32 id, address user) external returns (uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return position[id][user].pendingFee;
  }

  function credit(bytes32 id, address user) external returns (uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return position[id][user].credit;
  }

  function updatePositionView(Market memory market, bytes32 id, address user) external returns (uint128, uint128, uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var result = updatePositionView_body(market, id, user);
    return (result.0, result.1, result.2);
  }

  function tickSpacing(bytes32 id) external returns (uint8) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return marketState[id].tickSpacing;
  }

  function lastAccrual(bytes32 id, address user) external returns (uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return position[id][user].lastAccrual;
  }

  function consumed(address arg0, bytes32 arg1) external returns (uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return consumed[arg0][arg1];
  }

  function marketState(bytes32 arg0) external returns (uint128, uint128, uint128, uint128, uint16, uint16, uint16, uint16, uint16, uint16, uint16, uint32, uint8) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return (marketState[arg0].totalUnits, marketState[arg0].lossFactor, marketState[arg0].withdrawable, marketState[arg0].continuousFeeCredit, marketState[arg0].settlementFeeCbp0, marketState[arg0].settlementFeeCbp1, marketState[arg0].settlementFeeCbp2, marketState[arg0].settlementFeeCbp3, marketState[arg0].settlementFeeCbp4, marketState[arg0].settlementFeeCbp5, marketState[arg0].settlementFeeCbp6, marketState[arg0].continuousFee, marketState[arg0].tickSpacing);
  }

  function collateral(bytes32 id, address user, uint256 index) external returns (uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return position[id][user].collateral[index];
  }

  function setConsumed(bytes32 group, uint128 amount, address onBehalf) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require((onBehalf == msg.sender) || isAuthorized[onBehalf][msg.sender]);
    require(amount >= consumed[onBehalf][group]);
    consumed[onBehalf][group] = amount;
    emit SetConsumed(msg.sender, group, amount, onBehalf);
  }

  function setMarketTickSpacing(bytes32 id, uint256 newTickSpacing) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(msg.sender == tickSpacingSetter);
    require(marketState[id].tickSpacing > 0);
    require((newTickSpacing > 0) && ((marketState[id].tickSpacing % newTickSpacing) == 0));
    marketState[id].tickSpacing = uint8(newTickSpacing);
    emit SetMarketTickSpacing(id, newTickSpacing);
  }

  function setTickSpacingSetter(address newTickSpacingSetter) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(msg.sender == configurator);
    tickSpacingSetter = newTickSpacingSetter;
    emit SetTickSpacingSetter(newTickSpacingSetter);
  }

  function toMarket(bytes32 id) external returns ((uint256, address, address, CollateralParams[], uint256, uint256, address, address)) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(marketState[id].tickSpacing > 0);
    address create2Address = address(uint160(uint256(id)));
    -- The two compiler size guards, stated only in terms of code and array lengths.
    require(create2Address.code.length <= 18446744073709550464);
    bytes code = extCodePrefix(create2Address, create2Address.code.length);
    var decoded = abi.decode(code, (Market));
    var collaterals = decoded.3;
    require((((code.length + 31) / 32) * 32) + (160 * collaterals.length) + 1408 <
      18446744073709551616);
    return decoded;
  }

  function continuousFeeCredit(bytes32 id) external returns (uint128) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return marketState[id].continuousFeeCredit;
  }

}

end Benchmarks.Midnight.Syntax
