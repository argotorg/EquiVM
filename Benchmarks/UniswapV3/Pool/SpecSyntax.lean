import Solm.Notation

/-!
# Uniswap V3 pool specification

Pinned source: v3-core e3589b192d0be27e100cd0daaf6c97204fdb1899, solc 0.7.6.
Library storage arguments are specialized to the pool's stores; position references travel as
mapping keys and are re-aliased at the point of use. FullMath uses an unbounded product with the
source's quotient-overflow guard. TickMath and UnsafeMath model their assembly arithmetic.
This specification is being checked against the runtime report and the differential suite.
-/

open Solm Solm.Notation

namespace Benchmarks.UniswapV3.Pool.Syntax

def contractSyntax : ContractDecl := solidity% contract UniswapV3Pool {
  struct Slot0 {
    uint160 sqrtPriceX96;
    int24 tick;
    uint16 observationIndex;
    uint16 observationCardinality;
    uint16 observationCardinalityNext;
    uint8 feeProtocol;
    bool unlocked;
  }

  struct ProtocolFees {
    uint128 token0;
    uint128 token1;
  }

  struct ModifyPositionParams {
    address owner;
    int24 tickLower;
    int24 tickUpper;
    int128 liquidityDelta;
  }

  struct SwapCache {
    uint8 feeProtocol;
    uint128 liquidityStart;
    uint32 blockTimestamp;
    int56 tickCumulative;
    uint160 secondsPerLiquidityCumulativeX128;
    bool computedLatestObservation;
  }

  struct SwapState {
    int256 amountSpecifiedRemaining;
    int256 amountCalculated;
    uint160 sqrtPriceX96;
    int24 tick;
    uint256 feeGrowthGlobalX128;
    uint128 protocolFee;
    uint128 liquidity;
  }

  struct StepComputations {
    uint160 sqrtPriceStartX96;
    int24 tickNext;
    bool initialized;
    uint160 sqrtPriceNextX96;
    uint256 amountIn;
    uint256 amountOut;
    uint256 feeAmount;
  }

  struct Observation {
    uint32 blockTimestamp;
    int56 tickCumulative;
    uint160 secondsPerLiquidityCumulativeX128;
    bool initialized;
  }

  struct PositionInfo {
    uint128 liquidity;
    uint256 feeGrowthInside0LastX128;
    uint256 feeGrowthInside1LastX128;
    uint128 tokensOwed0;
    uint128 tokensOwed1;
  }

  struct TickInfo {
    uint128 liquidityGross;
    int128 liquidityNet;
    uint256 feeGrowthOutside0X128;
    uint256 feeGrowthOutside1X128;
    int56 tickCumulativeOutside;
    uint160 secondsPerLiquidityOutsideX128;
    uint32 secondsOutside;
    bool initialized;
  }

  address immutable original;
  address immutable factory;
  address immutable token0;
  address immutable token1;
  uint256 immutable fee;
  uint256 immutable tickSpacing;
  uint256 immutable maxLiquidityPerTick;
  Slot0 slot0;
  uint256 feeGrowthGlobal0X128;
  uint256 feeGrowthGlobal1X128;
  ProtocolFees protocolFees;
  uint128 liquidity;
  mapping(int24 => TickInfo) ticks;
  mapping(int16 => uint256) tickBitmap;
  mapping(bytes32 => PositionInfo) positions;
  Observation[65535] observations;

  event Initialize(uint160 sqrtPriceX96, int24 tick);
  event Mint(address sender, address indexed owner, int24 indexed tickLower,
      int24 indexed tickUpper, uint128 amount, uint256 amount0, uint256 amount1);
  event Collect(address indexed owner, address recipient, int24 indexed tickLower,
      int24 indexed tickUpper, uint128 amount0, uint128 amount1);
  event Burn(address indexed owner, int24 indexed tickLower, int24 indexed tickUpper,
      uint128 amount, uint256 amount0, uint256 amount1);
  event Swap(address indexed sender, address indexed recipient, int256 amount0, int256 amount1,
      uint160 sqrtPriceX96, uint128 liquidity, int24 tick);
  event Flash(address indexed sender, address indexed recipient, uint256 amount0,
      uint256 amount1, uint256 paid0, uint256 paid1);
  event IncreaseObservationCardinalityNext(uint16 observationCardinalityNextOld,
      uint16 observationCardinalityNextNew);
  event SetFeeProtocol(uint8 feeProtocol0Old, uint8 feeProtocol1Old, uint8 feeProtocol0New,
      uint8 feeProtocol1New);
  event CollectProtocol(address indexed sender, address indexed recipient, uint128 amount0,
      uint128 amount1);

  constructor() {
    original = address(this);
    int24 _tickSpacing = 0;
    require(${Expr.extCodeSize (.env .caller)} > 0);
    (bool parameterSuccess, bytes parameterData) =
      msg.sender.staticcall(${Expr.bytesLit ⟨#[0x89, 0x03, 0x57, 0x30]⟩});
    require(parameterSuccess);
    var __c0 = ${Expr.abiDecode (.tuple [.elem .address, .elem .address, .elem .address,
      .elem (.int (.uint ⟨24, by decide⟩)), .elem (.int (.sint ⟨24, by decide⟩))])
      (.var "parameterData")};
    factory = __c0.0;
    token0 = __c0.1;
    token1 = __c0.2;
    fee = __c0.3;
    _tickSpacing = __c0.4;
    tickSpacing = uint24(_tickSpacing);
    var __c1 = Tick_tickSpacingToMaxLiquidityPerTick(_tickSpacing);
    maxLiquidityPerTick = __c1;
  }

  function factoryOwner() internal returns (address) {
    address currentFactory = factory;
    require(currentFactory.code.length > 0);
    (bool ownerSuccess, bytes ownerData) =
      currentFactory.staticcall(${Expr.bytesLit ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩});
    require(ownerSuccess);
    -- Runtime pc 8429-8438 loads and masks the address instead of validating high bits.
    return abi.decode(ownerData, (address));
  }

  function checkNotDelegateCall() internal {
    require(address(this) == original);
  }

  function checkTicks(int24 tickLower, int24 tickUpper) internal {
    require(tickLower < tickUpper);
    require(tickLower >= -887272);
    require(tickUpper <= (int24(0 - -887272)));
  }

  function _blockTimestamp() internal returns (uint32) {
    return uint32(block.timestamp);
  }

  function Oracle_observeSingle(uint32 time, uint32 secondsAgo, int24 tick, uint16 index,
      uint128 liquidity, uint16 cardinality) internal returns (int56, uint160) {
    int56 tickCumulative = 0;
    uint160 secondsPerLiquidityCumulativeX128 = 0;
    if (secondsAgo == 0) {
      Observation memory last = observations[index];
      if (last.blockTimestamp != time) {
        var __c0 = Oracle_transform(last, time, tick, liquidity);
        last = __c0;
      }
      return (last.tickCumulative, last.secondsPerLiquidityCumulativeX128);
    }
    uint32 target = uint32(time - secondsAgo);
    var __c1 = Oracle_getSurroundingObservations(time, target, tick, index, liquidity, cardinality);
    Observation beforeOrAt = __c1.0;
    Observation atOrAfter = __c1.1;
    if (target == beforeOrAt.blockTimestamp) {
      return (beforeOrAt.tickCumulative, beforeOrAt.secondsPerLiquidityCumulativeX128);
    } else {
      if (target == atOrAfter.blockTimestamp) {
        return (atOrAfter.tickCumulative, atOrAfter.secondsPerLiquidityCumulativeX128);
      } else {
        uint32 observationTimeDelta = uint32(atOrAfter.blockTimestamp - beforeOrAt.blockTimestamp);
        uint32 targetDelta = uint32(target - beforeOrAt.blockTimestamp);
        return (int56(beforeOrAt.tickCumulative + int56((sdiv((int56(atOrAfter.tickCumulative -
      beforeOrAt.tickCumulative)), observationTimeDelta)) * targetDelta)),
      uint160(beforeOrAt.secondsPerLiquidityCumulativeX128 +
      uint160(((uint256(uint256(uint160(atOrAfter.secondsPerLiquidityCumulativeX128 -
      beforeOrAt.secondsPerLiquidityCumulativeX128)) * targetDelta)) / observationTimeDelta))));
      }
    }
    return (tickCumulative, secondsPerLiquidityCumulativeX128);
  }

  function Oracle_observe(uint32 time, uint32[] memory secondsAgos, int24 tick, uint16 index,
      uint128 liquidity, uint16 cardinality) internal returns (int56[], uint160[]) {
    int56[] tickCumulatives = new int56[](0);
    uint160[] secondsPerLiquidityCumulativeX128s = new uint160[](0);
    require(cardinality > 0);
    require(secondsAgos.length <= type(uint64).max);
    tickCumulatives = new int56[](secondsAgos.length);
    require(secondsAgos.length <= type(uint64).max);
    secondsPerLiquidityCumulativeX128s = new uint160[](secondsAgos.length);
    for (uint256 i = 0; i < secondsAgos.length; i = uint256(i + 1)) {
      var __c0 = Oracle_observeSingle(time, secondsAgos[i], tick, index, liquidity, cardinality);
      tickCumulatives[i] = __c0.0;
      secondsPerLiquidityCumulativeX128s[i] = __c0.1;
    }
    return (tickCumulatives, secondsPerLiquidityCumulativeX128s);
  }

  function Oracle_grow(uint16 current, uint16 next) internal returns (uint16) {
    require(current > 0);
    if (next <= current) {
      return current;
    }
    for (uint16 i = current; i < next; i = uint16(i + 1)) {
      observations[i].blockTimestamp = 1;
    }
    return next;
  }

  function TickMath_getTickAtSqrtRatio(uint160 sqrtPriceX96) internal returns (int24) {
    int24 tick = 0;
    require((sqrtPriceX96 >= 4295128739) && (sqrtPriceX96 <
      (1461446703485210103287273052203988822378723970342)));
    uint256 ratio = uint256(sqrtPriceX96) <<[uint256] 32;
    uint256 r = ratio;
    uint256 msb = 0;
    if (r >= 2 ** 128) {
      msb = msb + 128;
      r = r >>[uint256] 128;
    }
    if (r >= 2 ** 64) {
      msb = msb + 64;
      r = r >>[uint256] 64;
    }
    if (r >= 2 ** 32) {
      msb = msb + 32;
      r = r >>[uint256] 32;
    }
    if (r >= 2 ** 16) {
      msb = msb + 16;
      r = r >>[uint256] 16;
    }
    if (r >= 2 ** 8) {
      msb = msb + 8;
      r = r >>[uint256] 8;
    }
    if (r >= 2 ** 4) {
      msb = msb + 4;
      r = r >>[uint256] 4;
    }
    if (r >= 2 ** 2) {
      msb = msb + 2;
      r = r >>[uint256] 2;
    }
    if (r >= 2 ** 1) {
      msb = msb + 1;
      r = r >>[uint256] 1;
    }
    if (msb >= 128) {
      r = ratio >>[uint256] (uint256(msb - 127));
    } else {
      r = ratio <<[uint256] (uint256(127 - msb));
    }
    int256 log_2 = (int256(int256(msb) - 128)) <<[int256] 64;
    r = uint256(r * r) >>[uint256] 127;
    var logBit63 = r >>[uint256] 128;
    log_2 = log_2 |[int256] (logBit63 <<[int256] 63);
    r = r >>[uint256] logBit63;
    r = uint256(r * r) >>[uint256] 127;
    var logBit62 = r >>[uint256] 128;
    log_2 = log_2 |[int256] (logBit62 <<[int256] 62);
    r = r >>[uint256] logBit62;
    r = uint256(r * r) >>[uint256] 127;
    var logBit61 = r >>[uint256] 128;
    log_2 = log_2 |[int256] (logBit61 <<[int256] 61);
    r = r >>[uint256] logBit61;
    r = uint256(r * r) >>[uint256] 127;
    var logBit60 = r >>[uint256] 128;
    log_2 = log_2 |[int256] (logBit60 <<[int256] 60);
    r = r >>[uint256] logBit60;
    r = uint256(r * r) >>[uint256] 127;
    var logBit59 = r >>[uint256] 128;
    log_2 = log_2 |[int256] (logBit59 <<[int256] 59);
    r = r >>[uint256] logBit59;
    r = uint256(r * r) >>[uint256] 127;
    var logBit58 = r >>[uint256] 128;
    log_2 = log_2 |[int256] (logBit58 <<[int256] 58);
    r = r >>[uint256] logBit58;
    r = uint256(r * r) >>[uint256] 127;
    var logBit57 = r >>[uint256] 128;
    log_2 = log_2 |[int256] (logBit57 <<[int256] 57);
    r = r >>[uint256] logBit57;
    r = uint256(r * r) >>[uint256] 127;
    var logBit56 = r >>[uint256] 128;
    log_2 = log_2 |[int256] (logBit56 <<[int256] 56);
    r = r >>[uint256] logBit56;
    r = uint256(r * r) >>[uint256] 127;
    var logBit55 = r >>[uint256] 128;
    log_2 = log_2 |[int256] (logBit55 <<[int256] 55);
    r = r >>[uint256] logBit55;
    r = uint256(r * r) >>[uint256] 127;
    var logBit54 = r >>[uint256] 128;
    log_2 = log_2 |[int256] (logBit54 <<[int256] 54);
    r = r >>[uint256] logBit54;
    r = uint256(r * r) >>[uint256] 127;
    var logBit53 = r >>[uint256] 128;
    log_2 = log_2 |[int256] (logBit53 <<[int256] 53);
    r = r >>[uint256] logBit53;
    r = uint256(r * r) >>[uint256] 127;
    var logBit52 = r >>[uint256] 128;
    log_2 = log_2 |[int256] (logBit52 <<[int256] 52);
    r = r >>[uint256] logBit52;
    r = uint256(r * r) >>[uint256] 127;
    var logBit51 = r >>[uint256] 128;
    log_2 = log_2 |[int256] (logBit51 <<[int256] 51);
    r = r >>[uint256] logBit51;
    r = uint256(r * r) >>[uint256] 127;
    var logBit50 = r >>[uint256] 128;
    log_2 = log_2 |[int256] (logBit50 <<[int256] 50);
    int256 log_sqrt10001 = int256(log_2 * 255738958999603826347141);
    int24 tickLow = int24(((int256(log_sqrt10001 -
      3402992956809132418596140100660247210)) >>[int256] 128));
    int24 tickHi = int24(((int256(log_sqrt10001 +
      291339464771989622907027621153398088495)) >>[int256] 128));
    var __cond1 = 0;
    if ((tickLow == tickHi)) {
      __cond1 = tickLow;
    } else {
      var __c0 = TickMath_getSqrtRatioAtTick(tickHi);
      __cond1 = ((__c0 <= sqrtPriceX96) ? tickHi : tickLow);
    }
    tick = __cond1;
    return tick;
  }

  function Oracle_initialize(uint32 time) internal returns (uint16, uint16) {
    uint16 cardinality = 0;
    uint16 cardinalityNext = 0;
    observations[0] = Observation({blockTimestamp: time, tickCumulative: 0,
      secondsPerLiquidityCumulativeX128: 0, initialized: true});
    return (1, 1);
  }

  function _modifyPosition(ModifyPositionParams memory params) internal returns (bytes32, int256,
      int256) {
    bytes32 position = bytes32(0);
    int256 amount0 = 0;
    int256 amount1 = 0;
    var __c0 = checkNotDelegateCall();
    var __c1 = checkTicks(params.tickLower, params.tickUpper);
    Slot0 memory _slot0 = slot0;
    var __c2 = _updatePosition(params.owner, params.tickLower, params.tickUpper,
      params.liquidityDelta, _slot0.tick);
    position = __c2;
    if (params.liquidityDelta != 0) {
      if (_slot0.tick < params.tickLower) {
        var __c3 = TickMath_getSqrtRatioAtTick(params.tickLower);
        var __c4 = TickMath_getSqrtRatioAtTick(params.tickUpper);
        var __c5 = SqrtPriceMath_getAmount0Delta(__c3, __c4, params.liquidityDelta);
        amount0 = __c5;
      } else {
        if (_slot0.tick < params.tickUpper) {
          uint128 liquidityBefore = liquidity;
          var __c6 = _blockTimestamp();
          var __c7 = Oracle_write(_slot0.observationIndex, __c6, _slot0.tick, liquidityBefore,
      _slot0.observationCardinality, _slot0.observationCardinalityNext);
          slot0.observationIndex = __c7.0;
          slot0.observationCardinality = __c7.1;
          var __c8 = TickMath_getSqrtRatioAtTick(params.tickUpper);
          var __c9 = SqrtPriceMath_getAmount0Delta(_slot0.sqrtPriceX96, __c8,
      params.liquidityDelta);
          amount0 = __c9;
          var __c10 = TickMath_getSqrtRatioAtTick(params.tickLower);
          var __c11 = SqrtPriceMath_getAmount1Delta(__c10, _slot0.sqrtPriceX96,
      params.liquidityDelta);
          amount1 = __c11;
          var __c12 = LiquidityMath_addDelta(liquidityBefore, params.liquidityDelta);
          liquidity = __c12;
        } else {
          var __c13 = TickMath_getSqrtRatioAtTick(params.tickLower);
          var __c14 = TickMath_getSqrtRatioAtTick(params.tickUpper);
          var __c15 = SqrtPriceMath_getAmount1Delta(__c13, __c14, params.liquidityDelta);
          amount1 = __c15;
        }
      }
    }
    return (position, amount0, amount1);
  }

  function SafeCast_toInt128(int256 y) internal returns (int128) {
    int128 z = 0;
    z = int128(y);
    require(z == y);
    return z;
  }

  function balance0() internal returns (uint256) {
    address token = token0;
    (bool success, bytes memory data) = token.staticcall(abi.encodeWithSelector(balanceOf,
      address(this)));
    require(success && (data.length >= 32));
    return abi.decode(data, (uint256));
  }

  function balance1() internal returns (uint256) {
    address token = token1;
    (bool success, bytes memory data) = token.staticcall(abi.encodeWithSelector(balanceOf,
      address(this)));
    require(success && (data.length >= 32));
    return abi.decode(data, (uint256));
  }

  function LowGasSafeMath_add(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = 0;
    z = uint256(x + y);
    require(z >= x);
    return z;
  }

  function Position_get(address owner, int24 tickLower,
      int24 tickUpper) internal returns (bytes32) {
    return keccak256(abi.encodePacked(address(owner), int24(tickLower), int24(tickUpper)));
  }

  function TransferHelper_safeTransfer(address token, address «to», uint256 value) internal {
    (bool success, bytes memory data) = token.call(abi.encodeWithSelector(transfer, «to», value));
    require(success && ((data.length == 0) || abi.decode(data, (bool))));
  }

  function TickBitmap_nextInitializedTickWithinOneWord(int24 tick, int24 tickSpacing,
      bool lte) internal returns (int24, bool) {
    int24 next = 0;
    bool initialized = false;
    int24 compressed = sdiv(tick, tickSpacing);
    if ((tick < 0) && (srem(tick, tickSpacing) != 0)) {
      compressed = int24(compressed - 1);
    }
    if (lte) {
      var __c0 = TickBitmap_position(compressed);
      int16 wordPos = __c0.0;
      uint8 bitPos = __c0.1;
      uint256 mask = uint256(uint256((1 <<[uint256] bitPos) - 1) + (1 <<[uint256] bitPos));
      uint256 masked = tickBitmap[wordPos] &[uint256] mask;
      initialized = masked != 0;
      var __cond2 = 0;
      if (initialized) {
        var __c1 = BitMath_mostSignificantBit(masked);
        __cond2 = int24((int24(compressed - int24(uint8(bitPos - __c1)))) * tickSpacing);
      } else {
        __cond2 = int24((int24(compressed - int24(bitPos))) * tickSpacing);
      }
      next = __cond2;
    } else {
      var __c3 = TickBitmap_position(int24(compressed + 1));
      int16 wordPos = __c3.0;
      uint8 bitPos = __c3.1;
      uint256 mask = ~[uint256] (uint256((1 <<[uint256] bitPos) - 1));
      uint256 masked = tickBitmap[wordPos] &[uint256] mask;
      initialized = masked != 0;
      var __cond5 = 0;
      if (initialized) {
        var __c4 = BitMath_leastSignificantBit(masked);
        __cond5 = int24((int24(int24(compressed + 1) + int24(uint8(__c4 - bitPos)))) * tickSpacing);
      } else {
        __cond5 = int24((int24(int24(compressed + 1) + int24(uint8(type(uint8).max - bitPos)))) *
      tickSpacing);
      }
      next = __cond5;
    }
    return (next, initialized);
  }

  function TickMath_getSqrtRatioAtTick(int24 tick) internal returns (uint160) {
    uint160 sqrtPriceX96 = 0;
    uint256 absTick = (tick < 0) ? uint256(int256(0 - int256(tick))) : uint256(int256(tick));
    require(absTick <= uint256((int24(0 - -887272))));
    uint256 ratio = ((absTick &[uint256] 1) != 0) ? 340265354078544963557816517032075149313 :
      340282366920938463463374607431768211456;
    if ((absTick &[uint256] 2) != 0) {
      ratio = (uint256(ratio * 340248342086729790484326174814286782778)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 4) != 0) {
      ratio = (uint256(ratio * 340214320654664324051920982716015181260)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 8) != 0) {
      ratio = (uint256(ratio * 340146287995602323631171512101879684304)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 16) != 0) {
      ratio = (uint256(ratio * 340010263488231146823593991679159461444)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 32) != 0) {
      ratio = (uint256(ratio * 339738377640345403697157401104375502016)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 64) != 0) {
      ratio = (uint256(ratio * 339195258003219555707034227454543997025)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 128) != 0) {
      ratio = (uint256(ratio * 338111622100601834656805679988414885971)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 256) != 0) {
      ratio = (uint256(ratio * 335954724994790223023589805789778977700)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 512) != 0) {
      ratio = (uint256(ratio * 331682121138379247127172139078559817300)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 1024) != 0) {
      ratio = (uint256(ratio * 323299236684853023288211250268160618739)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 2048) != 0) {
      ratio = (uint256(ratio * 307163716377032989948697243942600083929)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 4096) != 0) {
      ratio = (uint256(ratio * 277268403626896220162999269216087595045)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 8192) != 0) {
      ratio = (uint256(ratio * 225923453940442621947126027127485391333)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 16384) != 0) {
      ratio = (uint256(ratio * 149997214084966997727330242082538205943)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 32768) != 0) {
      ratio = (uint256(ratio * 66119101136024775622716233608466517926)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 65536) != 0) {
      ratio = (uint256(ratio * 12847376061809297530290974190478138313)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 131072) != 0) {
      ratio = (uint256(ratio * 485053260817066172746253684029974020)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 262144) != 0) {
      ratio = (uint256(ratio * 691415978906521570653435304214168)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 524288) != 0) {
      ratio = (uint256(ratio * 1404880482679654955896180642)) >>[uint256] 128;
    }
    if (tick > 0) {
      ratio = type(uint256).max / ratio;
    }
    sqrtPriceX96 = uint160(uint256((ratio >>[uint256] 32) + (((ratio % 4294967296) == 0) ? 0 : 1)));
    return sqrtPriceX96;
  }

  function SwapMath_computeSwapStep(uint160 sqrtRatioCurrentX96, uint160 sqrtRatioTargetX96,
      uint128 liquidity, int256 amountRemaining, uint24 feePips) internal returns (uint160,
      uint256, uint256, uint256) {
    uint160 sqrtRatioNextX96 = 0;
    uint256 amountIn = 0;
    uint256 amountOut = 0;
    uint256 feeAmount = 0;
    bool zeroForOne = sqrtRatioCurrentX96 >= sqrtRatioTargetX96;
    bool exactIn = amountRemaining >= 0;
    if (exactIn) {
      var amountRemainingLessFee = FullMath_mulDiv(uint256(amountRemaining), uint24(1000000 -
      feePips), 1000000);
      var __cond3 = 0;
      if (zeroForOne) {
        var __c1 = SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool(sqrtRatioTargetX96,
      sqrtRatioCurrentX96, liquidity, true);
        __cond3 = __c1;
      } else {
        var __c2 =
      SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool(sqrtRatioCurrentX96,
      sqrtRatioTargetX96, liquidity, true);
        __cond3 = __c2;
      }
      amountIn = __cond3;
      if (amountRemainingLessFee >= amountIn) {
        sqrtRatioNextX96 = sqrtRatioTargetX96;
      } else {
        var __c4 = SqrtPriceMath_getNextSqrtPriceFromInput(sqrtRatioCurrentX96, liquidity,
      amountRemainingLessFee, zeroForOne);
        sqrtRatioNextX96 = __c4;
      }
    } else {
      var __cond7 = 0;
      if (zeroForOne) {
        var __c5 = SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool(sqrtRatioTargetX96,
      sqrtRatioCurrentX96, liquidity, false);
        __cond7 = __c5;
      } else {
        var __c6 =
      SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool(sqrtRatioCurrentX96,
      sqrtRatioTargetX96, liquidity, false);
        __cond7 = __c6;
      }
      amountOut = __cond7;
      if (uint256(int256(0 - amountRemaining)) >= amountOut) {
        sqrtRatioNextX96 = sqrtRatioTargetX96;
      } else {
        var __c8 = SqrtPriceMath_getNextSqrtPriceFromOutput(sqrtRatioCurrentX96, liquidity,
      uint256(int256(0 - amountRemaining)), zeroForOne);
        sqrtRatioNextX96 = __c8;
      }
    }
    bool max = sqrtRatioTargetX96 == sqrtRatioNextX96;
    if (zeroForOne) {
      var __cond10 = 0;
      if ((max && exactIn)) {
        __cond10 = amountIn;
      } else {
        var __c9 = SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool(sqrtRatioNextX96,
      sqrtRatioCurrentX96, liquidity, true);
        __cond10 = __c9;
      }
      amountIn = __cond10;
      var __cond12 = 0;
      if ((max && !(exactIn))) {
        __cond12 = amountOut;
      } else {
        var __c11 = SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool(sqrtRatioNextX96,
      sqrtRatioCurrentX96, liquidity, false);
        __cond12 = __c11;
      }
      amountOut = __cond12;
    } else {
      var __cond14 = 0;
      if ((max && exactIn)) {
        __cond14 = amountIn;
      } else {
        var __c13 =
      SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool(sqrtRatioCurrentX96,
      sqrtRatioNextX96, liquidity, true);
        __cond14 = __c13;
      }
      amountIn = __cond14;
      var __cond16 = 0;
      if ((max && !(exactIn))) {
        __cond16 = amountOut;
      } else {
        var __c15 =
      SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool(sqrtRatioCurrentX96,
      sqrtRatioNextX96, liquidity, false);
        __cond16 = __c15;
      }
      amountOut = __cond16;
    }
    if (!(exactIn) && (amountOut > uint256(int256(0 - amountRemaining)))) {
      amountOut = uint256(int256(0 - amountRemaining));
    }
    if (exactIn && (sqrtRatioNextX96 != sqrtRatioTargetX96)) {
      feeAmount = uint256(uint256(amountRemaining) - amountIn);
    } else {
      var __c17 = FullMath_mulDivRoundingUp(amountIn, feePips, uint24(1000000 - feePips));
      feeAmount = __c17;
    }
    return (sqrtRatioNextX96, amountIn, amountOut, feeAmount);
  }

  function SafeCast_toInt256(uint256 y) internal returns (int256) {
    int256 z = 0;
    require(y < uint256(2 ** 255));
    z = int256(y);
    return z;
  }

  function LowGasSafeMath_sub(int256 x, int256 y) internal returns (int256) {
    int256 z = 0;
    z = int256(x - y);
    require((z <= x) == (y >= 0));
    return z;
  }

  function LowGasSafeMath_add_int256_int256(int256 x, int256 y) internal returns (int256) {
    int256 z = 0;
    z = int256(x + y);
    require((z >= x) == (y >= 0));
    return z;
  }

  function FullMath_mulDiv(uint256 a, uint256 b, uint256 denominator) internal returns (uint256) {
    -- Exact 512-bit product; the source requires its high limb to be below the denominator.
    var product = a * b;
    require(denominator > product / (2 ** 256));
    return product / denominator;
  }

  function Tick_cross(int24 tick, uint256 feeGrowthGlobal0X128, uint256 feeGrowthGlobal1X128,
      uint160 secondsPerLiquidityCumulativeX128, int56 tickCumulative,
      uint32 time) internal returns (int128) {
    int128 liquidityNet = 0;
    TickInfo storage info = ticks[tick];
    info.feeGrowthOutside0X128 = uint256(feeGrowthGlobal0X128 - info.feeGrowthOutside0X128);
    info.feeGrowthOutside1X128 = uint256(feeGrowthGlobal1X128 - info.feeGrowthOutside1X128);
    info.secondsPerLiquidityOutsideX128 = uint160(secondsPerLiquidityCumulativeX128 -
      info.secondsPerLiquidityOutsideX128);
    info.tickCumulativeOutside = int56(tickCumulative - info.tickCumulativeOutside);
    info.secondsOutside = uint32(time - info.secondsOutside);
    liquidityNet = info.liquidityNet;
    return liquidityNet;
  }

  function LiquidityMath_addDelta(uint128 x, int128 y) internal returns (uint128) {
    uint128 z = 0;
    if (y < 0) {
      z = uint128(x - uint128(int128(0 - y)));
      require(z < x);
    } else {
      z = uint128(x + uint128(y));
      require(z >= x);
    }
    return z;
  }

  function Oracle_write(uint16 index, uint32 blockTimestamp, int24 tick, uint128 liquidity,
      uint16 cardinality, uint16 cardinalityNext) internal returns (uint16, uint16) {
    uint16 indexUpdated = 0;
    uint16 cardinalityUpdated = 0;
    Observation memory last = observations[index];
    if (last.blockTimestamp == blockTimestamp) {
      return (index, cardinality);
    }
    if ((cardinalityNext > cardinality) && (index == (uint16(cardinality - 1)))) {
      cardinalityUpdated = cardinalityNext;
    } else {
      cardinalityUpdated = cardinality;
    }
    indexUpdated = (uint16(index + 1)) % cardinalityUpdated;
    var __c0 = Oracle_transform(last, blockTimestamp, tick, liquidity);
    observations[indexUpdated] = __c0;
    return (indexUpdated, cardinalityUpdated);
  }

  function FullMath_mulDivRoundingUp(uint256 a, uint256 b,
      uint256 denominator) internal returns (uint256) {
    uint256 result = 0;
    var __c0 = FullMath_mulDiv(a, b, denominator);
    result = __c0;
    if (((a * b) % denominator) > 0) {
      require(result < type(uint256).max);
      result = uint256(result + 1);
    }
    return result;
  }

  function Tick_tickSpacingToMaxLiquidityPerTick(int24 tickSpacing) internal returns (uint128) {
    int24 minTick = int24((sdiv(-887272, tickSpacing)) * tickSpacing);
    int24 maxTick = int24((sdiv((int24(0 - -887272)), tickSpacing)) * tickSpacing);
    uint24 numTicks = uint24(uint24(sdiv((int24(maxTick - minTick)), tickSpacing)) + 1);
    return type(uint128).max / numTicks;
  }

  function Oracle_transform(Observation memory last, uint32 blockTimestamp, int24 tick,
      uint128 liquidity) internal returns (Observation) {
    uint32 delta = uint32(blockTimestamp - last.blockTimestamp);
    return Observation({blockTimestamp: blockTimestamp,
      tickCumulative: int56(last.tickCumulative + int56(int56(tick) * delta)),
      secondsPerLiquidityCumulativeX128: uint160(last.secondsPerLiquidityCumulativeX128 +
      ((uint160(delta) <<[uint160] 128) / ((liquidity > 0) ? liquidity : 1))), initialized: true});
  }

  function Oracle_getSurroundingObservations(uint32 time, uint32 target, int24 tick,
      uint16 index, uint128 liquidity, uint16 cardinality) internal returns (Observation,
      Observation) {
    Observation beforeOrAt = Observation({blockTimestamp: 0, tickCumulative: 0,
      secondsPerLiquidityCumulativeX128: 0, initialized: false});
    Observation atOrAfter = Observation({blockTimestamp: 0, tickCumulative: 0,
      secondsPerLiquidityCumulativeX128: 0, initialized: false});
    beforeOrAt = observations[index];
    var __c0 = Oracle_lte(time, beforeOrAt.blockTimestamp, target);
    if (__c0) {
      if (beforeOrAt.blockTimestamp == target) {
        return (beforeOrAt, atOrAfter);
      } else {
        var __c1 = Oracle_transform(beforeOrAt, target, tick, liquidity);
        return (beforeOrAt, __c1);
      }
    }
    beforeOrAt = observations[((uint16(index + 1)) % cardinality)];
    if (!(beforeOrAt.initialized)) {
      beforeOrAt = observations[0];
    }
    var __c2 = Oracle_lte(time, beforeOrAt.blockTimestamp, target);
    require(__c2);
    var __c3 = Oracle_binarySearch(time, target, index, cardinality);
    return (__c3.0, __c3.1);
  }

  function _updatePosition(address owner, int24 tickLower, int24 tickUpper,
      int128 liquidityDelta, int24 tick) internal returns (bytes32) {
    bytes32 position = bytes32(0);
    var __c0 = Position_get(owner, tickLower, tickUpper);
    position = __c0;
    uint256 _feeGrowthGlobal0X128 = feeGrowthGlobal0X128;
    uint256 _feeGrowthGlobal1X128 = feeGrowthGlobal1X128;
    bool flippedLower = false;
    bool flippedUpper = false;
    if (liquidityDelta != 0) {
      var time = _blockTimestamp();
      var __c2 = Oracle_observeSingle(time, 0, slot0.tick, slot0.observationIndex, liquidity,
      slot0.observationCardinality);
      int56 tickCumulative = __c2.0;
      uint160 secondsPerLiquidityCumulativeX128 = __c2.1;
      var __c3 = Tick_update(tickLower, tick, liquidityDelta, _feeGrowthGlobal0X128,
      _feeGrowthGlobal1X128, secondsPerLiquidityCumulativeX128, tickCumulative, time, false,
      uint128(maxLiquidityPerTick));
      flippedLower = __c3;
      var __c4 = Tick_update(tickUpper, tick, liquidityDelta, _feeGrowthGlobal0X128,
      _feeGrowthGlobal1X128, secondsPerLiquidityCumulativeX128, tickCumulative, time, true,
      uint128(maxLiquidityPerTick));
      flippedUpper = __c4;
      if (flippedLower) {
        var __c5 = TickBitmap_flipTick(tickLower, int24(tickSpacing));
      }
      if (flippedUpper) {
        var __c6 = TickBitmap_flipTick(tickUpper, int24(tickSpacing));
      }
    }
    var __c7 = Tick_getFeeGrowthInside(tickLower, tickUpper, tick, _feeGrowthGlobal0X128,
      _feeGrowthGlobal1X128);
    uint256 feeGrowthInside0X128 = __c7.0;
    uint256 feeGrowthInside1X128 = __c7.1;
    var __c8 = Position_update(position, liquidityDelta, feeGrowthInside0X128,
      feeGrowthInside1X128);
    if (liquidityDelta < 0) {
      if (flippedLower) {
        var __c9 = Tick_clear(tickLower);
      }
      if (flippedUpper) {
        var __c10 = Tick_clear(tickUpper);
      }
    }
    return position;
  }

  function SqrtPriceMath_getAmount0Delta(uint160 sqrtRatioAX96, uint160 sqrtRatioBX96,
      int128 liquidity) internal returns (int256) {
    int256 amount0 = 0;
    var __cond4 = 0;
    if ((liquidity < 0)) {
      var __c0 = SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool(sqrtRatioAX96,
      sqrtRatioBX96, uint128(int128(0 - liquidity)), false);
      var __c1 = SafeCast_toInt256(__c0);
      __cond4 = int256(0 - __c1);
    } else {
      var __c2 = SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool(sqrtRatioAX96,
      sqrtRatioBX96, uint128(liquidity), true);
      var __c3 = SafeCast_toInt256(__c2);
      __cond4 = __c3;
    }
    return __cond4;
  }

  function SqrtPriceMath_getAmount1Delta(uint160 sqrtRatioAX96, uint160 sqrtRatioBX96,
      int128 liquidity) internal returns (int256) {
    int256 amount1 = 0;
    var __cond4 = 0;
    if ((liquidity < 0)) {
      var __c0 = SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool(sqrtRatioAX96,
      sqrtRatioBX96, uint128(int128(0 - liquidity)), false);
      var __c1 = SafeCast_toInt256(__c0);
      __cond4 = int256(0 - __c1);
    } else {
      var __c2 = SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool(sqrtRatioAX96,
      sqrtRatioBX96, uint128(liquidity), true);
      var __c3 = SafeCast_toInt256(__c2);
      __cond4 = __c3;
    }
    return __cond4;
  }

  function TickBitmap_position(int24 tick) internal returns (int16, uint8) {
    int16 wordPos = 0;
    uint8 bitPos = 0;
    wordPos = int16((tick >>[int24] 8));
    bitPos = uint8(srem(tick, 256));
    return (wordPos, bitPos);
  }

  function BitMath_mostSignificantBit(uint256 x) internal returns (uint8) {
    uint8 r = 0;
    require(x > 0);
    if (x >= 340282366920938463463374607431768211456) {
      x = (x >>[uint256] 128);
      r = uint8(r + 128);
    }
    if (x >= 18446744073709551616) {
      x = (x >>[uint256] 64);
      r = uint8(r + 64);
    }
    if (x >= 4294967296) {
      x = (x >>[uint256] 32);
      r = uint8(r + 32);
    }
    if (x >= 65536) {
      x = (x >>[uint256] 16);
      r = uint8(r + 16);
    }
    if (x >= 256) {
      x = (x >>[uint256] 8);
      r = uint8(r + 8);
    }
    if (x >= 16) {
      x = (x >>[uint256] 4);
      r = uint8(r + 4);
    }
    if (x >= 4) {
      x = (x >>[uint256] 2);
      r = uint8(r + 2);
    }
    if (x >= 2) {
      r = uint8(r + 1);
    }
    return r;
  }

  function BitMath_leastSignificantBit(uint256 x) internal returns (uint8) {
    uint8 r = 0;
    require(x > 0);
    r = 255;
    if ((x &[uint256] type(uint128).max) > 0) {
      r = uint8(r - 128);
    } else {
      x = (x >>[uint256] 128);
    }
    if ((x &[uint256] type(uint64).max) > 0) {
      r = uint8(r - 64);
    } else {
      x = (x >>[uint256] 64);
    }
    if ((x &[uint256] type(uint32).max) > 0) {
      r = uint8(r - 32);
    } else {
      x = (x >>[uint256] 32);
    }
    if ((x &[uint256] type(uint16).max) > 0) {
      r = uint8(r - 16);
    } else {
      x = (x >>[uint256] 16);
    }
    if ((x &[uint256] type(uint8).max) > 0) {
      r = uint8(r - 8);
    } else {
      x = (x >>[uint256] 8);
    }
    if ((x &[uint256] 15) > 0) {
      r = uint8(r - 4);
    } else {
      x = (x >>[uint256] 4);
    }
    if ((x &[uint256] 3) > 0) {
      r = uint8(r - 2);
    } else {
      x = (x >>[uint256] 2);
    }
    if ((x &[uint256] 1) > 0) {
      r = uint8(r - 1);
    }
    return r;
  }

  function SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool(uint160 sqrtRatioAX96,
      uint160 sqrtRatioBX96, uint128 liquidity, bool roundUp) internal returns (uint256) {
    uint256 amount0 = 0;
    if (sqrtRatioAX96 > sqrtRatioBX96) {
      var __t0 = sqrtRatioBX96;
      var __t1 = sqrtRatioAX96;
      sqrtRatioAX96 = __t0;
      sqrtRatioBX96 = __t1;
    }
    uint256 numerator1 = uint256(liquidity) <<[uint256] 96;
    uint256 numerator2 = uint160(sqrtRatioBX96 - sqrtRatioAX96);
    require(sqrtRatioAX96 > 0);
    var __cond5 = 0;
    if (roundUp) {
      var __c2 = FullMath_mulDivRoundingUp(numerator1, numerator2, sqrtRatioBX96);
      var __c3 = UnsafeMath_divRoundingUp(__c2, sqrtRatioAX96);
      __cond5 = __c3;
    } else {
      var __c4 = FullMath_mulDiv(numerator1, numerator2, sqrtRatioBX96);
      __cond5 = (__c4 / sqrtRatioAX96);
    }
    return __cond5;
  }

  function SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool(uint160 sqrtRatioAX96,
      uint160 sqrtRatioBX96, uint128 liquidity, bool roundUp) internal returns (uint256) {
    uint256 amount1 = 0;
    if (sqrtRatioAX96 > sqrtRatioBX96) {
      var __t0 = sqrtRatioBX96;
      var __t1 = sqrtRatioAX96;
      sqrtRatioAX96 = __t0;
      sqrtRatioBX96 = __t1;
    }
    var __cond4 = 0;
    if (roundUp) {
      var __c2 = FullMath_mulDivRoundingUp(liquidity, uint160(sqrtRatioBX96 - sqrtRatioAX96),
      79228162514264337593543950336);
      __cond4 = __c2;
    } else {
      var __c3 = FullMath_mulDiv(liquidity, uint160(sqrtRatioBX96 - sqrtRatioAX96),
      79228162514264337593543950336);
      __cond4 = __c3;
    }
    return __cond4;
  }

  function SqrtPriceMath_getNextSqrtPriceFromInput(uint160 sqrtPX96, uint128 liquidity,
      uint256 amountIn, bool zeroForOne) internal returns (uint160) {
    uint160 sqrtQX96 = 0;
    require(sqrtPX96 > 0);
    require(liquidity > 0);
    var __cond2 = 0;
    if (zeroForOne) {
      var __c0 = SqrtPriceMath_getNextSqrtPriceFromAmount0RoundingUp(sqrtPX96, liquidity,
      amountIn, true);
      __cond2 = __c0;
    } else {
      var __c1 = SqrtPriceMath_getNextSqrtPriceFromAmount1RoundingDown(sqrtPX96, liquidity,
      amountIn, true);
      __cond2 = __c1;
    }
    return __cond2;
  }

  function SqrtPriceMath_getNextSqrtPriceFromOutput(uint160 sqrtPX96, uint128 liquidity,
      uint256 amountOut, bool zeroForOne) internal returns (uint160) {
    uint160 sqrtQX96 = 0;
    require(sqrtPX96 > 0);
    require(liquidity > 0);
    var __cond2 = 0;
    if (zeroForOne) {
      var __c0 = SqrtPriceMath_getNextSqrtPriceFromAmount1RoundingDown(sqrtPX96, liquidity,
      amountOut, false);
      __cond2 = __c0;
    } else {
      var __c1 = SqrtPriceMath_getNextSqrtPriceFromAmount0RoundingUp(sqrtPX96, liquidity,
      amountOut, false);
      __cond2 = __c1;
    }
    return __cond2;
  }

  function Oracle_lte(uint32 time, uint32 a, uint32 b) internal returns (bool) {
    if ((a <= time) && (b <= time)) {
      return a <= b;
    }
    uint256 aAdjusted = (a > time) ? a : uint40(a + 4294967296);
    uint256 bAdjusted = (b > time) ? b : uint40(b + 4294967296);
    return aAdjusted <= bAdjusted;
  }

  function Oracle_binarySearch(uint32 time, uint32 target, uint16 index,
      uint16 cardinality) internal returns (Observation, Observation) {
    Observation beforeOrAt = Observation({blockTimestamp: 0, tickCumulative: 0,
      secondsPerLiquidityCumulativeX128: 0, initialized: false});
    Observation atOrAfter = Observation({blockTimestamp: 0, tickCumulative: 0,
      secondsPerLiquidityCumulativeX128: 0, initialized: false});
    uint256 l = (uint16(index + 1)) % cardinality;
    uint256 r = uint256(uint256(l + cardinality) - 1);
    uint256 i = 0;
    while (true) {
      i = (uint256(l + r)) / 2;
      beforeOrAt = observations[(i % cardinality)];
      if (!(beforeOrAt.initialized)) {
        l = uint256(i + 1);
        continue;
      }
      atOrAfter = observations[((uint256(i + 1)) % cardinality)];
      var targetAtOrAfter = Oracle_lte(time, beforeOrAt.blockTimestamp, target);
      bool targetBeforeOrAt = false;
      if (targetAtOrAfter) {
        var __c1 = Oracle_lte(time, target, atOrAfter.blockTimestamp);
        targetBeforeOrAt = __c1;
      }
      if (targetBeforeOrAt) {
        break;
      }
      if (!(targetAtOrAfter)) {
        r = uint256(i - 1);
      } else {
        l = uint256(i + 1);
      }
    }
    return (beforeOrAt, atOrAfter);
  }

  function Tick_update(int24 tick, int24 tickCurrent, int128 liquidityDelta,
      uint256 feeGrowthGlobal0X128, uint256 feeGrowthGlobal1X128,
      uint160 secondsPerLiquidityCumulativeX128, int56 tickCumulative, uint32 time, bool upper,
      uint128 maxLiquidity) internal returns (bool) {
    bool flipped = false;
    TickInfo storage info = ticks[tick];
    uint128 liquidityGrossBefore = info.liquidityGross;
    var liquidityGrossAfter = LiquidityMath_addDelta(liquidityGrossBefore, liquidityDelta);
    require(liquidityGrossAfter <= maxLiquidity);
    flipped = (liquidityGrossAfter == 0) != (liquidityGrossBefore == 0);
    if (liquidityGrossBefore == 0) {
      if (tick <= tickCurrent) {
        info.feeGrowthOutside0X128 = feeGrowthGlobal0X128;
        info.feeGrowthOutside1X128 = feeGrowthGlobal1X128;
        info.secondsPerLiquidityOutsideX128 = secondsPerLiquidityCumulativeX128;
        info.tickCumulativeOutside = tickCumulative;
        info.secondsOutside = time;
      }
      info.initialized = true;
    }
    info.liquidityGross = liquidityGrossAfter;
    var __cond5 = 0;
    if (upper) {
      var __c1 = LowGasSafeMath_sub(int256(info.liquidityNet), liquidityDelta);
      var __c2 = SafeCast_toInt128(__c1);
      __cond5 = __c2;
    } else {
      var __c3 = LowGasSafeMath_add_int256_int256(int256(info.liquidityNet), liquidityDelta);
      var __c4 = SafeCast_toInt128(__c3);
      __cond5 = __c4;
    }
    info.liquidityNet = __cond5;
    return flipped;
  }

  function TickBitmap_flipTick(int24 tick, int24 tickSpacing) internal {
    require(srem(tick, tickSpacing) == 0);
    var __c0 = TickBitmap_position(sdiv(tick, tickSpacing));
    int16 wordPos = __c0.0;
    uint8 bitPos = __c0.1;
    uint256 mask = 1 <<[uint256] bitPos;
    tickBitmap[wordPos] = (tickBitmap[wordPos] ^[uint256] mask);
  }

  function Tick_getFeeGrowthInside(int24 tickLower, int24 tickUpper, int24 tickCurrent,
      uint256 feeGrowthGlobal0X128, uint256 feeGrowthGlobal1X128) internal returns (uint256,
      uint256) {
    uint256 feeGrowthInside0X128 = 0;
    uint256 feeGrowthInside1X128 = 0;
    TickInfo storage lower = ticks[tickLower];
    TickInfo storage upper = ticks[tickUpper];
    uint256 feeGrowthBelow0X128 = 0;
    uint256 feeGrowthBelow1X128 = 0;
    if (tickCurrent >= tickLower) {
      feeGrowthBelow0X128 = lower.feeGrowthOutside0X128;
      feeGrowthBelow1X128 = lower.feeGrowthOutside1X128;
    } else {
      feeGrowthBelow0X128 = uint256(feeGrowthGlobal0X128 - lower.feeGrowthOutside0X128);
      feeGrowthBelow1X128 = uint256(feeGrowthGlobal1X128 - lower.feeGrowthOutside1X128);
    }
    uint256 feeGrowthAbove0X128 = 0;
    uint256 feeGrowthAbove1X128 = 0;
    if (tickCurrent < tickUpper) {
      feeGrowthAbove0X128 = upper.feeGrowthOutside0X128;
      feeGrowthAbove1X128 = upper.feeGrowthOutside1X128;
    } else {
      feeGrowthAbove0X128 = uint256(feeGrowthGlobal0X128 - upper.feeGrowthOutside0X128);
      feeGrowthAbove1X128 = uint256(feeGrowthGlobal1X128 - upper.feeGrowthOutside1X128);
    }
    feeGrowthInside0X128 = uint256(uint256(feeGrowthGlobal0X128 - feeGrowthBelow0X128) -
      feeGrowthAbove0X128);
    feeGrowthInside1X128 = uint256(uint256(feeGrowthGlobal1X128 - feeGrowthBelow1X128) -
      feeGrowthAbove1X128);
    return (feeGrowthInside0X128, feeGrowthInside1X128);
  }

  function Position_update(bytes32 key, int128 liquidityDelta, uint256 feeGrowthInside0X128,
      uint256 feeGrowthInside1X128) internal {
    PositionInfo storage self = positions[key];
    PositionInfo memory _self = self;
    uint128 liquidityNext = 0;
    if (liquidityDelta == 0) {
      require(_self.liquidity > 0);
      liquidityNext = _self.liquidity;
    } else {
      var __c0 = LiquidityMath_addDelta(_self.liquidity, liquidityDelta);
      liquidityNext = __c0;
    }
    var __c1 = FullMath_mulDiv(uint256(feeGrowthInside0X128 - _self.feeGrowthInside0LastX128),
      _self.liquidity, (340282366920938463463374607431768211456));
    uint128 tokensOwed0 = uint128(__c1);
    var __c2 = FullMath_mulDiv(uint256(feeGrowthInside1X128 - _self.feeGrowthInside1LastX128),
      _self.liquidity, (340282366920938463463374607431768211456));
    uint128 tokensOwed1 = uint128(__c2);
    if (liquidityDelta != 0) {
      self.liquidity = liquidityNext;
    }
    self.feeGrowthInside0LastX128 = feeGrowthInside0X128;
    self.feeGrowthInside1LastX128 = feeGrowthInside1X128;
    if ((tokensOwed0 > 0) || (tokensOwed1 > 0)) {
      self.tokensOwed0 = uint128(self.tokensOwed0 + tokensOwed0);
      self.tokensOwed1 = uint128(self.tokensOwed1 + tokensOwed1);
    }
  }

  function Tick_clear(int24 tick) internal {
    delete ticks[tick];
  }

  function UnsafeMath_divRoundingUp(uint256 x, uint256 y) internal returns (uint256) {
    -- Yul DIV and MOD return zero for a zero divisor.
    if (y == 0) { return 0; }
    return (x / y) + ((x % y == 0) ? 0 : 1);
  }

  function SqrtPriceMath_getNextSqrtPriceFromAmount0RoundingUp(uint160 sqrtPX96,
      uint128 liquidity, uint256 amount, bool add) internal returns (uint160) {
    if (amount == 0) {
      return sqrtPX96;
    }
    uint256 numerator1 = uint256(liquidity) <<[uint256] 96;
    if (add) {
      uint256 product = 0;
      product = uint256(amount * sqrtPX96);
      if ((product / amount) == sqrtPX96) {
        uint256 denominator = uint256(numerator1 + product);
        if (denominator >= numerator1) {
          var __c0 = FullMath_mulDivRoundingUp(numerator1, sqrtPX96, denominator);
          return uint160(__c0);
        }
      }
      var __c1 = LowGasSafeMath_add((numerator1 / sqrtPX96), amount);
      var __c2 = UnsafeMath_divRoundingUp(numerator1, __c1);
      return uint160(__c2);
    } else {
      uint256 product = 0;
      product = uint256(amount * sqrtPX96);
      require(((product / amount) == sqrtPX96) && (numerator1 > product));
      uint256 denominator = uint256(numerator1 - product);
      var __c3 = FullMath_mulDivRoundingUp(numerator1, sqrtPX96, denominator);
      var __c4 = SafeCast_toUint160(__c3);
      return __c4;
    }
  }

  function SqrtPriceMath_getNextSqrtPriceFromAmount1RoundingDown(uint160 sqrtPX96,
      uint128 liquidity, uint256 amount, bool add) internal returns (uint160) {
    if (add) {
      var __cond1 = 0;
      if ((amount <= type(uint160).max)) {
        __cond1 = ((amount <<[uint256] 96) / liquidity);
      } else {
        var __c0 = FullMath_mulDiv(amount, 79228162514264337593543950336, liquidity);
        __cond1 = __c0;
      }
      uint256 quotient = __cond1;
      var __c2 = LowGasSafeMath_add(uint256(sqrtPX96), quotient);
      var __c3 = SafeCast_toUint160(__c2);
      return __c3;
    } else {
      var __cond6 = 0;
      if ((amount <= type(uint160).max)) {
        var __c4 = UnsafeMath_divRoundingUp((amount <<[uint256] 96), liquidity);
        __cond6 = __c4;
      } else {
        var __c5 = FullMath_mulDivRoundingUp(amount, 79228162514264337593543950336, liquidity);
        __cond6 = __c5;
      }
      uint256 quotient = __cond6;
      require(sqrtPX96 > quotient);
      return uint160(uint256(sqrtPX96 - quotient));
    }
  }

  function SafeCast_toUint160(uint256 y) internal returns (uint160) {
    uint160 z = 0;
    z = uint160(y);
    require(z == y);
    return z;
  }

  function token0() external returns (address) {
    return token0;
  }

  function swap(address recipient, bool zeroForOne, int256 amountSpecified,
      uint160 sqrtPriceLimitX96, bytes calldata data) external returns (int256, int256) {
    int256 amount0 = 0;
    int256 amount1 = 0;
    var __c0 = checkNotDelegateCall();
    require(amountSpecified != 0);
    Slot0 memory slot0Start = slot0;
    require(slot0Start.unlocked);
    require(zeroForOne ? ((sqrtPriceLimitX96 < slot0Start.sqrtPriceX96) && (sqrtPriceLimitX96 >
      4295128739)) : ((sqrtPriceLimitX96 > slot0Start.sqrtPriceX96) && (sqrtPriceLimitX96 <
      (1461446703485210103287273052203988822378723970342))));
    slot0.unlocked = false;
    var __c1 = _blockTimestamp();
    SwapCache memory cache = SwapCache({liquidityStart: liquidity, blockTimestamp: __c1,
      feeProtocol: (zeroForOne ? (slot0Start.feeProtocol % 16) :
      (slot0Start.feeProtocol >>[uint8] 4)), secondsPerLiquidityCumulativeX128: 0,
      tickCumulative: 0, computedLatestObservation: false});
    bool exactInput = amountSpecified > 0;
    SwapState memory state = SwapState({amountSpecifiedRemaining: amountSpecified,
      amountCalculated: 0, sqrtPriceX96: slot0Start.sqrtPriceX96, tick: slot0Start.tick,
      feeGrowthGlobalX128: (zeroForOne ? feeGrowthGlobal0X128 : feeGrowthGlobal1X128),
      protocolFee: 0, liquidity: cache.liquidityStart});
    while ((state.amountSpecifiedRemaining != 0) && (state.sqrtPriceX96 != sqrtPriceLimitX96)) {
      StepComputations step = StepComputations({sqrtPriceStartX96: 0, tickNext: 0,
      initialized: false, sqrtPriceNextX96: 0, amountIn: 0, amountOut: 0, feeAmount: 0});
      step.sqrtPriceStartX96 = state.sqrtPriceX96;
      var __c2 = TickBitmap_nextInitializedTickWithinOneWord(state.tick, int24(tickSpacing),
      zeroForOne);
      step.tickNext = __c2.0;
      step.initialized = __c2.1;
      if (step.tickNext < -887272) {
        step.tickNext = -887272;
      } else {
        if (step.tickNext > (int24(0 - -887272))) {
          step.tickNext = int24(0 - -887272);
        }
      }
      var __c3 = TickMath_getSqrtRatioAtTick(step.tickNext);
      step.sqrtPriceNextX96 = __c3;
      var __c4 = SwapMath_computeSwapStep(state.sqrtPriceX96, ((zeroForOne ?
      (step.sqrtPriceNextX96 < sqrtPriceLimitX96) : (step.sqrtPriceNextX96 >
      sqrtPriceLimitX96)) ? sqrtPriceLimitX96 : step.sqrtPriceNextX96), state.liquidity,
      state.amountSpecifiedRemaining, uint24(fee));
      state.sqrtPriceX96 = __c4.0;
      step.amountIn = __c4.1;
      step.amountOut = __c4.2;
      step.feeAmount = __c4.3;
      if (exactInput) {
        var __c5 = SafeCast_toInt256((uint256(step.amountIn + step.feeAmount)));
        state.amountSpecifiedRemaining = int256(state.amountSpecifiedRemaining - __c5);
        var __c6 = SafeCast_toInt256(step.amountOut);
        var __c7 = LowGasSafeMath_sub(state.amountCalculated, __c6);
        state.amountCalculated = __c7;
      } else {
        var __c8 = SafeCast_toInt256(step.amountOut);
        state.amountSpecifiedRemaining = int256(state.amountSpecifiedRemaining + __c8);
        var __c9 = SafeCast_toInt256((uint256(step.amountIn + step.feeAmount)));
        var __c10 = LowGasSafeMath_add_int256_int256(state.amountCalculated, __c9);
        state.amountCalculated = __c10;
      }
      if (cache.feeProtocol > 0) {
        uint256 delta = step.feeAmount / cache.feeProtocol;
        step.feeAmount = uint256(step.feeAmount - delta);
        state.protocolFee = uint128(state.protocolFee + uint128(delta));
      }
      if (state.liquidity > 0) {
        var __c11 = FullMath_mulDiv(step.feeAmount, (340282366920938463463374607431768211456),
      state.liquidity);
        state.feeGrowthGlobalX128 = uint256(state.feeGrowthGlobalX128 + __c11);
      }
      if (state.sqrtPriceX96 == step.sqrtPriceNextX96) {
        if (step.initialized) {
          if (!(cache.computedLatestObservation)) {
            var __c12 = Oracle_observeSingle(cache.blockTimestamp, 0, slot0Start.tick,
      slot0Start.observationIndex, cache.liquidityStart, slot0Start.observationCardinality);
            cache.tickCumulative = __c12.0;
            cache.secondsPerLiquidityCumulativeX128 = __c12.1;
            cache.computedLatestObservation = true;
          }
          var liquidityNet = Tick_cross(step.tickNext, (zeroForOne ? state.feeGrowthGlobalX128 :
      feeGrowthGlobal0X128), (zeroForOne ? feeGrowthGlobal1X128 : state.feeGrowthGlobalX128),
      cache.secondsPerLiquidityCumulativeX128, cache.tickCumulative, cache.blockTimestamp);
          if (zeroForOne) {
            liquidityNet = int128(0 - liquidityNet);
          }
          var __c14 = LiquidityMath_addDelta(state.liquidity, liquidityNet);
          state.liquidity = __c14;
        }
        state.tick = zeroForOne ? int24(step.tickNext - 1) : step.tickNext;
      } else {
        if (state.sqrtPriceX96 != step.sqrtPriceStartX96) {
          var __c15 = TickMath_getTickAtSqrtRatio(state.sqrtPriceX96);
          state.tick = __c15;
        }
      }
    }
    if (state.tick != slot0Start.tick) {
      var __c16 = Oracle_write(slot0Start.observationIndex, cache.blockTimestamp,
      slot0Start.tick, cache.liquidityStart, slot0Start.observationCardinality,
      slot0Start.observationCardinalityNext);
      uint16 observationIndex = __c16.0;
      uint16 observationCardinality = __c16.1;
      var __t17 = state.sqrtPriceX96;
      var __t18 = state.tick;
      var __t19 = observationIndex;
      var __t20 = observationCardinality;
      slot0.sqrtPriceX96 = __t17;
      slot0.tick = __t18;
      slot0.observationIndex = __t19;
      slot0.observationCardinality = __t20;
    } else {
      slot0.sqrtPriceX96 = state.sqrtPriceX96;
    }
    if (cache.liquidityStart != state.liquidity) {
      liquidity = state.liquidity;
    }
    if (zeroForOne) {
      feeGrowthGlobal0X128 = state.feeGrowthGlobalX128;
      if (state.protocolFee > 0) {
        protocolFees.token0 = uint128(protocolFees.token0 + state.protocolFee);
      }
    } else {
      feeGrowthGlobal1X128 = state.feeGrowthGlobalX128;
      if (state.protocolFee > 0) {
        protocolFees.token1 = uint128(protocolFees.token1 + state.protocolFee);
      }
    }
    if (zeroForOne == exactInput) {
      amount0 = int256(amountSpecified - state.amountSpecifiedRemaining);
      amount1 = state.amountCalculated;
    } else {
      amount0 = state.amountCalculated;
      amount1 = int256(amountSpecified - state.amountSpecifiedRemaining);
    }
    if (zeroForOne) {
      if (amount1 < 0) {
        var __c21 = TransferHelper_safeTransfer(token1, recipient, uint256(int256(0 - amount1)));
      }
      var balance0Before = balance0();
      address callback = msg.sender;
      require(callback.code.length > 0);
      var __c23 = callback.uniswapV3SwapCallback(amount0, amount1, data);
      var __c25 = balance0();
      var __c24 = LowGasSafeMath_add(balance0Before, uint256(amount0));
      require(__c24 <= __c25);
    } else {
      if (amount0 < 0) {
        var __c26 = TransferHelper_safeTransfer(token0, recipient, uint256(int256(0 - amount0)));
      }
      var balance1Before = balance1();
      address callback = msg.sender;
      require(callback.code.length > 0);
      var __c28 = callback.uniswapV3SwapCallback(amount0, amount1, data);
      var __c30 = balance1();
      var __c29 = LowGasSafeMath_add(balance1Before, uint256(amount1));
      require(__c29 <= __c30);
    }
    emit Swap(msg.sender, recipient, amount0, amount1, state.sqrtPriceX96, state.liquidity,
      state.tick);
    slot0.unlocked = true;
    return (amount0, amount1);
  }

  function liquidity() external returns (uint128) {
    return liquidity;
  }

  function protocolFees() external returns (uint128, uint128) {
    return (protocolFees.token0, protocolFees.token1);
  }

  function observations(uint256 arg0) external returns (uint32, int56, uint160, bool) {
    return (observations[arg0].blockTimestamp, observations[arg0].tickCumulative,
      observations[arg0].secondsPerLiquidityCumulativeX128, observations[arg0].initialized);
  }

  function increaseObservationCardinalityNext(uint16 observationCardinalityNext) external {
    require(slot0.unlocked);
    slot0.unlocked = false;
    var __c0 = checkNotDelegateCall();
    uint16 observationCardinalityNextOld = slot0.observationCardinalityNext;
    var observationCardinalityNextNew = Oracle_grow(observationCardinalityNextOld,
      observationCardinalityNext);
    slot0.observationCardinalityNext = observationCardinalityNextNew;
    if (observationCardinalityNextOld != observationCardinalityNextNew) {
      emit IncreaseObservationCardinalityNext(observationCardinalityNextOld,
      observationCardinalityNextNew);
    }
    slot0.unlocked = true;
  }

  function slot0() external returns (uint160, int24, uint16, uint16, uint16, uint8, bool) {
    return (slot0.sqrtPriceX96, slot0.tick, slot0.observationIndex, slot0.observationCardinality,
      slot0.observationCardinalityNext, slot0.feeProtocol, slot0.unlocked);
  }

  function mint(address recipient, int24 tickLower, int24 tickUpper, uint128 amount,
      bytes calldata data) external returns (uint256, uint256) {
    uint256 amount0 = 0;
    uint256 amount1 = 0;
    require(slot0.unlocked);
    slot0.unlocked = false;
    require(amount > 0);
    var __c0 = SafeCast_toInt128(int256(amount));
    var __c1 = _modifyPosition(ModifyPositionParams({owner: recipient, tickLower: tickLower,
      tickUpper: tickUpper, liquidityDelta: __c0}));
    int256 amount0Int = __c1.1;
    int256 amount1Int = __c1.2;
    amount0 = uint256(amount0Int);
    amount1 = uint256(amount1Int);
    uint256 balance0Before = 0;
    uint256 balance1Before = 0;
    if (amount0 > 0) {
      var __c2 = balance0();
      balance0Before = __c2;
    }
    if (amount1 > 0) {
      var __c3 = balance1();
      balance1Before = __c3;
    }
    address callback = msg.sender;
    require(callback.code.length > 0);
    var __c4 = callback.uniswapV3MintCallback(amount0, amount1, data);
    if (amount0 > 0) {
      var __c6 = balance0();
      var __c5 = LowGasSafeMath_add(balance0Before, amount0);
      require(__c5 <= __c6);
    }
    if (amount1 > 0) {
      var __c8 = balance1();
      var __c7 = LowGasSafeMath_add(balance1Before, amount1);
      require(__c7 <= __c8);
    }
    emit Mint(msg.sender, recipient, tickLower, tickUpper, amount, amount0, amount1);
    slot0.unlocked = true;
    return (amount0, amount1);
  }

  function feeGrowthGlobal1X128() external returns (uint256) {
    return feeGrowthGlobal1X128;
  }

  function flash(address recipient, uint256 amount0, uint256 amount1,
      bytes calldata data) external {
    require(slot0.unlocked);
    slot0.unlocked = false;
    var __c0 = checkNotDelegateCall();
    uint128 _liquidity = liquidity;
    require(_liquidity > 0);
    var fee0 = FullMath_mulDivRoundingUp(amount0, uint24(fee), 1000000);
    var fee1 = FullMath_mulDivRoundingUp(amount1, uint24(fee), 1000000);
    var balance0Before = balance0();
    var balance1Before = balance1();
    if (amount0 > 0) {
      var __c5 = TransferHelper_safeTransfer(token0, recipient, amount0);
    }
    if (amount1 > 0) {
      var __c6 = TransferHelper_safeTransfer(token1, recipient, amount1);
    }
    address callback = msg.sender;
    require(callback.code.length > 0);
    var __c7 = callback.uniswapV3FlashCallback(fee0, fee1, data);
    var balance0After = balance0();
    var balance1After = balance1();
    var __c10 = LowGasSafeMath_add(balance0Before, fee0);
    require(__c10 <= balance0After);
    var __c11 = LowGasSafeMath_add(balance1Before, fee1);
    require(__c11 <= balance1After);
    uint256 paid0 = uint256(balance0After - balance0Before);
    uint256 paid1 = uint256(balance1After - balance1Before);
    if (paid0 > 0) {
      uint8 feeProtocol0 = slot0.feeProtocol % 16;
      uint256 fees0 = (feeProtocol0 == 0) ? 0 : (paid0 / feeProtocol0);
      if (uint128(fees0) > 0) {
        protocolFees.token0 = uint128(protocolFees.token0 + uint128(fees0));
      }
      var __c12 = FullMath_mulDiv(uint256(paid0 - fees0),
      (340282366920938463463374607431768211456), _liquidity);
      feeGrowthGlobal0X128 = uint256(feeGrowthGlobal0X128 + __c12);
    }
    if (paid1 > 0) {
      uint8 feeProtocol1 = slot0.feeProtocol >>[uint8] 4;
      uint256 fees1 = (feeProtocol1 == 0) ? 0 : (paid1 / feeProtocol1);
      if (uint128(fees1) > 0) {
        protocolFees.token1 = uint128(protocolFees.token1 + uint128(fees1));
      }
      var __c13 = FullMath_mulDiv(uint256(paid1 - fees1),
      (340282366920938463463374607431768211456), _liquidity);
      feeGrowthGlobal1X128 = uint256(feeGrowthGlobal1X128 + __c13);
    }
    emit Flash(msg.sender, recipient, amount0, amount1, paid0, paid1);
    slot0.unlocked = true;
  }

  function collect(address recipient, int24 tickLower, int24 tickUpper, uint128 amount0Requested,
      uint128 amount1Requested) external returns (uint128, uint128) {
    uint128 amount0 = 0;
    uint128 amount1 = 0;
    require(slot0.unlocked);
    slot0.unlocked = false;
    var __c0 = Position_get(msg.sender, tickLower, tickUpper);
    PositionInfo storage position = positions[__c0];
    amount0 = (amount0Requested > position.tokensOwed0) ? position.tokensOwed0 : amount0Requested;
    amount1 = (amount1Requested > position.tokensOwed1) ? position.tokensOwed1 : amount1Requested;
    if (amount0 > 0) {
      position.tokensOwed0 = uint128(position.tokensOwed0 - amount0);
      var __c1 = TransferHelper_safeTransfer(token0, recipient, amount0);
    }
    if (amount1 > 0) {
      position.tokensOwed1 = uint128(position.tokensOwed1 - amount1);
      var __c2 = TransferHelper_safeTransfer(token1, recipient, amount1);
    }
    emit Collect(msg.sender, recipient, tickLower, tickUpper, amount0, amount1);
    slot0.unlocked = true;
    return (amount0, amount1);
  }

  function positions(bytes32 arg0) external returns (uint128, uint256, uint256, uint128, uint128) {
    return (positions[arg0].liquidity, positions[arg0].feeGrowthInside0LastX128,
      positions[arg0].feeGrowthInside1LastX128, positions[arg0].tokensOwed0,
      positions[arg0].tokensOwed1);
  }

  function tickBitmap(int16 arg0) external returns (uint256) {
    return tickBitmap[arg0];
  }

  function maxLiquidityPerTick() external returns (uint128) {
    return uint128(maxLiquidityPerTick);
  }

  function setFeeProtocol(uint8 feeProtocol0, uint8 feeProtocol1) external {
    require(slot0.unlocked);
    slot0.unlocked = false;
    var __c0 = factoryOwner();
    require(msg.sender == __c0);
    require(((feeProtocol0 == 0) || ((feeProtocol0 >= 4) && (feeProtocol0 <= 10))) &&
      ((feeProtocol1 == 0) || ((feeProtocol1 >= 4) && (feeProtocol1 <= 10))));
    uint8 feeProtocolOld = slot0.feeProtocol;
    slot0.feeProtocol = uint8(feeProtocol0 + (feeProtocol1 <<[uint8] 4));
    emit SetFeeProtocol((feeProtocolOld % 16), (feeProtocolOld >>[uint8] 4), feeProtocol0,
      feeProtocol1);
    slot0.unlocked = true;
  }

  function collectProtocol(address recipient, uint128 amount0Requested,
      uint128 amount1Requested) external returns (uint128, uint128) {
    uint128 amount0 = 0;
    uint128 amount1 = 0;
    require(slot0.unlocked);
    slot0.unlocked = false;
    var __c0 = factoryOwner();
    require(msg.sender == __c0);
    amount0 = (amount0Requested > protocolFees.token0) ? protocolFees.token0 : amount0Requested;
    amount1 = (amount1Requested > protocolFees.token1) ? protocolFees.token1 : amount1Requested;
    if (amount0 > 0) {
      if (amount0 == protocolFees.token0) {
        amount0 = uint128(amount0 - 1);
      }
      protocolFees.token0 = uint128(protocolFees.token0 - amount0);
      var __c1 = TransferHelper_safeTransfer(token0, recipient, amount0);
    }
    if (amount1 > 0) {
      if (amount1 == protocolFees.token1) {
        amount1 = uint128(amount1 - 1);
      }
      protocolFees.token1 = uint128(protocolFees.token1 - amount1);
      var __c2 = TransferHelper_safeTransfer(token1, recipient, amount1);
    }
    emit CollectProtocol(msg.sender, recipient, amount0, amount1);
    slot0.unlocked = true;
    return (amount0, amount1);
  }

  function observe(uint32[] calldata secondsAgos) external returns (int56[], uint160[]) {
    int56[] tickCumulatives = new int56[](0);
    uint160[] secondsPerLiquidityCumulativeX128s = new uint160[](0);
    var __c0 = checkNotDelegateCall();
    var __c1 = _blockTimestamp();
    var __c2 = Oracle_observe(__c1, secondsAgos, slot0.tick, slot0.observationIndex, liquidity,
      slot0.observationCardinality);
    return (__c2.0, __c2.1);
  }

  function burn(int24 tickLower, int24 tickUpper, uint128 amount) external returns (uint256,
      uint256) {
    uint256 amount0 = 0;
    uint256 amount1 = 0;
    require(slot0.unlocked);
    slot0.unlocked = false;
    var __c0 = SafeCast_toInt128(int256(amount));
    var __c1 = _modifyPosition(ModifyPositionParams({owner: msg.sender, tickLower: tickLower,
      tickUpper: tickUpper, liquidityDelta: int128(0 - __c0)}));
    PositionInfo storage position = positions[__c1.0];
    int256 amount0Int = __c1.1;
    int256 amount1Int = __c1.2;
    amount0 = uint256(int256(0 - amount0Int));
    amount1 = uint256(int256(0 - amount1Int));
    if ((amount0 > 0) || (amount1 > 0)) {
      var __t2 = uint128(position.tokensOwed0 + uint128(amount0));
      var __t3 = uint128(position.tokensOwed1 + uint128(amount1));
      position.tokensOwed0 = __t2;
      position.tokensOwed1 = __t3;
    }
    emit Burn(msg.sender, tickLower, tickUpper, amount, amount0, amount1);
    slot0.unlocked = true;
    return (amount0, amount1);
  }

  function snapshotCumulativesInside(int24 tickLower, int24 tickUpper) external returns (int56,
      uint160, uint32) {
    int56 tickCumulativeInside = 0;
    uint160 secondsPerLiquidityInsideX128 = 0;
    uint32 secondsInside = 0;
    var __c0 = checkNotDelegateCall();
    var __c1 = checkTicks(tickLower, tickUpper);
    int56 tickCumulativeLower = 0;
    int56 tickCumulativeUpper = 0;
    uint160 secondsPerLiquidityOutsideLowerX128 = 0;
    uint160 secondsPerLiquidityOutsideUpperX128 = 0;
    uint32 secondsOutsideLower = 0;
    uint32 secondsOutsideUpper = 0;
    TickInfo storage lower = ticks[tickLower];
    TickInfo storage upper = ticks[tickUpper];
    bool initializedLower = false;
    var __t2 = lower.tickCumulativeOutside;
    var __t3 = lower.secondsPerLiquidityOutsideX128;
    var __t4 = lower.secondsOutside;
    var __t5 = lower.initialized;
    tickCumulativeLower = __t2;
    secondsPerLiquidityOutsideLowerX128 = __t3;
    secondsOutsideLower = __t4;
    initializedLower = __t5;
    require(initializedLower);
    bool initializedUpper = false;
    var __t6 = upper.tickCumulativeOutside;
    var __t7 = upper.secondsPerLiquidityOutsideX128;
    var __t8 = upper.secondsOutside;
    var __t9 = upper.initialized;
    tickCumulativeUpper = __t6;
    secondsPerLiquidityOutsideUpperX128 = __t7;
    secondsOutsideUpper = __t8;
    initializedUpper = __t9;
    require(initializedUpper);
    Slot0 memory _slot0 = slot0;
    if (_slot0.tick < tickLower) {
      return (int56(tickCumulativeLower - tickCumulativeUpper),
      uint160(secondsPerLiquidityOutsideLowerX128 - secondsPerLiquidityOutsideUpperX128),
      uint32(secondsOutsideLower - secondsOutsideUpper));
    } else {
      if (_slot0.tick < tickUpper) {
        var time = _blockTimestamp();
        var __c11 = Oracle_observeSingle(time, 0, _slot0.tick, _slot0.observationIndex,
      liquidity, _slot0.observationCardinality);
        int56 tickCumulative = __c11.0;
        uint160 secondsPerLiquidityCumulativeX128 = __c11.1;
        return (int56(int56(tickCumulative - tickCumulativeLower) - tickCumulativeUpper),
      uint160(uint160(secondsPerLiquidityCumulativeX128 - secondsPerLiquidityOutsideLowerX128) -
      secondsPerLiquidityOutsideUpperX128), uint32(uint32(time - secondsOutsideLower) -
      secondsOutsideUpper));
      } else {
        return (int56(tickCumulativeUpper - tickCumulativeLower),
      uint160(secondsPerLiquidityOutsideUpperX128 - secondsPerLiquidityOutsideLowerX128),
      uint32(secondsOutsideUpper - secondsOutsideLower));
      }
    }
    return (tickCumulativeInside, secondsPerLiquidityInsideX128, secondsInside);
  }

  function factory() external returns (address) {
    return factory;
  }

  function tickSpacing() external returns (int24) {
    return int24(tickSpacing);
  }

  function token1() external returns (address) {
    return token1;
  }

  function fee() external returns (uint24) {
    return uint24(fee);
  }

  function feeGrowthGlobal0X128() external returns (uint256) {
    return feeGrowthGlobal0X128;
  }

  function ticks(int24 arg0) external returns (uint128, int128, uint256, uint256, int56, uint160,
      uint32, bool) {
    return (ticks[arg0].liquidityGross, ticks[arg0].liquidityNet,
      ticks[arg0].feeGrowthOutside0X128, ticks[arg0].feeGrowthOutside1X128,
      ticks[arg0].tickCumulativeOutside, ticks[arg0].secondsPerLiquidityOutsideX128,
      ticks[arg0].secondsOutside, ticks[arg0].initialized);
  }

  function «initialize»(uint160 sqrtPriceX96) external {
    require(slot0.sqrtPriceX96 == 0);
    var tick = TickMath_getTickAtSqrtRatio(sqrtPriceX96);
    var __c1 = _blockTimestamp();
    var __c2 = Oracle_initialize(__c1);
    uint16 cardinality = __c2.0;
    uint16 cardinalityNext = __c2.1;
    slot0 = Slot0({sqrtPriceX96: sqrtPriceX96, tick: tick, observationIndex: 0,
      observationCardinality: cardinality, observationCardinalityNext: cardinalityNext,
      feeProtocol: 0, unlocked: true});
    emit Initialize(sqrtPriceX96, tick);
  }

}

end Benchmarks.UniswapV3.Pool.Syntax
