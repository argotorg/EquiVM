import Benchmarks.Scaffolds.UniswapV3Pool.Spec
import Solm.Notation

/-!
# UniswapV3Pool spec in the Solidity-faithful Solm frontend

The whole UniswapV3Pool benchmark spec written with `solidity%` and proven definitionally equal
to the AST spec in `Spec.lean`.

Escapes used, mirroring the AST spec exactly:
* Storage-alias *reads* are var-style in the spec (`.field (.var x) f`), so every alias field
  read goes through `${vf "x" "f"}`; alias *writes* are storage-style (`{base := alias, …}`) and
  stay in surface syntax (`info.liquidityGross = …;`).
* Immutables: `${addrLit v.…}` for addresses, `#(v.fee)` / `#(v.tickSpacing)` /
  `#(v.maxLiquidityPerTick)` for the integer ones.
* List-`Stmt` spec helpers whose receivers are immutable `Expr`s are spliced:
  `${safeTransfer …}`, `${balanceOfInto …}`, `${onlyFactoryOwner v}`, `${checkedWordAddLe …}`;
  their binders are read back via `${Expr.var "…"}` where needed (`flash` `paid0`/`paid1`).
* `${int56Wrap …}` splices for the signed-wrap shape (with `sdivTowardZeroE` inside for
  `observeSingle`); unsigned wraps are the surface `… % #(2 ^ N)`.
* External callbacks on `msg.sender` use the option form (`{view}` for the constructor's
  `parameters` view call, `{value: 0}` for the mint/swap/flash callbacks — the same
  `.intLit 0` eth as the spec's default).
* `#(-887272)` for `minTick` (surface `-` would be `.unary .neg`, the spec uses an `intLit`).
-/

open Solm Solm.Notation Benchmarks.UniswapV3Pool.Immutables

namespace Benchmarks.UniswapV3Pool.Syntax

/-- Var-style read of a storage-alias field: the spec reads aliases as `.field (.var x) f`,
    not as storage references. -/
def vf (x f : Ident) : Expr := .field (.var x) f

def contractSyntax (v : PoolImmutables) : ContractDecl := solidity% contract UniswapV3Pool {
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

  struct Tick.Info {
    uint128 liquidityGross;
    int128 liquidityNet;
    uint256 feeGrowthOutside0X128;
    uint256 feeGrowthOutside1X128;
    int56 tickCumulativeOutside;
    uint160 secondsPerLiquidityOutsideX128;
    uint32 secondsOutside;
    bool initialized;
  }

  struct Position.Info {
    uint128 liquidity;
    uint256 feeGrowthInside0LastX128;
    uint256 feeGrowthInside1LastX128;
    uint128 tokensOwed0;
    uint128 tokensOwed1;
  }

  struct Oracle.Observation {
    uint32 blockTimestamp;
    int56 tickCumulative;
    uint160 secondsPerLiquidityCumulativeX128;
    bool initialized;
  }

  Slot0 slot0;
  uint256 feeGrowthGlobal0X128;
  uint256 feeGrowthGlobal1X128;
  ProtocolFees protocolFees;
  uint128 liquidity;
  mapping(int24 => Tick.Info) ticks;
  mapping(int16 => uint256) tickBitmap;
  mapping(bytes32 => Position.Info) positions;
  Oracle.Observation[65535] observations;
  mapping(uint256 => Oracle.Observation) observationsRaw;

  constructor() {
    var r = msg.sender.parameters{view}();
    var imm_factory = r.0;
    var imm_token0 = r.1;
    var imm_token1 = r.2;
    var imm_fee = r.3;
    var imm_tickSpacing = r.4;
    var imm_original = this;
    var imm_maxLiquidityPerTick = #(2 ^ 128 - 1) / (2 * (887272 / imm_tickSpacing) + 1);
  }

  function getSqrtRatioAtTick(int24 tick) internal returns (uint160) {
    uint256 absTick = tick < 0 ? 0 - tick : tick;
    require(absTick <= 887272);
    uint256 ratio = absTick & 0x1 != 0 ? 0xfffcb933bd6fad37aa2d162d1a594001 : #(2 ^ 128);
    if (absTick & 0x2 != 0) {
      ratio = ratio * 0xfff97272373d413259a46990580e213a >> 128;
    }
    if (absTick & 0x4 != 0) {
      ratio = ratio * 0xfff2e50f5f656932ef12357cf3c7fdcc >> 128;
    }
    if (absTick & 0x8 != 0) {
      ratio = ratio * 0xffe5caca7e10e4e61c3624eaa0941cd0 >> 128;
    }
    if (absTick & 0x10 != 0) {
      ratio = ratio * 0xffcb9843d60f6159c9db58835c926644 >> 128;
    }
    if (absTick & 0x20 != 0) {
      ratio = ratio * 0xff973b41fa98c081472e6896dfb254c0 >> 128;
    }
    if (absTick & 0x40 != 0) {
      ratio = ratio * 0xff2ea16466c96a3843ec78b326b52861 >> 128;
    }
    if (absTick & 0x80 != 0) {
      ratio = ratio * 0xfe5dee046a99a2a811c461f1969c3053 >> 128;
    }
    if (absTick & 0x100 != 0) {
      ratio = ratio * 0xfcbe86c7900a88aedcffc83b479aa3a4 >> 128;
    }
    if (absTick & 0x200 != 0) {
      ratio = ratio * 0xf987a7253ac413176f2b074cf7815e54 >> 128;
    }
    if (absTick & 0x400 != 0) {
      ratio = ratio * 0xf3392b0822b70005940c7a398e4b70f3 >> 128;
    }
    if (absTick & 0x800 != 0) {
      ratio = ratio * 0xe7159475a2c29b7443b29c7fa6e889d9 >> 128;
    }
    if (absTick & 0x1000 != 0) {
      ratio = ratio * 0xd097f3bdfd2022b8845ad8f792aa5825 >> 128;
    }
    if (absTick & 0x2000 != 0) {
      ratio = ratio * 0xa9f746462d870fdf8a65dc1f90e061e5 >> 128;
    }
    if (absTick & 0x4000 != 0) {
      ratio = ratio * 0x70d869a156d2a1b890bb3df62baf32f7 >> 128;
    }
    if (absTick & 0x8000 != 0) {
      ratio = ratio * 0x31be135f97d08fd981231505542fcfa6 >> 128;
    }
    if (absTick & 0x10000 != 0) {
      ratio = ratio * 0x9aa508b5b7a84e1c677de54f3e99bc9 >> 128;
    }
    if (absTick & 0x20000 != 0) {
      ratio = ratio * 0x5d6af8dedb81196699c329225ee604 >> 128;
    }
    if (absTick & 0x40000 != 0) {
      ratio = ratio * 0x2216e584f5fa1ea926041bedfe98 >> 128;
    }
    if (absTick & 0x80000 != 0) {
      ratio = ratio * 0x48a170391f7dc42444e8fa2 >> 128;
    }
    if (tick > 0) {
      ratio = type(uint256).max / ratio;
    }
    return (ratio >> 32) + (ratio % #(2 ^ 32) == 0 ? 0 : 1);
  }

  function getTickAtSqrtRatio(uint160 sqrtPriceX96) internal returns (int24) {
    require(sqrtPriceX96 >= 4295128739 &&
      sqrtPriceX96 < 1461446703485210103287273052203988822378723970342);
    uint256 ratio = sqrtPriceX96 << 32;
    uint256 r = ratio;
    uint256 msb = 0;
    uint256 f = r > 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ? #(2 ^ 7) : 0;
    msb = msb + f;
    r = r >> f;
    uint256 f = r > 0xFFFFFFFFFFFFFFFF ? #(2 ^ 6) : 0;
    msb = msb + f;
    r = r >> f;
    uint256 f = r > 0xFFFFFFFF ? #(2 ^ 5) : 0;
    msb = msb + f;
    r = r >> f;
    uint256 f = r > 0xFFFF ? #(2 ^ 4) : 0;
    msb = msb + f;
    r = r >> f;
    uint256 f = r > 0xFF ? #(2 ^ 3) : 0;
    msb = msb + f;
    r = r >> f;
    uint256 f = r > 0xF ? #(2 ^ 2) : 0;
    msb = msb + f;
    r = r >> f;
    uint256 f = r > 0x3 ? #(2 ^ 1) : 0;
    msb = msb + f;
    r = r >> f;
    uint256 f = r > 0x1 ? 1 : 0;
    msb = msb + f;
    if (msb >= 128) {
      r = ratio >> (msb - 127);
    } else {
      r = ratio << (127 - msb);
    }
    int256 log_2 = (msb - 128) * #(2 ^ 64);
    r = r * r >> 127;
    uint256 f = r >> 128;
    log_2 = log_2 + f * #(2 ^ 63);
    r = r >> f;
    r = r * r >> 127;
    uint256 f = r >> 128;
    log_2 = log_2 + f * #(2 ^ 62);
    r = r >> f;
    r = r * r >> 127;
    uint256 f = r >> 128;
    log_2 = log_2 + f * #(2 ^ 61);
    r = r >> f;
    r = r * r >> 127;
    uint256 f = r >> 128;
    log_2 = log_2 + f * #(2 ^ 60);
    r = r >> f;
    r = r * r >> 127;
    uint256 f = r >> 128;
    log_2 = log_2 + f * #(2 ^ 59);
    r = r >> f;
    r = r * r >> 127;
    uint256 f = r >> 128;
    log_2 = log_2 + f * #(2 ^ 58);
    r = r >> f;
    r = r * r >> 127;
    uint256 f = r >> 128;
    log_2 = log_2 + f * #(2 ^ 57);
    r = r >> f;
    r = r * r >> 127;
    uint256 f = r >> 128;
    log_2 = log_2 + f * #(2 ^ 56);
    r = r >> f;
    r = r * r >> 127;
    uint256 f = r >> 128;
    log_2 = log_2 + f * #(2 ^ 55);
    r = r >> f;
    r = r * r >> 127;
    uint256 f = r >> 128;
    log_2 = log_2 + f * #(2 ^ 54);
    r = r >> f;
    r = r * r >> 127;
    uint256 f = r >> 128;
    log_2 = log_2 + f * #(2 ^ 53);
    r = r >> f;
    r = r * r >> 127;
    uint256 f = r >> 128;
    log_2 = log_2 + f * #(2 ^ 52);
    r = r >> f;
    r = r * r >> 127;
    uint256 f = r >> 128;
    log_2 = log_2 + f * #(2 ^ 51);
    r = r >> f;
    r = r * r >> 127;
    uint256 f = r >> 128;
    log_2 = log_2 + f * #(2 ^ 50);
    int256 log_sqrt10001 = log_2 * 255738958999603826347141;
    int24 tickLow = (log_sqrt10001 - 3402992956809132418596140100660247210) / #(2 ^ 128);
    int24 tickHi = (log_sqrt10001 + 291339464771989622907027621153398088495) / #(2 ^ 128);
    var sqrtRatioAtTickHi = getSqrtRatioAtTick(tickHi);
    return tickLow == tickHi ? tickLow : (sqrtRatioAtTickHi <= sqrtPriceX96 ? tickHi : tickLow);
  }

  function oracleLte(uint32 time, uint32 a, uint32 b) internal returns (bool) {
    if (a <= time && b <= time) {
      return a <= b;
    }
    uint256 aAdjusted = a > time ? a : a + #(2 ^ 32);
    uint256 bAdjusted = b > time ? b : b + #(2 ^ 32);
    return aAdjusted <= bAdjusted;
  }

  function oracleTransform(uint32 lastBlockTimestamp, int56 lastTickCumulative,
      uint160 lastSecondsPerLiquidityCumulativeX128, uint32 blockTimestamp, int24 tick,
      uint128 liquidity) internal returns (uint32, int56, uint160, bool) {
    uint32 delta = (blockTimestamp - lastBlockTimestamp) % #(2 ^ 32);
    uint128 liquidityDenominator = liquidity > 0 ? liquidity : 1;
    int56 tickCumulative =
      ${int56Wrap (addE (.var "lastTickCumulative") (mulE (.var "tick") (.var "delta")))};
    uint160 secondsPerLiquidityCumulativeX128 =
      (lastSecondsPerLiquidityCumulativeX128 + (delta << 128) / liquidityDenominator)
        % #(2 ^ 160);
    return blockTimestamp, tickCumulative, secondsPerLiquidityCumulativeX128, true;
  }

  function getSurroundingObservations(uint32 time, uint32 target, int24 tick, uint16 index,
      uint128 liquidity, uint16 cardinality)
      internal returns (uint32, int56, uint160, bool, uint32, int56, uint160, bool) {
    Oracle.Observation storage beforeOrAt = observations[index];
    uint32 atOrAfterBlockTimestamp = 0;
    int56 atOrAfterTickCumulative = 0;
    uint160 atOrAfterSecondsPerLiquidityCumulativeX128 = 0;
    bool atOrAfterInitialized = false;
    var targetAtOrAfterNewest = oracleLte(time, ${vf "beforeOrAt" "blockTimestamp"}, target);
    if (targetAtOrAfterNewest) {
      if (${vf "beforeOrAt" "blockTimestamp"} == target) {
        return ${vf "beforeOrAt" "blockTimestamp"}, ${vf "beforeOrAt" "tickCumulative"},
          ${vf "beforeOrAt" "secondsPerLiquidityCumulativeX128"},
          ${vf "beforeOrAt" "initialized"},
          atOrAfterBlockTimestamp, atOrAfterTickCumulative,
          atOrAfterSecondsPerLiquidityCumulativeX128, atOrAfterInitialized;
      }
      var transformed = oracleTransform(${vf "beforeOrAt" "blockTimestamp"},
        ${vf "beforeOrAt" "tickCumulative"},
        ${vf "beforeOrAt" "secondsPerLiquidityCumulativeX128"}, target, tick, liquidity);
      return ${vf "beforeOrAt" "blockTimestamp"}, ${vf "beforeOrAt" "tickCumulative"},
        ${vf "beforeOrAt" "secondsPerLiquidityCumulativeX128"},
        ${vf "beforeOrAt" "initialized"},
        transformed.0, transformed.1, transformed.2, transformed.3;
    }
    uint256 oldestIndex = (index + 1) % cardinality;
    Oracle.Observation storage oldest = observations[oldestIndex];
    if (!${vf "oldest" "initialized"}) {
      Oracle.Observation storage oldest = observations[0];
    }
    var targetAtOrAfterOldest = oracleLte(time, ${vf "oldest" "blockTimestamp"}, target);
    require(targetAtOrAfterOldest);
    uint256 l = oldestIndex;
    uint256 r = l + (cardinality - 1);
    while (true) {
      uint256 i = (l + r) / 2;
      Oracle.Observation storage beforeOrAt = observations[i % cardinality];
      if (!${vf "beforeOrAt" "initialized"}) {
        l = i + 1;
        continue;
      }
      Oracle.Observation storage atOrAfter = observations[(i + 1) % cardinality];
      var targetAtOrAfter = oracleLte(time, ${vf "beforeOrAt" "blockTimestamp"}, target);
      var targetAtOrBeforeAfter = oracleLte(time, target, ${vf "atOrAfter" "blockTimestamp"});
      if (targetAtOrAfter && targetAtOrBeforeAfter) {
        return ${vf "beforeOrAt" "blockTimestamp"}, ${vf "beforeOrAt" "tickCumulative"},
          ${vf "beforeOrAt" "secondsPerLiquidityCumulativeX128"},
          ${vf "beforeOrAt" "initialized"},
          ${vf "atOrAfter" "blockTimestamp"}, ${vf "atOrAfter" "tickCumulative"},
          ${vf "atOrAfter" "secondsPerLiquidityCumulativeX128"},
          ${vf "atOrAfter" "initialized"};
      }
      if (!targetAtOrAfter) {
        r = i - 1;
      } else {
        l = i + 1;
      }
    }
    return ${vf "oldest" "blockTimestamp"}, ${vf "oldest" "tickCumulative"},
      ${vf "oldest" "secondsPerLiquidityCumulativeX128"}, ${vf "oldest" "initialized"},
      atOrAfterBlockTimestamp, atOrAfterTickCumulative,
      atOrAfterSecondsPerLiquidityCumulativeX128, atOrAfterInitialized;
  }

  function observeSingle(uint32 time, uint32 secondsAgo, int24 tick, uint16 index,
      uint128 liquidity, uint16 cardinality) internal returns (int56, uint160) {
    if (secondsAgo == 0) {
      require(index < 65535);
      if (observationsRaw[index].blockTimestamp != time) {
        var lastTransformed = oracleTransform(observationsRaw[index].blockTimestamp,
          observationsRaw[index].tickCumulative,
          observationsRaw[index].secondsPerLiquidityCumulativeX128, time, tick, liquidity);
        return lastTransformed.1, lastTransformed.2;
      } else {
        return observationsRaw[index].tickCumulative,
          observationsRaw[index].secondsPerLiquidityCumulativeX128;
      }
    }
    uint32 target = (time - secondsAgo) % #(2 ^ 32);
    var surrounding = getSurroundingObservations(time, target, tick, index, liquidity,
      cardinality);
    if (target == surrounding.0) {
      return surrounding.1, surrounding.2;
    }
    if (target == surrounding.4) {
      return surrounding.5, surrounding.6;
    }
    uint32 observationTimeDelta = (surrounding.4 - surrounding.0) % #(2 ^ 32);
    uint32 targetDelta = (target - surrounding.0) % #(2 ^ 32);
    return
      ${int56Wrap (addE (tuple1 (.var "surrounding"))
        (mulE
          (sdivTowardZeroE (subE (tuple5 (.var "surrounding")) (tuple1 (.var "surrounding")))
            (.var "observationTimeDelta"))
          (.var "targetDelta")))},
      (surrounding.2 + (surrounding.6 - surrounding.2) * targetDelta / observationTimeDelta)
        % #(2 ^ 160);
  }

  function observeBody(uint32 time, uint32[] secondsAgos, int24 tick, uint16 index,
      uint128 liquidity, uint16 cardinality) internal returns (int56[], uint160[]) {
    require(cardinality > 0);
    int56[] tickCumulatives = new int56[](secondsAgos.length);
    uint160[] secondsPerLiquidityCumulativeX128s = new uint160[](secondsAgos.length);
    uint256 i = 0;
    while (i < secondsAgos.length) {
      var observed = observeSingle(time, secondsAgos[i], tick, index, liquidity, cardinality);
      tickCumulatives[i] = observed.0;
      secondsPerLiquidityCumulativeX128s[i] = observed.1;
      i = i + 1;
    }
    return tickCumulatives, secondsPerLiquidityCumulativeX128s;
  }

  function liquidityAddDelta(uint128 x, int128 y) internal returns (uint128) {
    if (y < 0) {
      uint128 z = (x - (0 - y)) % #(2 ^ 128);
      require(z < x);
      return z;
    } else {
      uint128 z = (x + y) % #(2 ^ 128);
      require(z >= x);
      return z;
    }
  }

  function oracleWrite(uint16 index, uint32 blockTimestamp, int24 tick, uint128 liquidity,
      uint16 cardinality, uint16 cardinalityNext) internal returns (uint16, uint16) {
    Oracle.Observation storage last = observations[index];
    if (${vf "last" "blockTimestamp"} == blockTimestamp) {
      return index, cardinality;
    }
    uint16 cardinalityUpdated =
      cardinalityNext > cardinality && index == cardinality - 1 ? cardinalityNext : cardinality;
    uint16 indexUpdated = (index + 1) % cardinalityUpdated;
    var transformed = oracleTransform(${vf "last" "blockTimestamp"},
      ${vf "last" "tickCumulative"}, ${vf "last" "secondsPerLiquidityCumulativeX128"},
      blockTimestamp, tick, liquidity);
    observations[indexUpdated].blockTimestamp = transformed.0;
    observations[indexUpdated].tickCumulative = transformed.1;
    observations[indexUpdated].secondsPerLiquidityCumulativeX128 = transformed.2;
    observations[indexUpdated].initialized = transformed.3;
    return indexUpdated, cardinalityUpdated;
  }

  function tickGetFeeGrowthInside(int24 tickLower, int24 tickUpper, int24 tickCurrent,
      uint256 feeGrowthGlobal0X128, uint256 feeGrowthGlobal1X128)
      internal returns (uint256, uint256) {
    Tick.Info storage lower = ticks[tickLower];
    Tick.Info storage upper = ticks[tickUpper];
    uint256 feeGrowthBelow0X128 = tickCurrent >= tickLower ?
      ${vf "lower" "feeGrowthOutside0X128"} :
      (feeGrowthGlobal0X128 - ${vf "lower" "feeGrowthOutside0X128"}) % #(2 ^ 256);
    uint256 feeGrowthBelow1X128 = tickCurrent >= tickLower ?
      ${vf "lower" "feeGrowthOutside1X128"} :
      (feeGrowthGlobal1X128 - ${vf "lower" "feeGrowthOutside1X128"}) % #(2 ^ 256);
    uint256 feeGrowthAbove0X128 = tickCurrent < tickUpper ?
      ${vf "upper" "feeGrowthOutside0X128"} :
      (feeGrowthGlobal0X128 - ${vf "upper" "feeGrowthOutside0X128"}) % #(2 ^ 256);
    uint256 feeGrowthAbove1X128 = tickCurrent < tickUpper ?
      ${vf "upper" "feeGrowthOutside1X128"} :
      (feeGrowthGlobal1X128 - ${vf "upper" "feeGrowthOutside1X128"}) % #(2 ^ 256);
    return ((feeGrowthGlobal0X128 - feeGrowthBelow0X128) % #(2 ^ 256) - feeGrowthAbove0X128)
        % #(2 ^ 256),
      ((feeGrowthGlobal1X128 - feeGrowthBelow1X128) % #(2 ^ 256) - feeGrowthAbove1X128)
        % #(2 ^ 256);
  }

  function tickUpdate(int24 tick, int24 tickCurrent, int128 liquidityDelta,
      uint256 feeGrowthGlobal0X128, uint256 feeGrowthGlobal1X128,
      uint160 secondsPerLiquidityCumulativeX128, int56 tickCumulative, uint32 time,
      bool upper, uint128 maxLiquidity) internal returns (bool) {
    Tick.Info storage info = ticks[tick];
    uint128 liquidityGrossBefore = ${vf "info" "liquidityGross"};
    var liquidityGrossAfter = liquidityAddDelta(liquidityGrossBefore, liquidityDelta);
    require(liquidityGrossAfter <= maxLiquidity);
    bool flipped = (liquidityGrossAfter == 0) != (liquidityGrossBefore == 0);
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
    info.liquidityNet = (upper ?
      ${vf "info" "liquidityNet"} - liquidityDelta :
      ${vf "info" "liquidityNet"} + liquidityDelta) as int128;
    return flipped;
  }

  function tickClear(int24 tick) internal {
    delete ticks[tick];
  }

  function tickBitmapFlip(int24 tick, int24 tickSpacing) internal {
    require(tick % tickSpacing == 0);
    int24 compressed = tick / tickSpacing;
    int16 wordPos = compressed / 256;
    uint8 bitPos = compressed % 256;
    uint256 mask = 1 << bitPos;
    tickBitmap[wordPos] = tickBitmap[wordPos] ^ mask;
  }

  function positionUpdate(bytes32 positionKey, int128 liquidityDelta,
      uint256 feeGrowthInside0X128, uint256 feeGrowthInside1X128) internal {
    Position.Info storage position = positions[positionKey];
    if (liquidityDelta == 0) {
      require(${vf "position" "liquidity"} > 0);
      uint128 liquidityNext = ${vf "position" "liquidity"};
    } else {
      var liquidityNext = liquidityAddDelta(${vf "position" "liquidity"}, liquidityDelta);
    }
    uint128 tokensOwed0 =
      ((feeGrowthInside0X128 - ${vf "position" "feeGrowthInside0LastX128"}) % #(2 ^ 256)
        * ${vf "position" "liquidity"} / #(2 ^ 128)) % #(2 ^ 128);
    uint128 tokensOwed1 =
      ((feeGrowthInside1X128 - ${vf "position" "feeGrowthInside1LastX128"}) % #(2 ^ 256)
        * ${vf "position" "liquidity"} / #(2 ^ 128)) % #(2 ^ 128);
    if (liquidityDelta != 0) {
      position.liquidity = liquidityNext;
    }
    position.feeGrowthInside0LastX128 = feeGrowthInside0X128;
    position.feeGrowthInside1LastX128 = feeGrowthInside1X128;
    if (tokensOwed0 > 0 || tokensOwed1 > 0) {
      position.tokensOwed0 = ${vf "position" "tokensOwed0"} + tokensOwed0;
      position.tokensOwed1 = ${vf "position" "tokensOwed1"} + tokensOwed1;
    }
  }

  function getAmount0DeltaUnsigned(uint160 sqrtRatioAX96, uint160 sqrtRatioBX96,
      uint128 liquidity, bool roundUp) internal returns (uint256) {
    uint160 sqrtRatioA = sqrtRatioAX96;
    uint160 sqrtRatioB = sqrtRatioBX96;
    if (sqrtRatioA > sqrtRatioB) {
      sqrtRatioA = sqrtRatioBX96;
      sqrtRatioB = sqrtRatioAX96;
    }
    uint256 numerator1 = liquidity << 96;
    uint256 numerator2 = sqrtRatioB - sqrtRatioA;
    require(sqrtRatioA > 0);
    if (roundUp) {
      require(sqrtRatioB > 0);
      uint256 product = numerator1 * numerator2 / sqrtRatioB;
      require(product <= type(uint256).max);
      if (numerator1 * numerator2 % sqrtRatioB > 0) {
        require(product < type(uint256).max);
        product = product + 1;
      }
      require(sqrtRatioA > 0);
      uint256 amount0 = product / sqrtRatioA;
      if (product % sqrtRatioA > 0) {
        require(amount0 < type(uint256).max);
        amount0 = amount0 + 1;
      }
      return amount0;
    } else {
      require(sqrtRatioB > 0);
      uint256 product = numerator1 * numerator2 / sqrtRatioB;
      require(product <= type(uint256).max);
      return product / sqrtRatioA;
    }
  }

  function getAmount1DeltaUnsigned(uint160 sqrtRatioAX96, uint160 sqrtRatioBX96,
      uint128 liquidity, bool roundUp) internal returns (uint256) {
    uint160 sqrtRatioA = sqrtRatioAX96;
    uint160 sqrtRatioB = sqrtRatioBX96;
    if (sqrtRatioA > sqrtRatioB) {
      sqrtRatioA = sqrtRatioBX96;
      sqrtRatioB = sqrtRatioAX96;
    }
    if (roundUp) {
      require(#(2 ^ 96) > 0);
      uint256 amount1 = liquidity * (sqrtRatioB - sqrtRatioA) / #(2 ^ 96);
      require(amount1 <= type(uint256).max);
      if (liquidity * (sqrtRatioB - sqrtRatioA) % #(2 ^ 96) > 0) {
        require(amount1 < type(uint256).max);
        amount1 = amount1 + 1;
      }
      return amount1;
    } else {
      require(#(2 ^ 96) > 0);
      uint256 amount1 = liquidity * (sqrtRatioB - sqrtRatioA) / #(2 ^ 96);
      require(amount1 <= type(uint256).max);
      return amount1;
    }
  }

  function getAmount0DeltaSigned(uint160 sqrtRatioAX96, uint160 sqrtRatioBX96,
      int128 liquidity) internal returns (int256) {
    if (liquidity < 0) {
      var amount0Unsigned = getAmount0DeltaUnsigned(sqrtRatioAX96, sqrtRatioBX96,
        (0 - liquidity) % #(2 ^ 128), false);
      return 0 - amount0Unsigned;
    } else {
      var amount0Unsigned = getAmount0DeltaUnsigned(sqrtRatioAX96, sqrtRatioBX96,
        liquidity % #(2 ^ 128), true);
      return amount0Unsigned;
    }
  }

  function getAmount1DeltaSigned(uint160 sqrtRatioAX96, uint160 sqrtRatioBX96,
      int128 liquidity) internal returns (int256) {
    if (liquidity < 0) {
      var amount1Unsigned = getAmount1DeltaUnsigned(sqrtRatioAX96, sqrtRatioBX96,
        (0 - liquidity) % #(2 ^ 128), false);
      return 0 - amount1Unsigned;
    } else {
      var amount1Unsigned = getAmount1DeltaUnsigned(sqrtRatioAX96, sqrtRatioBX96,
        liquidity % #(2 ^ 128), true);
      return amount1Unsigned;
    }
  }

  function modifyPosition(address owner, int24 tickLower, int24 tickUpper,
      int128 liquidityDelta) internal returns (bytes32, int256, int256) {
    require(this == ${addrLit v.original});
    require(tickLower < tickUpper);
    require(tickLower >= #(-887272));
    require(tickUpper <= 887272);
    uint160 _slot0sqrtPriceX96 = slot0.sqrtPriceX96;
    int24 _slot0tick = slot0.tick;
    uint16 _slot0observationIndex = slot0.observationIndex;
    uint16 _slot0observationCardinality = slot0.observationCardinality;
    uint16 _slot0observationCardinalityNext = slot0.observationCardinalityNext;
    bytes32 _positionKey =
      keccak256(abi.encodePacked(address(owner), int24(tickLower), int24(tickUpper)));
    uint256 _feeGrowthGlobal0X128 = feeGrowthGlobal0X128;
    uint256 _feeGrowthGlobal1X128 = feeGrowthGlobal1X128;
    bool flippedLower = false;
    bool flippedUpper = false;
    if (liquidityDelta != 0) {
      uint32 time = block.timestamp % #(2 ^ 32);
      var observedForUpdate = observeSingle(time, 0, slot0.tick, slot0.observationIndex,
        liquidity, slot0.observationCardinality);
      var flippedLowerCall = tickUpdate(tickLower, _slot0tick, liquidityDelta,
        _feeGrowthGlobal0X128, _feeGrowthGlobal1X128, observedForUpdate.1,
        observedForUpdate.0, time, false, #(v.maxLiquidityPerTick));
      flippedLower = flippedLowerCall;
      var flippedUpperCall = tickUpdate(tickUpper, _slot0tick, liquidityDelta,
        _feeGrowthGlobal0X128, _feeGrowthGlobal1X128, observedForUpdate.1,
        observedForUpdate.0, time, true, #(v.maxLiquidityPerTick));
      flippedUpper = flippedUpperCall;
      if (flippedLower) {
        var _flipLower = tickBitmapFlip(tickLower, #(v.tickSpacing));
      }
      if (flippedUpper) {
        var _flipUpper = tickBitmapFlip(tickUpper, #(v.tickSpacing));
      }
    }
    var feeGrowthInside = tickGetFeeGrowthInside(tickLower, tickUpper, _slot0tick,
      _feeGrowthGlobal0X128, _feeGrowthGlobal1X128);
    var _positionUpdated = positionUpdate(_positionKey, liquidityDelta, feeGrowthInside.0,
      feeGrowthInside.1);
    if (liquidityDelta < 0) {
      if (flippedLower) {
        var _clearLower = tickClear(tickLower);
      }
      if (flippedUpper) {
        var _clearUpper = tickClear(tickUpper);
      }
    }
    int256 amount0 = 0;
    int256 amount1 = 0;
    if (liquidityDelta != 0) {
      if (_slot0tick < tickLower) {
        var sqrtRatioLowerBelow = getSqrtRatioAtTick(tickLower);
        var sqrtRatioUpperBelow = getSqrtRatioAtTick(tickUpper);
        var amount0Below = getAmount0DeltaSigned(sqrtRatioLowerBelow, sqrtRatioUpperBelow,
          liquidityDelta);
        amount0 = amount0Below;
      } else {
        if (_slot0tick < tickUpper) {
          uint128 liquidityBefore = liquidity;
          var oracleUpdated = oracleWrite(_slot0observationIndex, block.timestamp % #(2 ^ 32),
            _slot0tick, liquidityBefore, _slot0observationCardinality,
            _slot0observationCardinalityNext);
          slot0.observationIndex = oracleUpdated.0;
          slot0.observationCardinality = oracleUpdated.1;
          var sqrtRatioUpperInside = getSqrtRatioAtTick(tickUpper);
          var amount0Inside = getAmount0DeltaSigned(_slot0sqrtPriceX96, sqrtRatioUpperInside,
            liquidityDelta);
          amount0 = amount0Inside;
          var sqrtRatioLowerInside = getSqrtRatioAtTick(tickLower);
          var amount1Inside = getAmount1DeltaSigned(sqrtRatioLowerInside, _slot0sqrtPriceX96,
            liquidityDelta);
          amount1 = amount1Inside;
          var liquidityAfter = liquidityAddDelta(liquidityBefore, liquidityDelta);
          liquidity = liquidityAfter;
        } else {
          var sqrtRatioLowerAbove = getSqrtRatioAtTick(tickLower);
          var sqrtRatioUpperAbove = getSqrtRatioAtTick(tickUpper);
          var amount1Above = getAmount1DeltaSigned(sqrtRatioLowerAbove, sqrtRatioUpperAbove,
            liquidityDelta);
          amount1 = amount1Above;
        }
      }
    }
    return _positionKey, amount0, amount1;
  }

  function mostSignificantBit(uint256 x) internal returns (uint8) {
    require(x > 0);
    uint8 r = 0;
    if (x >= #(2 ^ 128)) {
      x = x >> 128;
      r = r + 128;
    }
    if (x >= #(2 ^ 64)) {
      x = x >> 64;
      r = r + 64;
    }
    if (x >= #(2 ^ 32)) {
      x = x >> 32;
      r = r + 32;
    }
    if (x >= #(2 ^ 16)) {
      x = x >> 16;
      r = r + 16;
    }
    if (x >= #(2 ^ 8)) {
      x = x >> 8;
      r = r + 8;
    }
    if (x >= #(2 ^ 4)) {
      x = x >> 4;
      r = r + 4;
    }
    if (x >= #(2 ^ 2)) {
      x = x >> 2;
      r = r + 2;
    }
    if (x >= 2) {
      r = r + 1;
    }
    return r;
  }

  function leastSignificantBit(uint256 x) internal returns (uint8) {
    require(x > 0);
    uint8 r = 255;
    if (x & #(2 ^ 128 - 1) > 0) {
      r = r - 128;
    } else {
      x = x >> 128;
    }
    if (x & #(2 ^ 64 - 1) > 0) {
      r = r - 64;
    } else {
      x = x >> 64;
    }
    if (x & #(2 ^ 32 - 1) > 0) {
      r = r - 32;
    } else {
      x = x >> 32;
    }
    if (x & #(2 ^ 16 - 1) > 0) {
      r = r - 16;
    } else {
      x = x >> 16;
    }
    if (x & #(2 ^ 8 - 1) > 0) {
      r = r - 8;
    } else {
      x = x >> 8;
    }
    if (x & 0xf > 0) {
      r = r - 4;
    } else {
      x = x >> 4;
    }
    if (x & 0x3 > 0) {
      r = r - 2;
    } else {
      x = x >> 2;
    }
    if (x & 0x1 > 0) {
      r = r - 1;
    }
    return r;
  }

  function tickBitmapNextInitializedTickWithinOneWord(int24 tick, int24 tickSpacing, bool lte)
      internal returns (int24, bool) {
    int24 compressed = tick / tickSpacing;
    if (lte) {
      int16 wordPos = compressed / 256;
      uint8 bitPos = compressed % 256;
      uint256 oneAtBit = 1 << bitPos;
      uint256 mask = (oneAtBit - 1) + oneAtBit;
      uint256 masked = tickBitmap[wordPos] & mask;
      bool initialized = masked != 0;
      if (initialized) {
        var msb = mostSignificantBit(masked);
        return ((compressed - (bitPos - msb)) * tickSpacing) as int24, initialized;
      } else {
        return ((compressed - bitPos) * tickSpacing) as int24, initialized;
      }
    } else {
      int24 compressedPlusOne = compressed + 1;
      int16 wordPos = compressedPlusOne / 256;
      uint8 bitPos = compressedPlusOne % 256;
      uint256 mask = ~((1 << bitPos) - 1);
      uint256 masked = tickBitmap[wordPos] & mask;
      bool initialized = masked != 0;
      if (initialized) {
        var lsb = leastSignificantBit(masked);
        return ((compressedPlusOne + (lsb - bitPos)) * tickSpacing) as int24, initialized;
      } else {
        return ((compressedPlusOne + (255 - bitPos)) * tickSpacing) as int24, initialized;
      }
    }
  }

  function tickCross(int24 tick, uint256 feeGrowthGlobal0X128, uint256 feeGrowthGlobal1X128,
      uint160 secondsPerLiquidityCumulativeX128, int56 tickCumulative, uint32 time)
      internal returns (int128) {
    Tick.Info storage info = ticks[tick];
    info.feeGrowthOutside0X128 =
      (feeGrowthGlobal0X128 - ${vf "info" "feeGrowthOutside0X128"}) % #(2 ^ 256);
    info.feeGrowthOutside1X128 =
      (feeGrowthGlobal1X128 - ${vf "info" "feeGrowthOutside1X128"}) % #(2 ^ 256);
    info.secondsPerLiquidityOutsideX128 =
      (secondsPerLiquidityCumulativeX128 - ${vf "info" "secondsPerLiquidityOutsideX128"})
        % #(2 ^ 160);
    info.tickCumulativeOutside =
      ${int56Wrap (subE (.var "tickCumulative") (vf "info" "tickCumulativeOutside"))};
    info.secondsOutside = (time - ${vf "info" "secondsOutside"}) % #(2 ^ 32);
    return ${vf "info" "liquidityNet"};
  }

  function getNextSqrtPriceFromAmount0RoundingUp(uint160 sqrtPX96, uint128 liquidity,
      uint256 amount, bool add) internal returns (uint160) {
    if (amount == 0) {
      return sqrtPX96;
    }
    uint256 numerator1 = liquidity << 96;
    if (add) {
      uint256 product = amount * sqrtPX96 % #(2 ^ 256);
      if (product / amount == sqrtPX96) {
        uint256 denominator = (numerator1 + product) % #(2 ^ 256);
        if (denominator >= numerator1) {
          require(denominator > 0);
          uint256 price = numerator1 * sqrtPX96 / denominator;
          require(price <= type(uint256).max);
          if (numerator1 * sqrtPX96 % denominator > 0) {
            require(price < type(uint256).max);
            price = price + 1;
          }
          return price % #(2 ^ 160);
        }
      }
      uint256 denominator2Base = numerator1 / sqrtPX96;
      uint256 denominator2 = (denominator2Base + amount) % #(2 ^ 256);
      require(denominator2 >= denominator2Base);
      require(denominator2 > 0);
      uint256 price = numerator1 / denominator2;
      if (numerator1 % denominator2 > 0) {
        require(price < type(uint256).max);
        price = price + 1;
      }
      return price % #(2 ^ 160);
    } else {
      uint256 product = amount * sqrtPX96 % #(2 ^ 256);
      require(product / amount == sqrtPX96 && numerator1 > product);
      uint256 denominator = numerator1 - product;
      require(denominator > 0);
      uint256 price = numerator1 * sqrtPX96 / denominator;
      require(price <= type(uint256).max);
      if (numerator1 * sqrtPX96 % denominator > 0) {
        require(price < type(uint256).max);
        price = price + 1;
      }
      return (price) as uint160;
    }
  }

  function getNextSqrtPriceFromAmount1RoundingDown(uint160 sqrtPX96, uint128 liquidity,
      uint256 amount, bool add) internal returns (uint160) {
    if (add) {
      if (amount <= type(uint160).max) {
        uint256 quotient = (amount << 96) / liquidity;
      } else {
        require(liquidity > 0);
        uint256 quotient = amount * #(2 ^ 96) / liquidity;
        require(quotient <= type(uint256).max);
      }
      uint256 next = (sqrtPX96 + quotient) % #(2 ^ 256);
      require(next >= sqrtPX96);
      return (next) as uint160;
    } else {
      if (amount <= type(uint160).max) {
        require(liquidity > 0);
        uint256 quotient = (amount << 96) / liquidity;
        if ((amount << 96) % liquidity > 0) {
          require(quotient < type(uint256).max);
          quotient = quotient + 1;
        }
      } else {
        require(liquidity > 0);
        uint256 quotient = amount * #(2 ^ 96) / liquidity;
        require(quotient <= type(uint256).max);
        if (amount * #(2 ^ 96) % liquidity > 0) {
          require(quotient < type(uint256).max);
          quotient = quotient + 1;
        }
      }
      require(sqrtPX96 > quotient);
      return sqrtPX96 - quotient;
    }
  }

  function getNextSqrtPriceFromInput(uint160 sqrtPX96, uint128 liquidity, uint256 amountIn,
      bool zeroForOne) internal returns (uint160) {
    require(sqrtPX96 > 0);
    require(liquidity > 0);
    if (zeroForOne) {
      var sqrtQX96 = getNextSqrtPriceFromAmount0RoundingUp(sqrtPX96, liquidity, amountIn,
        true);
      return sqrtQX96;
    } else {
      var sqrtQX96 = getNextSqrtPriceFromAmount1RoundingDown(sqrtPX96, liquidity, amountIn,
        true);
      return sqrtQX96;
    }
  }

  function getNextSqrtPriceFromOutput(uint160 sqrtPX96, uint128 liquidity, uint256 amountOut,
      bool zeroForOne) internal returns (uint160) {
    require(sqrtPX96 > 0);
    require(liquidity > 0);
    if (zeroForOne) {
      var sqrtQX96 = getNextSqrtPriceFromAmount1RoundingDown(sqrtPX96, liquidity, amountOut,
        false);
      return sqrtQX96;
    } else {
      var sqrtQX96 = getNextSqrtPriceFromAmount0RoundingUp(sqrtPX96, liquidity, amountOut,
        false);
      return sqrtQX96;
    }
  }

  function computeSwapStep(uint160 sqrtRatioCurrentX96, uint160 sqrtRatioTargetX96,
      uint128 liquidity, int256 amountRemaining, uint24 feePips)
      internal returns (uint160, uint256, uint256, uint256) {
    bool zeroForOne = sqrtRatioCurrentX96 >= sqrtRatioTargetX96;
    bool exactIn = amountRemaining >= 0;
    uint160 sqrtRatioNextX96 = 0;
    uint256 amountIn = 0;
    uint256 amountOut = 0;
    uint256 feeAmount = 0;
    if (exactIn) {
      require(1000000 > 0);
      uint256 amountRemainingLessFee =
        amountRemaining % #(2 ^ 256) * (1000000 - feePips) / 1000000;
      require(amountRemainingLessFee <= type(uint256).max);
      if (zeroForOne) {
        var amountInToTarget = getAmount0DeltaUnsigned(sqrtRatioTargetX96,
          sqrtRatioCurrentX96, liquidity, true);
      } else {
        var amountInToTarget = getAmount1DeltaUnsigned(sqrtRatioCurrentX96,
          sqrtRatioTargetX96, liquidity, true);
      }
      amountIn = amountInToTarget;
      if (amountRemainingLessFee >= amountIn) {
        sqrtRatioNextX96 = sqrtRatioTargetX96;
      } else {
        var nextSqrtInput = getNextSqrtPriceFromInput(sqrtRatioCurrentX96, liquidity,
          amountRemainingLessFee, zeroForOne);
        sqrtRatioNextX96 = nextSqrtInput;
      }
    } else {
      if (zeroForOne) {
        var amountOutToTarget = getAmount1DeltaUnsigned(sqrtRatioTargetX96,
          sqrtRatioCurrentX96, liquidity, false);
      } else {
        var amountOutToTarget = getAmount0DeltaUnsigned(sqrtRatioCurrentX96,
          sqrtRatioTargetX96, liquidity, false);
      }
      amountOut = amountOutToTarget;
      if ((0 - amountRemaining) % #(2 ^ 256) >= amountOut) {
        sqrtRatioNextX96 = sqrtRatioTargetX96;
      } else {
        var nextSqrtOutput = getNextSqrtPriceFromOutput(sqrtRatioCurrentX96, liquidity,
          (0 - amountRemaining) % #(2 ^ 256), zeroForOne);
        sqrtRatioNextX96 = nextSqrtOutput;
      }
    }
    bool max = sqrtRatioTargetX96 == sqrtRatioNextX96;
    if (zeroForOne) {
      if (!(max && exactIn)) {
        var amountInRecomputed = getAmount0DeltaUnsigned(sqrtRatioNextX96,
          sqrtRatioCurrentX96, liquidity, true);
        amountIn = amountInRecomputed;
      }
      if (!(max && !exactIn)) {
        var amountOutRecomputed = getAmount1DeltaUnsigned(sqrtRatioNextX96,
          sqrtRatioCurrentX96, liquidity, false);
        amountOut = amountOutRecomputed;
      }
    } else {
      if (!(max && exactIn)) {
        var amountInRecomputed = getAmount1DeltaUnsigned(sqrtRatioCurrentX96,
          sqrtRatioNextX96, liquidity, true);
        amountIn = amountInRecomputed;
      }
      if (!(max && !exactIn)) {
        var amountOutRecomputed = getAmount0DeltaUnsigned(sqrtRatioCurrentX96,
          sqrtRatioNextX96, liquidity, false);
        amountOut = amountOutRecomputed;
      }
    }
    if (!exactIn && amountOut > (0 - amountRemaining) % #(2 ^ 256)) {
      amountOut = (0 - amountRemaining) % #(2 ^ 256);
    }
    if (exactIn && sqrtRatioNextX96 != sqrtRatioTargetX96) {
      feeAmount = amountRemaining % #(2 ^ 256) - amountIn;
    } else {
      require(1000000 - feePips > 0);
      uint256 feeAmountComputed = amountIn * feePips / (1000000 - feePips);
      require(feeAmountComputed <= type(uint256).max);
      if (amountIn * feePips % (1000000 - feePips) > 0) {
        require(feeAmountComputed < type(uint256).max);
        feeAmountComputed = feeAmountComputed + 1;
      }
      feeAmount = feeAmountComputed;
    }
    return sqrtRatioNextX96, amountIn, amountOut, feeAmount;
  }

  function burn(int24 tickLower, int24 tickUpper, uint128 amount)
      external returns (uint256, uint256) {
    require(slot0.unlocked);
    slot0.unlocked = false;
    int128 liquidityDelta = 0 - ((amount) as int128);
    var modified = modifyPosition(msg.sender, tickLower, tickUpper, liquidityDelta);
    Position.Info storage position = positions[modified.0];
    uint256 amount0 = (0 - modified.1) % #(2 ^ 256);
    uint256 amount1 = (0 - modified.2) % #(2 ^ 256);
    if (amount0 > 0 || amount1 > 0) {
      position.tokensOwed0 = ${vf "position" "tokensOwed0"} + amount0 % #(2 ^ 128);
      position.tokensOwed1 = ${vf "position" "tokensOwed1"} + amount1 % #(2 ^ 128);
    }
    slot0.unlocked = true;
    return amount0, amount1;
  }

  function collect(address recipient, int24 tickLower, int24 tickUpper,
      uint128 amount0Requested, uint128 amount1Requested)
      external returns (uint128, uint128) {
    require(slot0.unlocked);
    slot0.unlocked = false;
    bytes32 positionKey =
      keccak256(abi.encodePacked(address(msg.sender), int24(tickLower), int24(tickUpper)));
    uint128 amount0 = amount0Requested > positions[positionKey].tokensOwed0 ?
      positions[positionKey].tokensOwed0 : amount0Requested;
    uint128 amount1 = amount1Requested > positions[positionKey].tokensOwed1 ?
      positions[positionKey].tokensOwed1 : amount1Requested;
    if (amount0 > 0) {
      positions[positionKey].tokensOwed0 = positions[positionKey].tokensOwed0 - amount0;
      ${safeTransfer (addrLit v.token0) (.var "recipient") (.var "amount0") "collect0"}
    }
    if (amount1 > 0) {
      positions[positionKey].tokensOwed1 = positions[positionKey].tokensOwed1 - amount1;
      ${safeTransfer (addrLit v.token1) (.var "recipient") (.var "amount1") "collect1"}
    }
    slot0.unlocked = true;
    return amount0, amount1;
  }

  function collectProtocol(address recipient, uint128 amount0Requested,
      uint128 amount1Requested) external returns (uint128, uint128) {
    require(slot0.unlocked);
    slot0.unlocked = false;
    ${onlyFactoryOwner v}
    uint128 amount0 = amount0Requested > protocolFees.token0 ?
      protocolFees.token0 : amount0Requested;
    uint128 amount1 = amount1Requested > protocolFees.token1 ?
      protocolFees.token1 : amount1Requested;
    if (amount0 > 0) {
      if (amount0 == protocolFees.token0) {
        amount0 = amount0 - 1;
      }
      protocolFees.token0 = protocolFees.token0 - amount0;
      ${safeTransfer (addrLit v.token0) (.var "recipient") (.var "amount0") "collectProtocol0"}
    }
    if (amount1 > 0) {
      if (amount1 == protocolFees.token1) {
        amount1 = amount1 - 1;
      }
      protocolFees.token1 = protocolFees.token1 - amount1;
      ${safeTransfer (addrLit v.token1) (.var "recipient") (.var "amount1") "collectProtocol1"}
    }
    slot0.unlocked = true;
    return amount0, amount1;
  }

  function factory() external returns (address) {
    return ${addrLit v.factory};
  }

  function fee() external returns (uint24) {
    return #(v.fee);
  }

  function feeGrowthGlobal0X128() external returns (uint256) {
    return feeGrowthGlobal0X128;
  }

  function feeGrowthGlobal1X128() external returns (uint256) {
    return feeGrowthGlobal1X128;
  }

  function flash(address recipient, uint256 amount0, uint256 amount1, bytes data) external {
    require(slot0.unlocked);
    slot0.unlocked = false;
    require(this == ${addrLit v.original});
    uint128 _liquidity = liquidity;
    require(_liquidity > 0);
    require(1000000 > 0);
    uint256 fee0 = amount0 * #(v.fee) / 1000000;
    require(fee0 <= type(uint256).max);
    if (amount0 * #(v.fee) % 1000000 > 0) {
      require(fee0 < type(uint256).max);
      fee0 = fee0 + 1;
    }
    require(1000000 > 0);
    uint256 fee1 = amount1 * #(v.fee) / 1000000;
    require(fee1 <= type(uint256).max);
    if (amount1 * #(v.fee) % 1000000 > 0) {
      require(fee1 < type(uint256).max);
      fee1 = fee1 + 1;
    }
    ${balanceOfInto (addrLit v.token0) "balance0Before" "flashBalance0Before"}
    ${balanceOfInto (addrLit v.token1) "balance1Before" "flashBalance1Before"}
    if (amount0 > 0) {
      ${safeTransfer (addrLit v.token0) (.var "recipient") (.var "amount0") "flashTransfer0"}
    }
    if (amount1 > 0) {
      ${safeTransfer (addrLit v.token1) (.var "recipient") (.var "amount1") "flashTransfer1"}
    }
    var _flashCallback = msg.sender.uniswapV3FlashCallback{value: 0}(fee0, fee1, data);
    ${balanceOfInto (addrLit v.token0) "balance0After" "flashBalance0After"}
    ${balanceOfInto (addrLit v.token1) "balance1After" "flashBalance1After"}
    ${checkedWordAddLe (.var "balance0Before") (.var "fee0") (.var "balance0After")}
    ${checkedWordAddLe (.var "balance1Before") (.var "fee1") (.var "balance1After")}
    uint256 paid0 = ${Expr.var "balance0After"} - ${Expr.var "balance0Before"};
    uint256 paid1 = ${Expr.var "balance1After"} - ${Expr.var "balance1Before"};
    if (paid0 > 0) {
      uint8 feeProtocol0 = slot0.feeProtocol % 16;
      uint256 fees0 = feeProtocol0 == 0 ? 0 : paid0 / feeProtocol0;
      if (fees0 % #(2 ^ 128) > 0) {
        protocolFees.token0 = protocolFees.token0 + fees0 % #(2 ^ 128);
      }
      require(_liquidity > 0);
      uint256 feeGrowth0Delta = (paid0 - fees0) * #(2 ^ 128) / _liquidity;
      require(feeGrowth0Delta <= type(uint256).max);
      feeGrowthGlobal0X128 = feeGrowthGlobal0X128 + feeGrowth0Delta;
    }
    if (paid1 > 0) {
      uint8 feeProtocol1 = 0 << 0;
      feeProtocol1 = slot0.feeProtocol >> 4;
      uint256 fees1 = feeProtocol1 == 0 ? 0 : paid1 / feeProtocol1;
      if (fees1 % #(2 ^ 128) > 0) {
        protocolFees.token1 = protocolFees.token1 + fees1 % #(2 ^ 128);
      }
      require(_liquidity > 0);
      uint256 feeGrowth1Delta = (paid1 - fees1) * #(2 ^ 128) / _liquidity;
      require(feeGrowth1Delta <= type(uint256).max);
      feeGrowthGlobal1X128 = feeGrowthGlobal1X128 + feeGrowth1Delta;
    }
    slot0.unlocked = true;
  }

  function increaseObservationCardinalityNext(uint16 observationCardinalityNext) external {
    require(slot0.unlocked);
    slot0.unlocked = false;
    require(this == ${addrLit v.original});
    uint16 observationCardinalityNextOld = slot0.observationCardinalityNext;
    uint16 observationCardinalityNextNew = observationCardinalityNext;
    require(observationCardinalityNextOld > 0);
    if (observationCardinalityNextNew <= observationCardinalityNextOld) {
      observationCardinalityNextNew = observationCardinalityNextOld;
    } else {
      uint16 i = observationCardinalityNextOld;
      while (i < observationCardinalityNextNew) {
        observationsRaw[i].blockTimestamp = 1;
        i = i + 1;
      }
    }
    slot0.observationCardinalityNext = observationCardinalityNextNew;
    slot0.unlocked = true;
  }

  function «initialize»(uint160 sqrtPriceX96) external {
    require(slot0.sqrtPriceX96 == 0);
    var tick = getTickAtSqrtRatio(sqrtPriceX96);
    uint32 time = block.timestamp % #(2 ^ 32);
    observations[0].blockTimestamp = time;
    observations[0].tickCumulative = 0;
    observations[0].secondsPerLiquidityCumulativeX128 = 0;
    observations[0].initialized = true;
    slot0.sqrtPriceX96 = sqrtPriceX96;
    slot0.tick = tick;
    slot0.observationIndex = 0;
    slot0.observationCardinality = 1;
    slot0.observationCardinalityNext = 1;
    slot0.feeProtocol = 0;
    slot0.unlocked = true;
  }

  function liquidity() external returns (uint128) {
    return liquidity;
  }

  function maxLiquidityPerTick() external returns (uint128) {
    return #(v.maxLiquidityPerTick);
  }

  function mint(address recipient, int24 tickLower, int24 tickUpper, uint128 amount,
      bytes data) external returns (uint256, uint256) {
    require(slot0.unlocked);
    slot0.unlocked = false;
    require(amount > 0);
    int128 liquidityDelta = (amount) as int128;
    var modified = modifyPosition(recipient, tickLower, tickUpper, liquidityDelta);
    uint256 amount0 = modified.1 % #(2 ^ 256);
    uint256 amount1 = modified.2 % #(2 ^ 256);
    if (amount0 > 0) {
      ${balanceOfInto (addrLit v.token0) "balance0Before" "mintBalance0Before"}
    }
    if (amount1 > 0) {
      ${balanceOfInto (addrLit v.token1) "balance1Before" "mintBalance1Before"}
    }
    var _mintCallback = msg.sender.uniswapV3MintCallback{value: 0}(amount0, amount1, data);
    if (amount0 > 0) {
      ${balanceOfInto (addrLit v.token0) "balance0After" "mintBalance0After" ++
        checkedWordAddLe (.var "balance0Before") (.var "amount0") (.var "balance0After")}
    }
    if (amount1 > 0) {
      ${balanceOfInto (addrLit v.token1) "balance1After" "mintBalance1After" ++
        checkedWordAddLe (.var "balance1Before") (.var "amount1") (.var "balance1After")}
    }
    slot0.unlocked = true;
    return amount0, amount1;
  }

  function observations(uint256 arg0) external returns (uint32, int56, uint160, bool) {
    require(arg0 < 65535);
    return observationsRaw[arg0].blockTimestamp, observationsRaw[arg0].tickCumulative,
      observationsRaw[arg0].secondsPerLiquidityCumulativeX128,
      observationsRaw[arg0].initialized;
  }

  function observe(uint32[] secondsAgos) external returns (int56[], uint160[]) {
    require(this == ${addrLit v.original});
    var observed = observeBody(block.timestamp % #(2 ^ 32), secondsAgos, slot0.tick,
      slot0.observationIndex, liquidity, slot0.observationCardinality);
    return observed.0, observed.1;
  }

  function positions(bytes32 arg0)
      external returns (uint128, uint256, uint256, uint128, uint128) {
    return positions[arg0].liquidity, positions[arg0].feeGrowthInside0LastX128,
      positions[arg0].feeGrowthInside1LastX128, positions[arg0].tokensOwed0,
      positions[arg0].tokensOwed1;
  }

  function protocolFees() external returns (uint128, uint128) {
    return protocolFees.token0, protocolFees.token1;
  }

  function setFeeProtocol(uint8 feeProtocol0, uint8 feeProtocol1) external {
    require(slot0.unlocked);
    slot0.unlocked = false;
    ${onlyFactoryOwner v}
    require((feeProtocol0 == 0 || (feeProtocol0 >= 4 && feeProtocol0 <= 10)) &&
      (feeProtocol1 == 0 || (feeProtocol1 >= 4 && feeProtocol1 <= 10)));
    uint8 feeProtocolOld = slot0.feeProtocol;
    slot0.feeProtocol = feeProtocol0 + (feeProtocol1 << 4);
    slot0.unlocked = true;
  }

  function slot0() external returns (uint160, int24, uint16, uint16, uint16, uint8, bool) {
    return slot0.sqrtPriceX96, slot0.tick, slot0.observationIndex,
      slot0.observationCardinality, slot0.observationCardinalityNext, slot0.feeProtocol,
      slot0.unlocked;
  }

  function snapshotCumulativesInside(int24 tickLower, int24 tickUpper)
      external returns (int56, uint160, uint32) {
    require(this == ${addrLit v.original});
    require(tickLower < tickUpper);
    require(tickLower >= #(-887272));
    require(tickUpper <= 887272);
    Tick.Info storage lower = ticks[tickLower];
    Tick.Info storage upper = ticks[tickUpper];
    require(${vf "lower" "initialized"});
    require(${vf "upper" "initialized"});
    if (slot0.tick < tickLower) {
      return ${int56Wrap (subE (vf "lower" "tickCumulativeOutside")
          (vf "upper" "tickCumulativeOutside"))},
        (${vf "lower" "secondsPerLiquidityOutsideX128"} -
          ${vf "upper" "secondsPerLiquidityOutsideX128"}) % #(2 ^ 160),
        (${vf "lower" "secondsOutside"} - ${vf "upper" "secondsOutside"}) % #(2 ^ 32);
    }
    if (slot0.tick < tickUpper) {
      uint32 time = block.timestamp % #(2 ^ 32);
      var currentObservation = observeSingle(time, 0, slot0.tick, slot0.observationIndex,
        liquidity, slot0.observationCardinality);
      return ${int56Wrap (subE (subE (tuple0 (.var "currentObservation"))
            (vf "lower" "tickCumulativeOutside"))
          (vf "upper" "tickCumulativeOutside"))},
        (currentObservation.1 - ${vf "lower" "secondsPerLiquidityOutsideX128"} -
          ${vf "upper" "secondsPerLiquidityOutsideX128"}) % #(2 ^ 160),
        (time - ${vf "lower" "secondsOutside"} - ${vf "upper" "secondsOutside"}) % #(2 ^ 32);
    } else {
      return ${int56Wrap (subE (vf "upper" "tickCumulativeOutside")
          (vf "lower" "tickCumulativeOutside"))},
        (${vf "upper" "secondsPerLiquidityOutsideX128"} -
          ${vf "lower" "secondsPerLiquidityOutsideX128"}) % #(2 ^ 160),
        (${vf "upper" "secondsOutside"} - ${vf "lower" "secondsOutside"}) % #(2 ^ 32);
    }
  }

  function swap(address recipient, bool zeroForOne, int256 amountSpecified,
      uint160 sqrtPriceLimitX96, bytes data) external returns (int256, int256) {
    require(this == ${addrLit v.original});
    require(amountSpecified != 0);
    uint160 slot0StartSqrtPriceX96 = slot0.sqrtPriceX96;
    int24 slot0StartTick = slot0.tick;
    uint16 slot0StartObservationIndex = slot0.observationIndex;
    uint16 slot0StartObservationCardinality = slot0.observationCardinality;
    uint16 slot0StartObservationCardinalityNext = slot0.observationCardinalityNext;
    uint8 slot0StartFeeProtocol = slot0.feeProtocol;
    bool slot0StartUnlocked = slot0.unlocked;
    require(slot0StartUnlocked);
    require(zeroForOne ?
      sqrtPriceLimitX96 < slot0StartSqrtPriceX96 && sqrtPriceLimitX96 > 4295128739 :
      sqrtPriceLimitX96 > slot0StartSqrtPriceX96 &&
        sqrtPriceLimitX96 < 1461446703485210103287273052203988822378723970342);
    slot0.unlocked = false;
    uint128 cacheLiquidityStart = liquidity;
    uint32 cacheBlockTimestamp = block.timestamp % #(2 ^ 32);
    uint8 cacheFeeProtocol = zeroForOne ?
      slot0StartFeeProtocol % 16 : slot0StartFeeProtocol >> 4;
    uint160 cacheSecondsPerLiquidityCumulativeX128 = 0;
    int56 cacheTickCumulative = 0;
    bool cacheComputedLatestObservation = false;
    bool exactInput = amountSpecified > 0;
    int256 stateAmountSpecifiedRemaining = amountSpecified;
    int256 stateAmountCalculated = 0;
    uint160 stateSqrtPriceX96 = slot0StartSqrtPriceX96;
    int24 stateTick = slot0StartTick;
    uint256 stateFeeGrowthGlobalX128 = zeroForOne ?
      feeGrowthGlobal0X128 : feeGrowthGlobal1X128;
    uint128 stateProtocolFee = 0;
    uint128 stateLiquidity = cacheLiquidityStart;
    while (stateAmountSpecifiedRemaining != 0 && stateSqrtPriceX96 != sqrtPriceLimitX96) {
      uint160 stepSqrtPriceStartX96 = stateSqrtPriceX96;
      var nextTick = tickBitmapNextInitializedTickWithinOneWord(stateTick, #(v.tickSpacing),
        zeroForOne);
      int24 stepTickNext = nextTick.0;
      bool stepInitialized = nextTick.1;
      if (stepTickNext < #(-887272)) {
        stepTickNext = #(-887272);
      } else {
        if (stepTickNext > 887272) {
          stepTickNext = 887272;
        }
      }
      var stepSqrtPriceNextX96 = getSqrtRatioAtTick(stepTickNext);
      uint160 stepTargetSqrtPriceX96 =
        (zeroForOne ? stepSqrtPriceNextX96 < sqrtPriceLimitX96 :
          stepSqrtPriceNextX96 > sqrtPriceLimitX96) ?
        sqrtPriceLimitX96 : stepSqrtPriceNextX96;
      var stepResult = computeSwapStep(stateSqrtPriceX96, stepTargetSqrtPriceX96,
        stateLiquidity, stateAmountSpecifiedRemaining, #(v.fee));
      stateSqrtPriceX96 = stepResult.0;
      uint256 stepAmountIn = stepResult.1;
      uint256 stepAmountOut = stepResult.2;
      uint256 stepFeeAmount = stepResult.3;
      if (exactInput) {
        stateAmountSpecifiedRemaining =
          (stateAmountSpecifiedRemaining - ((stepAmountIn + stepFeeAmount) as int256))
            as int256;
        stateAmountCalculated =
          (stateAmountCalculated - ((stepAmountOut) as int256)) as int256;
      } else {
        stateAmountSpecifiedRemaining =
          (stateAmountSpecifiedRemaining + ((stepAmountOut) as int256)) as int256;
        stateAmountCalculated =
          (stateAmountCalculated + ((stepAmountIn + stepFeeAmount) as int256)) as int256;
      }
      if (cacheFeeProtocol > 0) {
        uint256 protocolDelta = stepFeeAmount / cacheFeeProtocol;
        stepFeeAmount = stepFeeAmount - protocolDelta;
        stateProtocolFee = (stateProtocolFee + protocolDelta % #(2 ^ 128)) % #(2 ^ 128);
      }
      if (stateLiquidity > 0) {
        require(stateLiquidity > 0);
        uint256 feeGrowthGlobalDelta = stepFeeAmount * #(2 ^ 128) / stateLiquidity;
        require(feeGrowthGlobalDelta <= type(uint256).max);
        stateFeeGrowthGlobalX128 =
          (stateFeeGrowthGlobalX128 + feeGrowthGlobalDelta) % #(2 ^ 256);
      }
      if (stateSqrtPriceX96 == stepSqrtPriceNextX96) {
        if (stepInitialized) {
          if (!cacheComputedLatestObservation) {
            var latestObservation = observeSingle(cacheBlockTimestamp, 0, slot0StartTick,
              slot0StartObservationIndex, cacheLiquidityStart,
              slot0StartObservationCardinality);
            cacheTickCumulative = latestObservation.0;
            cacheSecondsPerLiquidityCumulativeX128 = latestObservation.1;
            cacheComputedLatestObservation = true;
          }
          var liquidityNetCross = tickCross(stepTickNext,
            zeroForOne ? stateFeeGrowthGlobalX128 : feeGrowthGlobal0X128,
            zeroForOne ? feeGrowthGlobal1X128 : stateFeeGrowthGlobalX128,
            cacheSecondsPerLiquidityCumulativeX128, cacheTickCumulative,
            cacheBlockTimestamp);
          int128 liquidityNet = liquidityNetCross;
          if (zeroForOne) {
            liquidityNet = (0 - liquidityNet) as int128;
          }
          var stateLiquidityAfterCross = liquidityAddDelta(stateLiquidity, liquidityNet);
          stateLiquidity = stateLiquidityAfterCross;
        }
        stateTick = zeroForOne ? stepTickNext - 1 : stepTickNext;
      } else {
        if (stateSqrtPriceX96 != stepSqrtPriceStartX96) {
          var stateTickUpdated = getTickAtSqrtRatio(stateSqrtPriceX96);
          stateTick = stateTickUpdated;
        }
      }
    }
    if (stateTick != slot0StartTick) {
      var oracleUpdatedAfterSwap = oracleWrite(slot0StartObservationIndex,
        cacheBlockTimestamp, slot0StartTick, cacheLiquidityStart,
        slot0StartObservationCardinality, slot0StartObservationCardinalityNext);
      slot0.sqrtPriceX96 = stateSqrtPriceX96;
      slot0.tick = stateTick;
      slot0.observationIndex = oracleUpdatedAfterSwap.0;
      slot0.observationCardinality = oracleUpdatedAfterSwap.1;
    } else {
      slot0.sqrtPriceX96 = stateSqrtPriceX96;
    }
    if (cacheLiquidityStart != stateLiquidity) {
      liquidity = stateLiquidity;
    }
    if (zeroForOne) {
      feeGrowthGlobal0X128 = stateFeeGrowthGlobalX128;
      if (stateProtocolFee > 0) {
        protocolFees.token0 = protocolFees.token0 + stateProtocolFee;
      }
    } else {
      feeGrowthGlobal1X128 = stateFeeGrowthGlobalX128;
      if (stateProtocolFee > 0) {
        protocolFees.token1 = protocolFees.token1 + stateProtocolFee;
      }
    }
    int256 amount0 = 0;
    int256 amount1 = 0;
    if (zeroForOne == exactInput) {
      amount0 = (amountSpecified - stateAmountSpecifiedRemaining) as int256;
      amount1 = stateAmountCalculated;
    } else {
      amount0 = stateAmountCalculated;
      amount1 = (amountSpecified - stateAmountSpecifiedRemaining) as int256;
    }
    if (zeroForOne) {
      if (amount1 < 0) {
        ${safeTransfer (addrLit v.token1) (.var "recipient")
          (uint256Wrap (subE (.intLit 0) (.var "amount1"))) "swapTransfer1"}
      }
      ${balanceOfInto (addrLit v.token0) "balance0Before" "swapBalance0Before"}
      var _swapCallback = msg.sender.uniswapV3SwapCallback{value: 0}(amount0, amount1, data);
      ${balanceOfInto (addrLit v.token0) "balance0After" "swapBalance0After"}
      ${checkedWordAddLe (.var "balance0Before") (uint256Wrap (.var "amount0"))
        (.var "balance0After")}
    } else {
      if (amount0 < 0) {
        ${safeTransfer (addrLit v.token0) (.var "recipient")
          (uint256Wrap (subE (.intLit 0) (.var "amount0"))) "swapTransfer0"}
      }
      ${balanceOfInto (addrLit v.token1) "balance1Before" "swapBalance1Before"}
      var _swapCallback = msg.sender.uniswapV3SwapCallback{value: 0}(amount0, amount1, data);
      ${balanceOfInto (addrLit v.token1) "balance1After" "swapBalance1After"}
      ${checkedWordAddLe (.var "balance1Before") (uint256Wrap (.var "amount1"))
        (.var "balance1After")}
    }
    slot0.unlocked = true;
    return amount0, amount1;
  }

  function tickBitmap(int16 arg0) external returns (uint256) {
    return tickBitmap[arg0];
  }

  function tickSpacing() external returns (int24) {
    return #(v.tickSpacing);
  }

  function ticks(int24 arg0)
      external returns (uint128, int128, uint256, uint256, int56, uint160, uint32, bool) {
    return ticks[arg0].liquidityGross, ticks[arg0].liquidityNet,
      ticks[arg0].feeGrowthOutside0X128, ticks[arg0].feeGrowthOutside1X128,
      ticks[arg0].tickCumulativeOutside, ticks[arg0].secondsPerLiquidityOutsideX128,
      ticks[arg0].secondsOutside, ticks[arg0].initialized;
  }

  function token0() external returns (address) {
    return ${addrLit v.token0};
  }

  function token1() external returns (address) {
    return ${addrLit v.token1};
  }
}

theorem contractSyntax_eq (v : PoolImmutables) :
    contractSyntax v = contract v := by rfl

end Benchmarks.UniswapV3Pool.Syntax
