import Solm.Notation
import Solm.Semantics.Types
import ABI.Encode

/-!
# PoolManager specification

Derived from the pinned solc 0.8.26 via-IR AST, then edited against the source and
the complete runtime and constructor bytecode. The original translator diagnostics
remain in PoolManager.spec.json; its call table mistakes several library and UDVT
operations for external calls. The authoritative table is `externalABI` below.

The generated refinement statements carry the user-authorized return-span
well-formedness condition and the gas bound below. See HANDOFF.md for the bound's
derivation, differential evidence, and the proof obligations left to the proving
session. This specification and the generated proof skeleton contain no completed
function-body refinement proofs.
-/

open Solm Solm.Notation

namespace Benchmarks.UniswapV4PoolManager.Syntax

/-- Authorized refinement precondition for `extsload(bytes32,uint256)`.
The named return is an ABI array only when its byte span does not wrap. The
runtime uses base 160 and a 64-byte prefix (PCs 9741–9780), hence 224 + 32*n.
This constrains the call argument, not storage or gas. In particular, it excludes
the cheap successful malformed returns for n = 2^251 and n = 2^251 - 2.
There is deliberately no corresponding `require` in the specification body:
the bytecode does not enforce this precondition. See DSS Cure/Common for the
same use of a no-overflow predicate in `runtimeRefinementWithWF`.
-/
def poolManagerWF (_σ : Ethereum.AccountMap) (I : Ethereum.ExecutionEnv) : Prop :=
  (I.calldata.extract 0 4 = (⟨#[0x35, 0xfd, 0x63, 0x1a]⟩ : ByteArray) ∧
    I.weiValue = ⟨0⟩ ∧ 68 ≤ I.calldata.size ∧ I.calldata.size < 2^255 + 4) →
  224 + 32 * (Ethereum.uInt256OfByteArray (I.calldata.readBytes 36 32)).toNat <
    Ethereum.UInt256.size

/-- Starting-gas domain for abstracting compiler memory-capacity bookkeeping.
With C(n) = 3*n + n*n/512 and K = 2^58, the cutoff is
C(K+3) + C(K-2) + 3*(K-2) + 1487. At the cutoff, an `unlockCallback`
reply can make the compiler's aggregate allocation check revert even though its
decoded bytes are valid. Below it, such a reply exhausts gas. The hand-off explains
the tight boundary and the other memory paths covered by it. This is a refinement
hypothesis, not a runtime guard or a model of memory in the specification body.
-/
def poolManagerGasBound (g : Ethereum.UInt256) : Prop :=
  g.toNat < 324518553658429321982441292826060

set_option maxHeartbeats 0 in
def contractSyntax : ContractDecl := solidity% contract PoolManager {
  struct TickInfo {
    uint256 liquidityPacked;
    uint256 feeGrowthOutside0X128;
    uint256 feeGrowthOutside1X128;
  }

  struct Pool_State {
    bytes32 slot0;
    uint256 feeGrowthGlobal0X128;
    uint256 feeGrowthGlobal1X128;
    uint128 liquidity;
    mapping(int24 => TickInfo) ticks;
    mapping(int16 => uint256) tickBitmap;
    mapping(bytes32 => Position_State) positions;
  }

  struct Pool_ModifyLiquidityParams {
    address owner;
    int24 tickLower;
    int24 tickUpper;
    int128 liquidityDelta;
    int24 tickSpacing;
    bytes32 salt;
  }

  struct ModifyLiquidityState {
    bool flippedLower;
    uint128 liquidityGrossAfterLower;
    bool flippedUpper;
    uint128 liquidityGrossAfterUpper;
  }

  struct SwapResult {
    uint160 sqrtPriceX96;
    int24 tick;
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
    uint256 feeGrowthGlobalX128;
  }

  struct Pool_SwapParams {
    int256 amountSpecified;
    int24 tickSpacing;
    bool zeroForOne;
    uint160 sqrtPriceLimitX96;
    uint24 lpFeeOverride;
  }

  struct Position_State {
    uint128 liquidity;
    uint256 feeGrowthInside0LastX128;
    uint256 feeGrowthInside1LastX128;
  }

  struct PoolKey {
    address currency0;
    address currency1;
    uint24 fee;
    int24 tickSpacing;
    address hooks;
  }

  struct ModifyLiquidityParams_8903 {
    int24 tickLower;
    int24 tickUpper;
    int256 liquidityDelta;
    bytes32 salt;
  }

  struct SwapParams_8914 {
    bool zeroForOne;
    int256 amountSpecified;
    uint160 sqrtPriceLimitX96;
  }

  -- Whole-word views for assembly's arbitrary slot access. Each array spans
  -- the 256-bit slot space. The next persistent declaration starts at 2^256,
  -- i.e. slot zero modulo 2^256, so all ordinary source slots stay unchanged.
  -- These are storage aliases, not memory arrays or allocation models.
  uint256[115792089237316195423570985008687907853269984665640564039457584007913129639936] rawSlots;
  uint256[115792089237316195423570985008687907853269984665640564039457584007913129639936] transient rawTransient;
  uint256 constant LOCK_SLOT = 0xc090fc4683624cfc3884e9d8de5eca132f2d0ec062aff75d43c0465d5ceeab23;
  uint256 constant COUNT_SLOT = 0x7d4b3164c6e45b97e7d87b7125a44c5828d005af88f9d751cfd78729c5d99a0b;
  uint256 constant CURRENCY_SLOT = 0x27e098c505d44ec3574004bca052aabf76bd35004c182099d8c575fb238593b9;
  uint256 constant RESERVES_SLOT = 0x1e0745a7db1623981f0b2a5d4232364c00787266eb75ad546f190e6cebe9bd95;
  address owner;
  mapping(address => uint256) protocolFeesAccrued;
  address protocolFeeController;
  address immutable original;
  mapping(address => mapping(address => bool)) isOperator;
  mapping(address => mapping(uint256 => uint256)) balanceOf;
  mapping(address => mapping(address => mapping(uint256 => uint256))) allowance;
  mapping(bytes32 => Pool_State) _pools;

  event ProtocolFeeControllerUpdated(address indexed protocolFeeController);
  event ProtocolFeeUpdated(bytes32 indexed id, uint24 protocolFee);
  event OperatorSet(address indexed owner, address indexed operator, bool approved);
  event Approval(address indexed owner, address indexed spender, uint256 indexed id, uint256 amount);
  event Transfer(address caller, address indexed «from», address indexed «to», uint256 indexed id, uint256 amount);
  event Initialize(bytes32 indexed id, address indexed currency0, address indexed currency1, uint24 fee, int24 tickSpacing, address hooks, uint160 sqrtPriceX96, int24 tick);
  event ModifyLiquidity(bytes32 indexed id, address indexed sender, int24 tickLower, int24 tickUpper, int256 liquidityDelta, bytes32 salt);
  event Swap(bytes32 indexed id, address indexed sender, int128 amount0, int128 amount1, uint160 sqrtPriceX96, uint128 liquidity, int24 tick, uint24 fee);
  event Donate(bytes32 indexed id, address indexed sender, uint256 amount0, uint256 amount1);
  event OwnershipTransferred(address indexed user, address indexed newOwner);

  constructor(address initialOwner) {
    address _owner = initialOwner;
    owner = _owner;
    emit OwnershipTransferred(address(0), _owner);
    address initialOwner = initialOwner;
    original = address(this);
  }

  function wordByte(uint256 word, uint256 index) internal returns (uint256) {
    return index < 32 ? ((word >>[uint256] ((31 - index) * 8)) &[uint256] 255) : 0;
  }

  function TickMath_logStep(uint256 r, int256 log2, uint256 bit, bool normalize) internal returns (uint256, int256) {
    r = uint256(r * r) >>[uint256] 127;
    uint256 f = r >>[uint256] 128;
    log2 = log2 |[int256] (int256(f) <<[int256] bit);
    if (normalize) { r = r >>[uint256] f; }
    return (r, log2);
  }

  function calldataWordAt(uint256 offset) internal returns (uint256) {
    bytes data = msg.data;
    uint256 word = 0;
    uint256 j = 0;
    while (j < 32) {
      word = word * 256;
      if (offset + j < data.length) {
        word = word + uint256(data[offset + j]);
      }
      j = j + 1;
    }
    return word;
  }

  function Lock_isUnlocked() internal returns (bool) {
    return rawTransient[LOCK_SLOT] != 0;
  }

  function CustomRevert_revertWith(bytes4 selector) internal {
    require(false);
  }

  function Lock_unlock() internal {
    rawTransient[LOCK_SLOT] = 1;
  }

  function NonzeroDeltaCount_read() internal returns (uint256) {
    return rawTransient[COUNT_SLOT];
  }

  function Lock_lock() internal {
    rawTransient[LOCK_SLOT] = 0;
  }

  function checkNotDelegateCall() internal {
    if (address(this) != original) {
      require(false);
    }
  }

  function CustomRevert_revertWith_bytes4_int24(bytes4 selector, int24 value) internal {
    require(false);
  }

  function CustomRevert_revertWith_bytes4_address_address(bytes4 selector, address value1, address value2) internal {
    require(false);
  }

  function CustomRevert_revertWith_bytes4_address(bytes4 selector, address addr) internal {
    require(false);
  }

  function LPFeeLibrary_getInitialLPFee(uint24 self) internal returns (uint24) {
    var __c0 = LPFeeLibrary_isDynamicFee(self);
    if (__c0) {
      return 0;
    }
    var __c1 = LPFeeLibrary_validate(self);
    return self;
  }

  function PoolIdLibrary_toId(PoolKey memory poolKey) internal returns (bytes32) {
    return keccak256(abi.encodePacked(uint256(uint160(poolKey.currency0)),
      uint256(uint160(poolKey.currency1)), uint256(poolKey.fee),
      uint256(uint256(int256(poolKey.tickSpacing))), uint256(uint160(poolKey.hooks))));
  }

  function Pool_initialize(Pool_State storage self, uint160 sqrtPriceX96, uint24 lpFee) internal returns (int24) {
    int24 tick = 0;
    var __c0 = Slot0Library_sqrtPriceX96(self.slot0);
    if (__c0 != 0) {
      require(false);
    }
    var __c1 = TickMath_getTickAtSqrtPrice(sqrtPriceX96);
    tick = __c1;
    var __c2 = bytes32(bytes32(0));
    var __c3 = Slot0Library_setSqrtPriceX96(__c2, sqrtPriceX96);
    var __c4 = Slot0Library_setTick(__c3, tick);
    var __c5 = Slot0Library_setLpFee(__c4, lpFee);
    self.slot0 = __c5;
    return tick;
  }

  function _getPool(bytes32 id) internal returns (Pool_State storage) {
    return _pools[id];
  }

  function Pool_checkPoolInitialized(Pool_State storage self) internal {
    var __c0 = Slot0Library_sqrtPriceX96(self.slot0);
    if (__c0 == 0) {
      require(false);
    }
  }

  function Pool_modifyLiquidity(Pool_State storage self, Pool_ModifyLiquidityParams memory params) internal returns (int256, int256) {
    int256 delta = 0;
    int256 feeDelta = 0;
    int128 liquidityDelta = params.liquidityDelta;
    int24 tickLower = params.tickLower;
    int24 tickUpper = params.tickUpper;
    var __c0 = Pool_checkTicks(tickLower, tickUpper);
    ModifyLiquidityState state = ModifyLiquidityState({flippedLower: false, liquidityGrossAfterLower: 0, flippedUpper: false, liquidityGrossAfterUpper: 0});
    if (liquidityDelta != 0) {
      var __c1 = Pool_updateTick(self, tickLower, liquidityDelta, false);
      state.flippedLower = __c1.0;
      state.liquidityGrossAfterLower = __c1.1;
      var __c2 = Pool_updateTick(self, tickUpper, liquidityDelta, true);
      state.flippedUpper = __c2.0;
      state.liquidityGrossAfterUpper = __c2.1;
      if (liquidityDelta >= 0) {
        var maxLiquidityPerTick = Pool_tickSpacingToMaxLiquidityPerTick(params.tickSpacing);
        if (state.liquidityGrossAfterLower > maxLiquidityPerTick) {
          require(false);
        }
        if (state.liquidityGrossAfterUpper > maxLiquidityPerTick) {
          require(false);
        }
      }
      if (state.flippedLower) {
        var __c4 = TickBitmap_flipTick(self.tickBitmap, tickLower, params.tickSpacing);
      }
      if (state.flippedUpper) {
        var __c5 = TickBitmap_flipTick(self.tickBitmap, tickUpper, params.tickSpacing);
      }
    }
    var __c6 = Pool_getFeeGrowthInside(self, tickLower, tickUpper);
    uint256 feeGrowthInside0X128 = __c6.0;
    uint256 feeGrowthInside1X128 = __c6.1;
    var __c7 = Position_get(self.positions, params.owner, tickLower, tickUpper, params.salt);
    Position_State storage position = __c7;
    var __c8 = Position_update(position, liquidityDelta, feeGrowthInside0X128, feeGrowthInside1X128);
    uint256 feesOwed0 = __c8.0;
    uint256 feesOwed1 = __c8.1;
    var __c9 = SafeCast_toInt128_uint256(feesOwed0);
    var __c10 = SafeCast_toInt128_uint256(feesOwed1);
    var __c11 = toBalanceDelta(__c9, __c10);
    feeDelta = __c11;
    if (liquidityDelta < 0) {
      if (state.flippedLower) {
        var __c12 = Pool_clearTick(self, tickLower);
      }
      if (state.flippedUpper) {
        var __c13 = Pool_clearTick(self, tickUpper);
      }
    }
    if (liquidityDelta != 0) {
      bytes32 _slot0 = self.slot0;
      var __c14 = Slot0Library_tick(_slot0);
      int24 tick = __c14;
      var __c15 = Slot0Library_sqrtPriceX96(_slot0);
      uint160 sqrtPriceX96 = __c15;
      if (tick < tickLower) {
        var __c16 = TickMath_getSqrtPriceAtTick(tickLower);
        var __c17 = TickMath_getSqrtPriceAtTick(tickUpper);
        var __c18 = SqrtPriceMath_getAmount0Delta(__c16, __c17, liquidityDelta);
        var __c19 = SafeCast_toInt128(__c18);
        var __c20 = toBalanceDelta(__c19, 0);
        delta = __c20;
      } else {
        if (tick < tickUpper) {
          var __c21 = TickMath_getSqrtPriceAtTick(tickUpper);
          var __c22 = SqrtPriceMath_getAmount0Delta(sqrtPriceX96, __c21, liquidityDelta);
          var __c23 = SafeCast_toInt128(__c22);
          var __c24 = TickMath_getSqrtPriceAtTick(tickLower);
          var __c25 = SqrtPriceMath_getAmount1Delta(__c24, sqrtPriceX96, liquidityDelta);
          var __c26 = SafeCast_toInt128(__c25);
          var __c27 = toBalanceDelta(__c23, __c26);
          delta = __c27;
          var __c28 = LiquidityMath_addDelta(self.liquidity, liquidityDelta);
          self.liquidity = __c28;
        } else {
          var __c29 = TickMath_getSqrtPriceAtTick(tickLower);
          var __c30 = TickMath_getSqrtPriceAtTick(tickUpper);
          var __c31 = SqrtPriceMath_getAmount1Delta(__c29, __c30, liquidityDelta);
          var __c32 = SafeCast_toInt128(__c31);
          var __c33 = toBalanceDelta(0, __c32);
          delta = __c33;
        }
      }
    }
    return (delta, feeDelta);
  }

  function SafeCast_toInt128(int256 x) internal returns (int128) {
    int128 y = 0;
    y = int128(x);
    if (y != x) {
      require(false);
    }
    return y;
  }

  function _accountPoolBalanceDelta(PoolKey memory key, int256 delta, address target) internal {
    var __c0 = BalanceDeltaLibrary_amount0(delta);
    var __c1 = _accountDelta(key.currency0, __c0, target);
    var __c2 = BalanceDeltaLibrary_amount1(delta);
    var __c3 = _accountDelta(key.currency1, __c2, target);
  }

  function _swap(Pool_State storage pool, bytes32 id, Pool_SwapParams memory params, address inputCurrency) internal returns (int256) {
    var __c0 = Pool_swap(pool, params);
    int256 delta = __c0.0;
    uint256 amountToProtocol = __c0.1;
    uint24 swapFee = __c0.2;
    SwapResult result = __c0.3;
    if (amountToProtocol > 0) {
      var __c1 = _updateProtocolFees(inputCurrency, amountToProtocol);
    }
    var __c2 = BalanceDeltaLibrary_amount0(delta);
    var __c3 = BalanceDeltaLibrary_amount1(delta);
    emit Swap(id, msg.sender, __c2, __c3, result.sqrtPriceX96, result.liquidity, result.tick, swapFee);
    return delta;
  }

  function Pool_donate(Pool_State storage state, uint256 amount0, uint256 amount1) internal returns (int256) {
    int256 delta = 0;
    uint128 liquidity = state.liquidity;
    if (liquidity == 0) {
      require(false);
    }
    var __c0 = SafeCast_toInt128_uint256(amount0);
    var __c1 = SafeCast_toInt128_uint256(amount1);
    var __c2 = toBalanceDelta(int128(0 - __c0), int128(0 - __c1));
    delta = __c2;
    if (amount0 > 0) {
      var __c3 = UnsafeMath_simpleMulDiv(amount0, (340282366920938463463374607431768211456), liquidity);
      state.feeGrowthGlobal0X128 = uint256(state.feeGrowthGlobal0X128 + __c3);
    }
    if (amount1 > 0) {
      var __c4 = UnsafeMath_simpleMulDiv(amount1, (340282366920938463463374607431768211456), liquidity);
      state.feeGrowthGlobal1X128 = uint256(state.feeGrowthGlobal1X128 + __c4);
    }
    return delta;
  }

  function CurrencyLibrary_isAddressZero(address currency) internal returns (bool) {
    return currency == address(0);
  }

  function CurrencyReserves_resetCurrency() internal {
    rawTransient[CURRENCY_SLOT] = 0;
  }

  function CurrencyLibrary_balanceOfSelf(address currency) internal returns (uint256) {
    var __c0 = CurrencyLibrary_isAddressZero(currency);
    if (__c0) {
      return address(this).balance;
    } else {
      var __c1 = address(currency);
      var __c2 = __c1.balanceOf{view}(address(this));
      return __c2;
    }
  }

  function CurrencyReserves_syncCurrencyAndReserves(address currency, uint256 value) internal {
    rawTransient[CURRENCY_SLOT] = uint256(uint160(currency));
    rawTransient[RESERVES_SLOT] = value;
  }

  function _accountDelta(address currency, int128 delta, address target) internal {
    if (delta == 0) {
      return;
    }
    var __c0 = CurrencyDelta_applyDelta(currency, target, delta);
    int256 previous = __c0.0;
    int256 next = __c0.1;
    if (next == 0) {
      var __c1 = NonzeroDeltaCount_decrement();
    } else {
      if (previous == 0) {
        var __c2 = NonzeroDeltaCount_increment();
      }
    }
  }

  function SafeCast_toInt128_uint256(uint256 x) internal returns (int128) {
    if (x >= (1 <<[uint256] 127)) {
      require(false);
    }
    return int128(int256(x));
  }

  function BalanceDelta_add(int256 a, int256 b) internal returns (int256) {
    var amount0 = SafeCast_toInt128(int128(a >>[int256] 128) + int128(b >>[int256] 128));
    var amount1 = SafeCast_toInt128(int128(a) + int128(b));
    var result = toBalanceDelta(amount0, amount1);
    return result;
  }

  function BalanceDelta_sub(int256 a, int256 b) internal returns (int256) {
    var amount0 = SafeCast_toInt128(int128(a >>[int256] 128) - int128(b >>[int256] 128));
    var amount1 = SafeCast_toInt128(int128(a) - int128(b));
    var result = toBalanceDelta(amount0, amount1);
    return result;
  }

  function Hooks_isValidHookAddress(address self, uint24 fee) internal returns (bool) {
    uint160 flags = uint160(self);
    if ((flags &[uint160] 128) == 0 && (flags &[uint160] 8) != 0) { return false; }
    if ((flags &[uint160] 64) == 0 && (flags &[uint160] 4) != 0) { return false; }
    if ((flags &[uint160] 1024) == 0 && (flags &[uint160] 2) != 0) { return false; }
    if ((flags &[uint160] 256) == 0 && (flags &[uint160] 1) != 0) { return false; }
    return self == address(0) ? fee != 8388608 : (flags &[uint160] 16383) != 0 || fee == 8388608;
  }

  function Hooks_callHook(address self, bytes data) internal returns (bytes) {
    (bool success, bytes result) = self.call(data);
    require(success);
    require(result.length >= 32);
    require(result[0 : 4] == data[0 : 4]);
    return result;
  }

  function Hooks_callHookWithReturnDelta(address self, bytes data, bool parseReturn) internal returns (int256) {
    var result = Hooks_callHook(self, data);
    if (!(parseReturn)) { return 0; }
    require(result.length == 64);
    return abi.decode(result[32 : 64], (int256));
  }

  function Hooks_beforeInitialize(address self, PoolKey key, uint160 sqrtPriceX96) internal {
    if (msg.sender != self && (uint160(self) &[uint160] 8192) != 0) {
      bytes payload = abi.encodeWithSelector(beforeInitialize, msg.sender, tuple(key.currency0, key.currency1, key.fee, key.tickSpacing, key.hooks), sqrtPriceX96);
      var ignored = Hooks_callHook(self, payload);
    }
  }

  function Hooks_afterInitialize(address self, PoolKey key, uint160 sqrtPriceX96, int24 tick) internal {
    if (msg.sender != self && (uint160(self) &[uint160] 4096) != 0) {
      bytes payload = abi.encodeWithSelector(afterInitialize, msg.sender, tuple(key.currency0, key.currency1, key.fee, key.tickSpacing, key.hooks), sqrtPriceX96, tick);
      var ignored = Hooks_callHook(self, payload);
    }
  }

  function Hooks_beforeModifyLiquidity(address self, PoolKey key, ModifyLiquidityParams_8903 params, bytes hookData) internal {
    if (msg.sender == self) { return; }
    if (params.liquidityDelta > 0 && (uint160(self) &[uint160] 2048) != 0) {
      bytes payload = abi.encodeWithSelector(beforeAddLiquidity, msg.sender, tuple(key.currency0, key.currency1, key.fee, key.tickSpacing, key.hooks), tuple(params.tickLower, params.tickUpper, params.liquidityDelta, params.salt), hookData);
      var ignored = Hooks_callHook(self, payload);
    } else {
      if (params.liquidityDelta <= 0 && (uint160(self) &[uint160] 512) != 0) {
        bytes payload = abi.encodeWithSelector(beforeRemoveLiquidity, msg.sender, tuple(key.currency0, key.currency1, key.fee, key.tickSpacing, key.hooks), tuple(params.tickLower, params.tickUpper, params.liquidityDelta, params.salt), hookData);
        var ignored = Hooks_callHook(self, payload);
      }
    }
  }

  function Hooks_afterModifyLiquidity(address self, PoolKey key, ModifyLiquidityParams_8903 params, int256 delta, int256 feesAccrued, bytes hookData) internal returns (int256, int256) {
    if (msg.sender == self) { return (delta, 0); }
    int256 hookDelta = 0;
    int256 callerDelta = delta;
    if (params.liquidityDelta > 0) {
      if ((uint160(self) &[uint160] 1024) != 0) {
        bytes payload = abi.encodeWithSelector(afterAddLiquidity, msg.sender, tuple(key.currency0, key.currency1, key.fee, key.tickSpacing, key.hooks), tuple(params.tickLower, params.tickUpper, params.liquidityDelta, params.salt), delta, feesAccrued, hookData);
        var result = Hooks_callHookWithReturnDelta(self, payload, (uint160(self) &[uint160] 2) != 0);
        hookDelta = result;
        var remaining = BalanceDelta_sub(callerDelta, hookDelta);
        callerDelta = remaining;
      }
    } else {
      if ((uint160(self) &[uint160] 256) != 0) {
        bytes payload = abi.encodeWithSelector(afterRemoveLiquidity, msg.sender, tuple(key.currency0, key.currency1, key.fee, key.tickSpacing, key.hooks), tuple(params.tickLower, params.tickUpper, params.liquidityDelta, params.salt), delta, feesAccrued, hookData);
        var result = Hooks_callHookWithReturnDelta(self, payload, (uint160(self) &[uint160] 1) != 0);
        hookDelta = result;
        var remaining = BalanceDelta_sub(callerDelta, hookDelta);
        callerDelta = remaining;
      }
    }
    return (callerDelta, hookDelta);
  }

  function Hooks_beforeSwap(address self, PoolKey key, SwapParams_8914 params, bytes hookData) internal returns (int256, int256, uint24) {
    int256 amountToSwap = params.amountSpecified;
    int256 hookReturn = 0;
    uint24 lpFeeOverride = 0;
    if (msg.sender == self) { return (amountToSwap, 0, 0); }
    if ((uint160(self) &[uint160] 128) != 0) {
      bytes payload = abi.encodeWithSelector(beforeSwap, msg.sender, tuple(key.currency0, key.currency1, key.fee, key.tickSpacing, key.hooks), tuple(params.zeroForOne, params.amountSpecified, params.sqrtPriceLimitX96), hookData);
      var result = Hooks_callHook(self, payload);
      require(result.length == 96);
      if (key.fee == 8388608) { lpFeeOverride = uint24(abi.decode(result[64 : 96], (uint256))); }
      if ((uint160(self) &[uint160] 8) != 0) {
        hookReturn = abi.decode(result[32 : 64], (int256));
        int128 hookDeltaSpecified = int128(hookReturn >>[int256] 128);
        if (hookDeltaSpecified != 0) {
          bool exactInput = amountToSwap < 0;
          amountToSwap = (amountToSwap + hookDeltaSpecified) as int256;
          require(exactInput ? amountToSwap <= 0 : amountToSwap >= 0);
        }
      }
    }
    return (amountToSwap, hookReturn, lpFeeOverride);
  }

  function Hooks_afterSwap(address self, PoolKey key, SwapParams_8914 params, int256 swapDelta, bytes hookData, int256 beforeSwapHookReturn) internal returns (int256, int256) {
    if (msg.sender == self) { return (swapDelta, 0); }
    int128 specified = int128(beforeSwapHookReturn >>[int256] 128);
    int128 unspecified = int128(beforeSwapHookReturn);
    if ((uint160(self) &[uint160] 64) != 0) {
      bytes payload = abi.encodeWithSelector(afterSwap, msg.sender, tuple(key.currency0, key.currency1, key.fee, key.tickSpacing, key.hooks), tuple(params.zeroForOne, params.amountSpecified, params.sqrtPriceLimitX96), swapDelta, hookData);
      var result = Hooks_callHookWithReturnDelta(self, payload, (uint160(self) &[uint160] 4) != 0);
      var delta = SafeCast_toInt128(result);
      unspecified = (unspecified + delta) as int128;
    }
    int256 hookDelta = 0;
    if (unspecified != 0 || specified != 0) {
      if ((params.amountSpecified < 0) == params.zeroForOne) {
        var packed = toBalanceDelta(specified, unspecified);
        hookDelta = packed;
      } else {
        var packed = toBalanceDelta(unspecified, specified);
        hookDelta = packed;
      }
      var remaining = BalanceDelta_sub(swapDelta, hookDelta);
      swapDelta = remaining;
    }
    return (swapDelta, hookDelta);
  }

  function Hooks_beforeDonate(address self, PoolKey key, uint256 amount0, uint256 amount1, bytes hookData) internal {
    if (msg.sender != self && (uint160(self) &[uint160] 32) != 0) {
      bytes payload = abi.encodeWithSelector(beforeDonate, msg.sender, tuple(key.currency0, key.currency1, key.fee, key.tickSpacing, key.hooks), amount0, amount1, hookData);
      var ignored = Hooks_callHook(self, payload);
    }
  }

  function Hooks_afterDonate(address self, PoolKey key, uint256 amount0, uint256 amount1, bytes hookData) internal {
    if (msg.sender != self && (uint160(self) &[uint160] 16) != 0) {
      bytes payload = abi.encodeWithSelector(afterDonate, msg.sender, tuple(key.currency0, key.currency1, key.fee, key.tickSpacing, key.hooks), amount0, amount1, hookData);
      var ignored = Hooks_callHook(self, payload);
    }
  }

  function CurrencyLibrary_transfer(address currency, address «to», uint256 amount) internal {
    if (currency == address(0)) {
      (bool success, bytes returned) = «to».call{value: amount}("");
      require(success);
    } else {
      bytes payload = abi.encodePacked(bytes4(bytes4(0xa9059cbb)), uint256(uint160(«to»)), uint256(amount));
      (bool success, bytes returned) = currency.call(payload);
      bool validReturn = returned.length == 0;
      if (returned.length > 31) {
        validReturn = abi.decode(returned[0 : 32], (uint256)) == 1;
      }
      require(validReturn && success);
    }
  }

  function _settle(address recipient) internal returns (uint256) {
    uint256 paid = 0;
    var currency = CurrencyReserves_getSyncedCurrency();
    var __c1 = CurrencyLibrary_isAddressZero(currency);
    if (__c1) {
      paid = msg.value;
    } else {
      if (msg.value > 0) {
        require(false);
      }
      var reservesBefore = CurrencyReserves_getSyncedReserves();
      var reservesNow = CurrencyLibrary_balanceOfSelf(currency);
      paid = (reservesNow - reservesBefore) as uint256;
      var __c4 = CurrencyReserves_resetCurrency();
    }
    var __c5 = SafeCast_toInt128_uint256(paid);
    var __c6 = _accountDelta(currency, __c5, recipient);
    return paid;
  }

  function CurrencyDelta_getDelta(address currency, address target) internal returns (int256) {
    var hashSlot = CurrencyDelta__computeSlot(target, currency);
    return int256(rawTransient[uint256(hashSlot)]);
  }

  function CurrencyLibrary_fromId(uint256 id) internal returns (address) {
    var __c0 = address(address(uint160(id)));
    return __c0;
  }

  function _mint(address receiver, uint256 id, uint256 amount) internal {
    balanceOf[receiver][id] = ((balanceOf[receiver][id] + amount) as uint256);
    emit Transfer(msg.sender, address(0), receiver, id, amount);
  }

  function CurrencyLibrary_toId(address currency) internal returns (uint256) {
    var __c0 = address(currency);
    return uint160(__c0);
  }

  function _burnFrom(address «from», uint256 id, uint256 amount) internal {
    address sender = msg.sender;
    if ((«from» != sender) && !(isOperator[«from»][sender])) {
      uint256 senderAllowance = allowance[«from»][sender][id];
      if (senderAllowance != type(uint256).max) {
        allowance[«from»][sender][id] = (senderAllowance - amount) as uint256;
      }
    }
    var __c0 = _burn(«from», id, amount);
  }

  function LPFeeLibrary_isDynamicFee(uint24 self) internal returns (bool) {
    return self == 8388608;
  }

  function LPFeeLibrary_validate(uint24 self) internal {
    var __c0 = LPFeeLibrary_isValid(self);
    if (!(__c0)) {
      require(false);
    }
  }

  function Pool_setLPFee(Pool_State storage self, uint24 lpFee) internal {
    var __c0 = Pool_checkPoolInitialized(self);
    var __c1 = Slot0Library_setLpFee(self.slot0, lpFee);
    self.slot0 = __c1;
  }

  function ProtocolFeeLibrary_isValidProtocolFee(uint24 self) internal returns (bool) {
    return (self &[uint24] 4095) < 1001 && (self &[uint24] 16773120) < 4100096;
  }

  function CustomRevert_revertWith_bytes4_uint160(bytes4 selector, uint160 value) internal {
    require(false);
  }

  function Pool_setProtocolFee(Pool_State storage self, uint24 protocolFee) internal {
    var __c0 = Pool_checkPoolInitialized(self);
    var __c1 = Slot0Library_setProtocolFee(self.slot0, protocolFee);
    self.slot0 = __c1;
  }

  function CurrencyReserves_getSyncedCurrency() internal returns (address) {
    return address(rawTransient[CURRENCY_SLOT]);
  }

  function Slot0Library_sqrtPriceX96(bytes32 _packed) internal returns (uint160) {
    return uint160(uint256(_packed));
  }

  function TickMath_getTickAtSqrtPrice(uint160 sqrtPriceX96) internal returns (int24) {
    int24 tick = 0;
    if ((uint160(sqrtPriceX96 - 4295128739)) > (((((1461446703485210103287273052203988822378723970342 - 4295128739) as uint256) - 1) as uint256))) {
      require(false);
    }
    uint256 price = uint256(sqrtPriceX96) <<[uint256] 32;
    uint256 r = price;
    var msb = BitMath_mostSignificantBit(r);
    if (msb >= 128) {
      r = price >>[uint256] (uint256(msb - 127));
    } else {
      r = price <<[uint256] (uint256(127 - msb));
    }
    int256 log_2 = (int256(int256(msb) - 128)) <<[int256] 64;
    var logStep0 = TickMath_logStep(r, log_2, 63, true);
    r = logStep0.0;
    log_2 = logStep0.1;
    var logStep1 = TickMath_logStep(r, log_2, 62, true);
    r = logStep1.0;
    log_2 = logStep1.1;
    var logStep2 = TickMath_logStep(r, log_2, 61, true);
    r = logStep2.0;
    log_2 = logStep2.1;
    var logStep3 = TickMath_logStep(r, log_2, 60, true);
    r = logStep3.0;
    log_2 = logStep3.1;
    var logStep4 = TickMath_logStep(r, log_2, 59, true);
    r = logStep4.0;
    log_2 = logStep4.1;
    var logStep5 = TickMath_logStep(r, log_2, 58, true);
    r = logStep5.0;
    log_2 = logStep5.1;
    var logStep6 = TickMath_logStep(r, log_2, 57, true);
    r = logStep6.0;
    log_2 = logStep6.1;
    var logStep7 = TickMath_logStep(r, log_2, 56, true);
    r = logStep7.0;
    log_2 = logStep7.1;
    var logStep8 = TickMath_logStep(r, log_2, 55, true);
    r = logStep8.0;
    log_2 = logStep8.1;
    var logStep9 = TickMath_logStep(r, log_2, 54, true);
    r = logStep9.0;
    log_2 = logStep9.1;
    var logStep10 = TickMath_logStep(r, log_2, 53, true);
    r = logStep10.0;
    log_2 = logStep10.1;
    var logStep11 = TickMath_logStep(r, log_2, 52, true);
    r = logStep11.0;
    log_2 = logStep11.1;
    var logStep12 = TickMath_logStep(r, log_2, 51, true);
    r = logStep12.0;
    log_2 = logStep12.1;
    var logStep13 = TickMath_logStep(r, log_2, 50, false);
    r = logStep13.0;
    log_2 = logStep13.1;
    int256 log_sqrt10001 = int256(log_2 * 255738958999603826347141);
    int24 tickLow = int24(((int256(log_sqrt10001 - 3402992956809132418596140100660247210)) >>[int256] 128));
    int24 tickHi = int24(((int256(log_sqrt10001 + 291339464771989622907027621153398088495)) >>[int256] 128));
    tick = tickLow;
    if (tickLow != tickHi) {
      var priceHi = TickMath_getSqrtPriceAtTick(tickHi);
      tick = priceHi <= sqrtPriceX96 ? tickHi : tickLow;
    }
    return tick;
  }

  function Slot0Library_setLpFee(bytes32 _packed, uint24 _lpFee) internal returns (bytes32) {
    uint256 cleared = uint256(_packed) &[uint256] 115792082335570260009146527875442584318540171552157837553037437240354742992895;
    return bytes32(cleared |[uint256] (uint256(uint24(_lpFee)) <<[uint256] 208));
  }

  function Slot0Library_setTick(bytes32 _packed, int24 _tick) internal returns (bytes32) {
    uint256 cleared = uint256(_packed) &[uint256] 115792089237316195423546465081495555268867154031409843925235967201614124548095;
    return bytes32(cleared |[uint256] (uint256(uint24(_tick)) <<[uint256] 160));
  }

  function Slot0Library_setSqrtPriceX96(bytes32 _packed, uint160 _sqrtPriceX96) internal returns (bytes32) {
    uint256 cleared = uint256(_packed) &[uint256] 115792089237316195423570985007226406215939081747436879206741300988257197096960;
    return bytes32(cleared |[uint256] (uint256(uint160(_sqrtPriceX96)) <<[uint256] 0));
  }

  function Pool_checkTicks(int24 tickLower, int24 tickUpper) internal {
    if (tickLower >= tickUpper) {
      require(false);
    }
    if (tickLower < -887272) {
      require(false);
    }
    if (tickUpper > 887272) {
      require(false);
    }
  }

  function Pool_updateTick(Pool_State storage self, int24 tick, int128 liquidityDelta, bool upper) internal returns (bool, uint128) {
    bool flipped = false;
    uint128 liquidityGrossAfter = 0;
    TickInfo storage info = self.ticks[tick];
    uint256 liquidityPacked = info.liquidityPacked;
    uint128 liquidityGrossBefore = uint128(liquidityPacked);
    int128 liquidityNetBefore = int128(liquidityPacked >>[uint256] 128);
    var __c0 = LiquidityMath_addDelta(liquidityGrossBefore, liquidityDelta);
    liquidityGrossAfter = __c0;
    flipped = (liquidityGrossAfter == 0) != (liquidityGrossBefore == 0);
    if (liquidityGrossBefore == 0) {
      var __c1 = Slot0Library_tick(self.slot0);
      if (tick <= __c1) {
        info.feeGrowthOutside0X128 = self.feeGrowthGlobal0X128;
        info.feeGrowthOutside1X128 = self.feeGrowthGlobal1X128;
      }
    }
    int128 liquidityNet = upper ? ((liquidityNetBefore - liquidityDelta) as int128) : ((liquidityNetBefore + liquidityDelta) as int128);
    info.liquidityPacked = uint256(liquidityGrossAfter) |[uint256] (uint256(uint128(liquidityNet)) <<[uint256] 128);
    return (flipped, liquidityGrossAfter);
  }

  function Pool_tickSpacingToMaxLiquidityPerTick(int24 tickSpacing) internal returns (uint128) {
    int256 minTick = 0;
    int256 maxTick = 0;
    if (tickSpacing != 0) {
      minTick = sdiv(-887272, tickSpacing) - (srem(-887272, tickSpacing) < 0 ? 1 : 0);
      maxTick = sdiv(887272, tickSpacing);
    }
    uint256 numTicks = uint256(maxTick - minTick + 1);
    return numTicks == 0 ? 0 : uint128(type(uint128).max / numTicks);
  }

  function TickBitmap_flipTick(mapping(int16 => uint256) storage self, int24 tick, int24 tickSpacing) internal {
    int256 compressed = 0;
    if (tickSpacing != 0) {
      require(srem(tick, tickSpacing) == 0);
      compressed = sdiv(tick, tickSpacing);
    }
    int16 wordPos = int16(compressed >>[int256] 8);
    uint256 mask = 1 <<[uint256] uint8(compressed);
    self[wordPos] = self[wordPos] ^[uint256] mask;
  }

  function Pool_getFeeGrowthInside(Pool_State storage self, int24 tickLower, int24 tickUpper) internal returns (uint256, uint256) {
    uint256 feeGrowthInside0X128 = 0;
    uint256 feeGrowthInside1X128 = 0;
    TickInfo storage lower = self.ticks[tickLower];
    TickInfo storage upper = self.ticks[tickUpper];
    var tickCurrent = Slot0Library_tick(self.slot0);
    if (tickCurrent < tickLower) {
      feeGrowthInside0X128 = uint256(lower.feeGrowthOutside0X128 - upper.feeGrowthOutside0X128);
      feeGrowthInside1X128 = uint256(lower.feeGrowthOutside1X128 - upper.feeGrowthOutside1X128);
    } else {
      if (tickCurrent >= tickUpper) {
        feeGrowthInside0X128 = uint256(upper.feeGrowthOutside0X128 - lower.feeGrowthOutside0X128);
        feeGrowthInside1X128 = uint256(upper.feeGrowthOutside1X128 - lower.feeGrowthOutside1X128);
      } else {
        feeGrowthInside0X128 = uint256(uint256(self.feeGrowthGlobal0X128 - lower.feeGrowthOutside0X128) - upper.feeGrowthOutside0X128);
        feeGrowthInside1X128 = uint256(uint256(self.feeGrowthGlobal1X128 - lower.feeGrowthOutside1X128) - upper.feeGrowthOutside1X128);
      }
    }
    return (feeGrowthInside0X128, feeGrowthInside1X128);
  }

  function Position_get(mapping(bytes32 => Position_State) storage self, address owner, int24 tickLower, int24 tickUpper, bytes32 salt) internal returns (Position_State storage) {
    var positionKey = Position_calculatePositionKey(owner, tickLower, tickUpper, salt);
    Position_State storage position = self[positionKey];
    return position;
  }

  function Position_update(Position_State storage self, int128 liquidityDelta, uint256 feeGrowthInside0X128, uint256 feeGrowthInside1X128) internal returns (uint256, uint256) {
    uint256 feesOwed0 = 0;
    uint256 feesOwed1 = 0;
    uint128 liquidity = self.liquidity;
    if (liquidityDelta == 0) {
      if (liquidity == 0) {
        require(false);
      }
    } else {
      var __c0 = LiquidityMath_addDelta(liquidity, liquidityDelta);
      self.liquidity = __c0;
    }
    var __c1 = FullMath_mulDiv(uint256(feeGrowthInside0X128 - self.feeGrowthInside0LastX128), liquidity, (340282366920938463463374607431768211456));
    feesOwed0 = __c1;
    var __c2 = FullMath_mulDiv(uint256(feeGrowthInside1X128 - self.feeGrowthInside1LastX128), liquidity, (340282366920938463463374607431768211456));
    feesOwed1 = __c2;
    self.feeGrowthInside0LastX128 = feeGrowthInside0X128;
    self.feeGrowthInside1LastX128 = feeGrowthInside1X128;
    return (feesOwed0, feesOwed1);
  }

  function toBalanceDelta(int128 _amount0, int128 _amount1) internal returns (int256) {
    return (int256(_amount0) <<[int256] 128) |[int256] int256(uint128(_amount1));
  }

  function Pool_clearTick(Pool_State storage self, int24 tick) internal {
    delete self.ticks[tick];
  }

  function Slot0Library_tick(bytes32 _packed) internal returns (int24) {
    return int24(uint256(_packed) >>[uint256] 160);
  }

  function SqrtPriceMath_getAmount0Delta(uint160 sqrtPriceAX96, uint160 sqrtPriceBX96, int128 liquidity) internal returns (int256) {
    if (liquidity < 0) {
      var amount = SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool(sqrtPriceAX96, sqrtPriceBX96, uint128(int128(0 - liquidity)), false);
      var result = SafeCast_toInt256(amount);
      return result;
    } else {
      var amount = SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool(sqrtPriceAX96, sqrtPriceBX96, uint128(liquidity), true);
      var result = SafeCast_toInt256(amount);
      return int256(0 - result);
    }
  }

  function TickMath_getSqrtPriceAtTick(int24 tick) internal returns (uint160) {
    uint160 sqrtPriceX96 = 0;
    uint256 absTick = 0;
    absTick = uint256(tick < 0 ? 0 - tick : tick);
    if (absTick > uint256(int256(887272))) {
      require(false);
    }
    uint256 price = 0;
    price = (absTick &[uint256] 1) != 0 ? 0xfffcb933bd6fad37aa2d162d1a594001 : (1 <<[uint256] 128);
    if ((absTick &[uint256] 2) != 0) {
      price = (uint256(price * 340248342086729790484326174814286782778)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 4) != 0) {
      price = (uint256(price * 340214320654664324051920982716015181260)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 8) != 0) {
      price = (uint256(price * 340146287995602323631171512101879684304)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 16) != 0) {
      price = (uint256(price * 340010263488231146823593991679159461444)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 32) != 0) {
      price = (uint256(price * 339738377640345403697157401104375502016)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 64) != 0) {
      price = (uint256(price * 339195258003219555707034227454543997025)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 128) != 0) {
      price = (uint256(price * 338111622100601834656805679988414885971)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 256) != 0) {
      price = (uint256(price * 335954724994790223023589805789778977700)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 512) != 0) {
      price = (uint256(price * 331682121138379247127172139078559817300)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 1024) != 0) {
      price = (uint256(price * 323299236684853023288211250268160618739)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 2048) != 0) {
      price = (uint256(price * 307163716377032989948697243942600083929)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 4096) != 0) {
      price = (uint256(price * 277268403626896220162999269216087595045)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 8192) != 0) {
      price = (uint256(price * 225923453940442621947126027127485391333)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 16384) != 0) {
      price = (uint256(price * 149997214084966997727330242082538205943)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 32768) != 0) {
      price = (uint256(price * 66119101136024775622716233608466517926)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 65536) != 0) {
      price = (uint256(price * 12847376061809297530290974190478138313)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 131072) != 0) {
      price = (uint256(price * 485053260817066172746253684029974020)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 262144) != 0) {
      price = (uint256(price * 691415978906521570653435304214168)) >>[uint256] 128;
    }
    if ((absTick &[uint256] 524288) != 0) {
      price = (uint256(price * 1404880482679654955896180642)) >>[uint256] 128;
    }
    if (tick > 0) { price = type(uint256).max / price; }
    sqrtPriceX96 = uint160(uint256(price + type(uint32).max) >>[uint256] 32);
    return sqrtPriceX96;
  }

  function SqrtPriceMath_getAmount1Delta(uint160 sqrtPriceAX96, uint160 sqrtPriceBX96, int128 liquidity) internal returns (int256) {
    if (liquidity < 0) {
      var amount = SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool(sqrtPriceAX96, sqrtPriceBX96, uint128(int128(0 - liquidity)), false);
      var result = SafeCast_toInt256(amount);
      return result;
    } else {
      var amount = SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool(sqrtPriceAX96, sqrtPriceBX96, uint128(liquidity), true);
      var result = SafeCast_toInt256(amount);
      return int256(0 - result);
    }
  }

  function LiquidityMath_addDelta(uint128 x, int128 y) internal returns (uint128) {
    uint128 z = 0;
    z = (x + y) as uint128;
    return z;
  }

  function BalanceDeltaLibrary_amount0(int256 balanceDelta) internal returns (int128) {
    return int128(balanceDelta >>[int256] 128);
  }

  function BalanceDeltaLibrary_amount1(int256 balanceDelta) internal returns (int128) {
    return int128(balanceDelta);
  }

  function Pool_swap(Pool_State storage self, Pool_SwapParams memory params) internal returns (int256, uint256, uint24, SwapResult) {
    int256 swapDelta = 0;
    uint256 amountToProtocol = 0;
    uint24 swapFee = 0;
    SwapResult result = SwapResult({sqrtPriceX96: 0, tick: 0, liquidity: 0});
    bytes32 slot0Start = self.slot0;
    bool zeroForOne = params.zeroForOne;
    var __c0 = Slot0Library_protocolFee(slot0Start);
    var __c1 = ProtocolFeeLibrary_getZeroForOneFee(__c0);
    var __c2 = Slot0Library_protocolFee(slot0Start);
    var __c3 = ProtocolFeeLibrary_getOneForZeroFee(__c2);
    uint256 protocolFee = zeroForOne ? __c1 : __c3;
    int256 amountSpecifiedRemaining = params.amountSpecified;
    int256 amountCalculated = 0;
    var __c4 = Slot0Library_sqrtPriceX96(slot0Start);
    result.sqrtPriceX96 = __c4;
    var __c5 = Slot0Library_tick(slot0Start);
    result.tick = __c5;
    result.liquidity = self.liquidity;
    var __c6 = LPFeeLibrary_isOverride(params.lpFeeOverride);
    uint24 lpFee = 0;
    if (__c6) {
      var overrideFee = LPFeeLibrary_removeOverrideFlagAndValidate(params.lpFeeOverride);
      lpFee = overrideFee;
    } else {
      var storedFee = Slot0Library_lpFee(slot0Start);
      lpFee = storedFee;
    }
    var __c9 = ProtocolFeeLibrary_calculateSwapFee(uint16(protocolFee), lpFee);
    swapFee = (protocolFee == 0) ? lpFee : __c9;
    if (swapFee >= 1000000) {
      if (params.amountSpecified > 0) {
        require(false);
      }
    }
    if (params.amountSpecified == 0) {
      return (0, 0, swapFee, result);
    }
    if (zeroForOne) {
      var __c10 = Slot0Library_sqrtPriceX96(slot0Start);
      if (params.sqrtPriceLimitX96 >= __c10) {
        require(false);
      }
      if (params.sqrtPriceLimitX96 <= 4295128739) {
        require(false);
      }
    } else {
      var __c11 = Slot0Library_sqrtPriceX96(slot0Start);
      if (params.sqrtPriceLimitX96 <= __c11) {
        require(false);
      }
      if (params.sqrtPriceLimitX96 >= (1461446703485210103287273052203988822378723970342)) {
        require(false);
      }
    }
    StepComputations step = StepComputations({sqrtPriceStartX96: 0, tickNext: 0, initialized: false, sqrtPriceNextX96: 0, amountIn: 0, amountOut: 0, feeAmount: 0, feeGrowthGlobalX128: 0});
    step.feeGrowthGlobalX128 = zeroForOne ? self.feeGrowthGlobal0X128 : self.feeGrowthGlobal1X128;
    while (!(((amountSpecifiedRemaining == 0) || (result.sqrtPriceX96 == params.sqrtPriceLimitX96)))) {
      step.sqrtPriceStartX96 = result.sqrtPriceX96;
      var __c12 = TickBitmap_nextInitializedTickWithinOneWord(self.tickBitmap, result.tick, params.tickSpacing, zeroForOne);
      step.tickNext = __c12.0;
      step.initialized = __c12.1;
      if (step.tickNext <= -887272) {
        step.tickNext = -887272;
      }
      if (step.tickNext >= 887272) {
        step.tickNext = 887272;
      }
      var __c13 = TickMath_getSqrtPriceAtTick(step.tickNext);
      step.sqrtPriceNextX96 = __c13;
      var __c14 = SwapMath_getSqrtPriceTarget(zeroForOne, step.sqrtPriceNextX96, params.sqrtPriceLimitX96);
      var __c15 = SwapMath_computeSwapStep(result.sqrtPriceX96, __c14, result.liquidity, amountSpecifiedRemaining, swapFee);
      result.sqrtPriceX96 = __c15.0;
      step.amountIn = __c15.1;
      step.amountOut = __c15.2;
      step.feeAmount = __c15.3;
      if (params.amountSpecified > 0) {
        var __c16 = SafeCast_toInt256(step.amountOut);
        amountSpecifiedRemaining = int256(amountSpecifiedRemaining - __c16);
        var __c17 = SafeCast_toInt256(((step.amountIn + step.feeAmount) as uint256));
        amountCalculated = ((amountCalculated - __c17) as int256);
      } else {
        var __c18 = SafeCast_toInt256((uint256(step.amountIn + step.feeAmount)));
        amountSpecifiedRemaining = int256(amountSpecifiedRemaining + __c18);
        var __c19 = SafeCast_toInt256(step.amountOut);
        amountCalculated = ((amountCalculated + __c19) as int256);
      }
      if (protocolFee > 0) {
        uint256 delta = (swapFee == protocolFee) ? step.feeAmount : (uint256((uint256(step.amountIn + step.feeAmount)) * protocolFee) / 1000000);
        step.feeAmount = uint256(step.feeAmount - delta);
        amountToProtocol = uint256(amountToProtocol + delta);
      }
      if (result.liquidity > 0) {
        var __c20 = UnsafeMath_simpleMulDiv(step.feeAmount, (340282366920938463463374607431768211456), result.liquidity);
        step.feeGrowthGlobalX128 = uint256(step.feeGrowthGlobalX128 + __c20);
      }
      if (result.sqrtPriceX96 == step.sqrtPriceNextX96) {
        if (step.initialized) {
          uint256 feeGrowthGlobal0X128 = zeroForOne ? step.feeGrowthGlobalX128 : self.feeGrowthGlobal0X128;
          uint256 feeGrowthGlobal1X128 = zeroForOne ? self.feeGrowthGlobal1X128 : step.feeGrowthGlobalX128;
          var liquidityNet = Pool_crossTick(self, step.tickNext, feeGrowthGlobal0X128, feeGrowthGlobal1X128);
          if (zeroForOne) {
            liquidityNet = int128(0 - liquidityNet);
          }
          var __c22 = LiquidityMath_addDelta(result.liquidity, liquidityNet);
          result.liquidity = __c22;
        }
        result.tick = zeroForOne ? int24(step.tickNext - 1) : step.tickNext;
      } else {
        if (result.sqrtPriceX96 != step.sqrtPriceStartX96) {
          var __c23 = TickMath_getTickAtSqrtPrice(result.sqrtPriceX96);
          result.tick = __c23;
        }
      }
    }
    var __c24 = Slot0Library_setTick(slot0Start, result.tick);
    var __c25 = Slot0Library_setSqrtPriceX96(__c24, result.sqrtPriceX96);
    self.slot0 = __c25;
    if (self.liquidity != result.liquidity) {
      self.liquidity = result.liquidity;
    }
    if (!(zeroForOne)) {
      self.feeGrowthGlobal1X128 = step.feeGrowthGlobalX128;
    } else {
      self.feeGrowthGlobal0X128 = step.feeGrowthGlobalX128;
    }
    if (zeroForOne != (params.amountSpecified < 0)) {
      var __c26 = SafeCast_toInt128(amountCalculated);
      var __c27 = SafeCast_toInt128((int256(params.amountSpecified - amountSpecifiedRemaining)));
      var __c28 = toBalanceDelta(__c26, __c27);
      swapDelta = __c28;
    } else {
      var __c29 = SafeCast_toInt128((int256(params.amountSpecified - amountSpecifiedRemaining)));
      var __c30 = SafeCast_toInt128(amountCalculated);
      var __c31 = toBalanceDelta(__c29, __c30);
      swapDelta = __c31;
    }
    return (swapDelta, amountToProtocol, swapFee, result);
  }

  function _updateProtocolFees(address currency, uint256 amount) internal {
    protocolFeesAccrued[currency] = uint256(protocolFeesAccrued[currency] + amount);
  }

  function UnsafeMath_simpleMulDiv(uint256 a, uint256 b, uint256 denominator) internal returns (uint256) {
    uint256 result = 0;
    result = denominator == 0 ? 0 : uint256(a * b) / denominator;
    return result;
  }

  function CurrencyDelta_applyDelta(address currency, address target, int128 delta) internal returns (int256, int256) {
    int256 previous = 0;
    int256 next = 0;
    var hashSlot = CurrencyDelta__computeSlot(target, currency);
    previous = int256(rawTransient[uint256(hashSlot)]);
    next = (previous + delta) as int256;
    rawTransient[uint256(hashSlot)] = uint256(next);
    return (previous, next);
  }

  function NonzeroDeltaCount_decrement() internal {
    rawTransient[COUNT_SLOT] = uint256(rawTransient[COUNT_SLOT] - 1);
  }

  function NonzeroDeltaCount_increment() internal {
    rawTransient[COUNT_SLOT] = uint256(rawTransient[COUNT_SLOT] + 1);
  }

  function CustomRevert_bubbleUpAndRevertWith(address revertingContract, bytes4 revertingFunctionSelector, bytes4 additionalContext) internal {
    require(false);
  }

  function CurrencyReserves_getSyncedReserves() internal returns (uint256) {
    return rawTransient[RESERVES_SLOT];
  }

  function CurrencyDelta__computeSlot(address target, address currency) internal returns (bytes32) {
    return keccak256(abi.encodePacked(uint256(uint160(target)), uint256(uint160(currency))));
  }

  function _burn(address sender, uint256 id, uint256 amount) internal {
    balanceOf[sender][id] = ((balanceOf[sender][id] - amount) as uint256);
    emit Transfer(msg.sender, sender, address(0), id, amount);
  }

  function LPFeeLibrary_isValid(uint24 self) internal returns (bool) {
    return self <= 1000000;
  }

  function Slot0Library_setProtocolFee(bytes32 _packed, uint24 _protocolFee) internal returns (bytes32) {
    uint256 cleared = uint256(_packed) &[uint256] 115792089237315784047456174635831223332708078880448723302429075438902230122495;
    return bytes32(cleared |[uint256] (uint256(uint24(_protocolFee)) <<[uint256] 184));
  }

  function BitMath_mostSignificantBit(uint256 x) internal returns (uint8) {
    require(x > 0);
    uint256 r = x > 0xffffffffffffffffffffffffffffffff ? 128 : 0;
    r = r |[uint256] ((x >>[uint256] r) > 0xffffffffffffffff ? 64 : 0);
    r = r |[uint256] ((x >>[uint256] r) > 0xffffffff ? 32 : 0);
    r = r |[uint256] ((x >>[uint256] r) > 0xffff ? 16 : 0);
    r = r |[uint256] ((x >>[uint256] r) > 0xff ? 8 : 0);
    uint256 index = (0x8421084210842108cc6318c6db6d54be >>[uint256] (x >>[uint256] r)) &[uint256] 31;
    var low = wordByte(0x0706060506020500060203020504000106050205030304010505030400000000, index);
    return uint8(r |[uint256] low);
  }

  function CustomRevert_revertWith_bytes4_int24_int24(bytes4 selector, int24 value1, int24 value2) internal {
    require(false);
  }

  function Position_calculatePositionKey(address owner, int24 tickLower, int24 tickUpper, bytes32 salt) internal returns (bytes32) {
    return keccak256(abi.encodePacked(address(owner), int24(tickLower), int24(tickUpper), bytes32(salt)));
  }

  function FullMath_mulDiv(uint256 a, uint256 b, uint256 denominator) internal returns (uint256) {
    uint256 result = 0;
    uint256 prod0 = uint256(a * b);
    uint256 prod1 = 0;
    uint256 mm = (a * b) % type(uint256).max;
    prod1 = uint256(mm - prod0 - (mm < prod0 ? 1 : 0));
    require(denominator > prod1);
    if (prod1 == 0) {
      result = prod0 / denominator;
      return result;
    }
    uint256 remainder = 0;
    remainder = (a * b) % denominator;
    prod1 = uint256(prod1 - (remainder > prod0 ? 1 : 0));
    prod0 = uint256(prod0 - remainder);
    uint256 twos = (uint256(0 - denominator)) &[uint256] denominator;
    denominator = denominator / twos;
    prod0 = prod0 / twos;
    twos = uint256(uint256(0 - twos) / twos + 1);
    prod0 = (prod0 |[uint256] uint256(prod1 * twos));
    uint256 inv = (uint256(3 * denominator)) ^[uint256] 2;
    inv = uint256(inv * uint256(2 - uint256(denominator * inv)));
    inv = uint256(inv * uint256(2 - uint256(denominator * inv)));
    inv = uint256(inv * uint256(2 - uint256(denominator * inv)));
    inv = uint256(inv * uint256(2 - uint256(denominator * inv)));
    inv = uint256(inv * uint256(2 - uint256(denominator * inv)));
    inv = uint256(inv * uint256(2 - uint256(denominator * inv)));
    result = uint256(prod0 * inv);
    return result;
    return result;
  }

  function SafeCast_toInt256(uint256 x) internal returns (int256) {
    int256 y = 0;
    y = int256(x);
    if (y < 0) {
      require(false);
    }
    return y;
  }

  function SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool(uint160 sqrtPriceAX96, uint160 sqrtPriceBX96, uint128 liquidity, bool roundUp) internal returns (uint256) {
    if (sqrtPriceAX96 > sqrtPriceBX96) {
      var __t0 = sqrtPriceBX96;
      var __t1 = sqrtPriceAX96;
      sqrtPriceAX96 = __t0;
      sqrtPriceBX96 = __t1;
    }
    require(sqrtPriceAX96 != 0);
    uint256 numerator1 = uint256(liquidity) <<[uint256] 96;
    uint256 numerator2 = uint160(sqrtPriceBX96 - sqrtPriceAX96);
    if (roundUp) {
      var amount = FullMath_mulDivRoundingUp(numerator1, numerator2, sqrtPriceBX96);
      var result = UnsafeMath_divRoundingUp(amount, sqrtPriceAX96);
      return result;
    } else {
      var amount = FullMath_mulDiv(numerator1, numerator2, sqrtPriceBX96);
      return amount / sqrtPriceAX96;
    }
  }

  function SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool(uint160 sqrtPriceAX96, uint160 sqrtPriceBX96, uint128 liquidity, bool roundUp) internal returns (uint256) {
    uint256 amount1 = 0;
    var numerator = SqrtPriceMath_absDiff(sqrtPriceAX96, sqrtPriceBX96);
    uint256 denominator = 79228162514264337593543950336;
    uint256 _liquidity = uint256(liquidity);
    var __c1 = FullMath_mulDiv(_liquidity, numerator, denominator);
    amount1 = __c1;
    amount1 = uint256(amount1 + (roundUp && ((_liquidity * numerator) % denominator > 0) ? 1 : 0));
    return amount1;
  }

  function ProtocolFeeLibrary_getZeroForOneFee(uint24 self) internal returns (uint16) {
    return uint16((self &[uint24] 4095));
  }

  function Slot0Library_protocolFee(bytes32 _packed) internal returns (uint24) {
    return uint24(uint256(_packed) >>[uint256] 184);
  }

  function ProtocolFeeLibrary_getOneForZeroFee(uint24 self) internal returns (uint16) {
    return uint16((self >>[uint24] 12));
  }

  function LPFeeLibrary_isOverride(uint24 self) internal returns (bool) {
    return (self &[uint24] 4194304) != 0;
  }

  function LPFeeLibrary_removeOverrideFlagAndValidate(uint24 self) internal returns (uint24) {
    uint24 fee = 0;
    var __c0 = LPFeeLibrary_removeOverrideFlag(self);
    fee = __c0;
    var __c1 = LPFeeLibrary_validate(fee);
    return fee;
  }

  function Slot0Library_lpFee(bytes32 _packed) internal returns (uint24) {
    return uint24(uint256(_packed) >>[uint256] 208);
  }

  function ProtocolFeeLibrary_calculateSwapFee(uint16 self, uint24 lpFee) internal returns (uint24) {
    uint256 protocol = uint256(self &[uint16] 4095);
    return uint24(protocol + lpFee - (protocol * lpFee) / 1000000);
  }

  function CustomRevert_revertWith_bytes4_uint160_uint160(bytes4 selector, uint160 value1, uint160 value2) internal {
    require(false);
  }

  function TickBitmap_nextInitializedTickWithinOneWord(mapping(int16 => uint256) storage self, int24 tick, int24 tickSpacing, bool lte) internal returns (int24, bool) {
    var compressed = TickBitmap_compress(tick, tickSpacing);
    if (lte) {
      var position = TickBitmap_position(compressed);
      int16 wordPos = position.0;
      uint8 bitPos = position.1;
      uint256 mask = type(uint256).max >>[uint256] (255 - bitPos);
      uint256 masked = self[wordPos] &[uint256] mask;
      bool initialized = masked != 0;
      int24 next = int24(int24(compressed - bitPos) * tickSpacing);
      if (initialized) {
        var msb = BitMath_mostSignificantBit(masked);
        next = int24(int24(compressed - uint8(bitPos - msb)) * tickSpacing);
      }
      return (next, initialized);
    } else {
      compressed = int24(compressed + 1);
      var position = TickBitmap_position(compressed);
      int16 wordPos = position.0;
      uint8 bitPos = position.1;
      uint256 mask = ~[uint256] uint256((1 <<[uint256] bitPos) - 1);
      uint256 masked = self[wordPos] &[uint256] mask;
      bool initialized = masked != 0;
      int24 next = int24(int24(compressed + uint8(255 - bitPos)) * tickSpacing);
      if (initialized) {
        var lsb = BitMath_leastSignificantBit(masked);
        next = int24(int24(compressed + uint8(lsb - bitPos)) * tickSpacing);
      }
      return (next, initialized);
    }
  }

  function SwapMath_computeSwapStep(uint160 sqrtPriceCurrentX96, uint160 sqrtPriceTargetX96, uint128 liquidity, int256 amountRemaining, uint24 feePips) internal returns (uint160, uint256, uint256, uint256) {
    uint160 sqrtPriceNextX96 = 0;
    uint256 amountIn = 0;
    uint256 amountOut = 0;
    uint256 feeAmount = 0;
    uint256 _feePips = feePips;
    bool zeroForOne = sqrtPriceCurrentX96 >= sqrtPriceTargetX96;
    bool exactIn = amountRemaining < 0;
    if (exactIn) {
      var amountRemainingLessFee = FullMath_mulDiv(uint256(int256(0 - amountRemaining)), uint256(1000000 - _feePips), 1000000);
      if (zeroForOne) {
        var amount = SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool(sqrtPriceTargetX96, sqrtPriceCurrentX96, liquidity, true);
        amountIn = amount;
      } else {
        var amount = SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool(sqrtPriceCurrentX96, sqrtPriceTargetX96, liquidity, true);
        amountIn = amount;
      }
      if (amountRemainingLessFee >= amountIn) {
        sqrtPriceNextX96 = sqrtPriceTargetX96;
        feeAmount = amountIn;
        if (_feePips != 1000000) {
          var computedFee = FullMath_mulDivRoundingUp(amountIn, _feePips, uint256(1000000 - _feePips));
          feeAmount = computedFee;
        }
      } else {
        amountIn = amountRemainingLessFee;
        var __c4 = SqrtPriceMath_getNextSqrtPriceFromInput(sqrtPriceCurrentX96, liquidity, amountRemainingLessFee, zeroForOne);
        sqrtPriceNextX96 = __c4;
        feeAmount = uint256(uint256(int256(0 - amountRemaining)) - amountIn);
      }
      if (zeroForOne) {
        var amount = SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool(sqrtPriceNextX96, sqrtPriceCurrentX96, liquidity, false);
        amountOut = amount;
      } else {
        var amount = SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool(sqrtPriceCurrentX96, sqrtPriceNextX96, liquidity, false);
        amountOut = amount;
      }
    } else {
      if (zeroForOne) {
        var amount = SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool(sqrtPriceTargetX96, sqrtPriceCurrentX96, liquidity, false);
        amountOut = amount;
      } else {
        var amount = SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool(sqrtPriceCurrentX96, sqrtPriceTargetX96, liquidity, false);
        amountOut = amount;
      }
      if (uint256(amountRemaining) >= amountOut) {
        sqrtPriceNextX96 = sqrtPriceTargetX96;
      } else {
        amountOut = uint256(amountRemaining);
        var __c9 = SqrtPriceMath_getNextSqrtPriceFromOutput(sqrtPriceCurrentX96, liquidity, amountOut, zeroForOne);
        sqrtPriceNextX96 = __c9;
      }
      if (zeroForOne) {
        var amount = SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool(sqrtPriceNextX96, sqrtPriceCurrentX96, liquidity, true);
        amountIn = amount;
      } else {
        var amount = SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool(sqrtPriceCurrentX96, sqrtPriceNextX96, liquidity, true);
        amountIn = amount;
      }
      var __c12 = FullMath_mulDivRoundingUp(amountIn, _feePips, uint256(1000000 - _feePips));
      feeAmount = __c12;
    }
    return (sqrtPriceNextX96, amountIn, amountOut, feeAmount);
  }

  function SwapMath_getSqrtPriceTarget(bool zeroForOne, uint160 sqrtPriceNextX96, uint160 sqrtPriceLimitX96) internal returns (uint160) {
    if (zeroForOne) {
      return sqrtPriceNextX96 < sqrtPriceLimitX96 ? sqrtPriceLimitX96 : sqrtPriceNextX96;
    }
    return sqrtPriceNextX96 > sqrtPriceLimitX96 ? sqrtPriceLimitX96 : sqrtPriceNextX96;
  }

  function Pool_crossTick(Pool_State storage self, int24 tick, uint256 feeGrowthGlobal0X128, uint256 feeGrowthGlobal1X128) internal returns (int128) {
    int128 liquidityNet = 0;
    TickInfo storage info = self.ticks[tick];
    info.feeGrowthOutside0X128 = uint256(feeGrowthGlobal0X128 - info.feeGrowthOutside0X128);
    info.feeGrowthOutside1X128 = uint256(feeGrowthGlobal1X128 - info.feeGrowthOutside1X128);
    liquidityNet = int128(info.liquidityPacked >>[uint256] 128);
    return liquidityNet;
  }

  function UnsafeMath_divRoundingUp(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = 0;
    if (y == 0) {
      return 0;
    }
    z = x / y + (x % y > 0 ? 1 : 0);
    return z;
  }

  function FullMath_mulDivRoundingUp(uint256 a, uint256 b, uint256 denominator) internal returns (uint256) {
    uint256 result = 0;
    var __c0 = FullMath_mulDiv(a, b, denominator);
    result = __c0;
    if (((a * b) % denominator) != 0) {
      result = uint256(result + 1);
      require(result > 0);
    }
    return result;
  }

  function SqrtPriceMath_absDiff(uint160 a, uint160 b) internal returns (uint256) {
    return a >= b ? a - b : b - a;
  }

  function LPFeeLibrary_removeOverrideFlag(uint24 self) internal returns (uint24) {
    return self &[uint24] 12582911;
  }

  function TickBitmap_compress(int24 tick, int24 tickSpacing) internal returns (int24) {
    if (tickSpacing == 0) { return 0; }
    return int24(sdiv(tick, tickSpacing) - (srem(tick, tickSpacing) < 0 ? 1 : 0));
  }

  function TickBitmap_position(int24 tick) internal returns (int16, uint8) {
    return (int16(tick >>[int24] 8), uint8(tick));
  }

  function BitMath_leastSignificantBit(uint256 x) internal returns (uint8) {
    require(x > 0);
    x = x &[uint256] uint256(0 - x);
    uint256 index = (uint256(x * 0xb6db6db6ddddddddd34d34d349249249210842108c6318c639ce739cffffffff) >>[uint256] 250) <<[uint256] 2;
    uint256 r = ((0x8040405543005266443200005020610674053026020000107506200176117077 <<[uint256] index) >>[uint256] 252) <<[uint256] 5;
    uint256 lowIndex = (0xd76453e0 / (x >>[uint256] r)) &[uint256] 31;
    var low = wordByte(0x001f0d1e100c1d070f090b19131c1706010e11080a1a141802121b1503160405, lowIndex);
    return uint8(r |[uint256] low);
  }

  function SqrtPriceMath_getNextSqrtPriceFromInput(uint160 sqrtPX96, uint128 liquidity, uint256 amountIn, bool zeroForOne) internal returns (uint160) {
    require(sqrtPX96 != 0 && liquidity != 0);
    if (zeroForOne) {
      var result = SqrtPriceMath_getNextSqrtPriceFromAmount0RoundingUp(sqrtPX96, liquidity, amountIn, true);
      return result;
    } else {
      var result = SqrtPriceMath_getNextSqrtPriceFromAmount1RoundingDown(sqrtPX96, liquidity, amountIn, true);
      return result;
    }
  }

  function SqrtPriceMath_getNextSqrtPriceFromOutput(uint160 sqrtPX96, uint128 liquidity, uint256 amountOut, bool zeroForOne) internal returns (uint160) {
    require(sqrtPX96 != 0 && liquidity != 0);
    if (zeroForOne) {
      var result = SqrtPriceMath_getNextSqrtPriceFromAmount1RoundingDown(sqrtPX96, liquidity, amountOut, false);
      return result;
    } else {
      var result = SqrtPriceMath_getNextSqrtPriceFromAmount0RoundingUp(sqrtPX96, liquidity, amountOut, false);
      return result;
    }
  }

  function SqrtPriceMath_getNextSqrtPriceFromAmount0RoundingUp(uint160 sqrtPX96, uint128 liquidity, uint256 amount, bool add) internal returns (uint160) {
    if (amount == 0) {
      return sqrtPX96;
    }
    uint256 numerator1 = uint256(liquidity) <<[uint256] 96;
    if (add) {
      uint256 product = uint256(amount * sqrtPX96);
      if ((product / amount) == sqrtPX96) {
        uint256 denominator = uint256(numerator1 + product);
        if (denominator >= numerator1) {
          var __c0 = FullMath_mulDivRoundingUp(numerator1, sqrtPX96, denominator);
          return uint160(__c0);
        }
      }
      var __c1 = UnsafeMath_divRoundingUp(numerator1, (((numerator1 / sqrtPX96) + amount) as uint256));
      return uint160(__c1);
    } else {
      uint256 product = uint256(amount * sqrtPX96);
      require(product / amount == sqrtPX96 && numerator1 > product);
      uint256 denominator = uint256(numerator1 - product);
      var __c2 = FullMath_mulDivRoundingUp(numerator1, sqrtPX96, denominator);
      var __c3 = SafeCast_toUint160(__c2);
      return __c3;
    }
  }

  function SqrtPriceMath_getNextSqrtPriceFromAmount1RoundingDown(uint160 sqrtPX96, uint128 liquidity, uint256 amount, bool add) internal returns (uint160) {
    uint256 quotient = 0;
    if (add) {
      if (amount <= type(uint160).max) {
        quotient = (amount <<[uint256] 96) / liquidity;
      } else {
        var product = FullMath_mulDiv(amount, 79228162514264337593543950336, liquidity);
        quotient = product;
      }
      var result = SafeCast_toUint160((sqrtPX96 + quotient) as uint256);
      return result;
    } else {
      if (amount <= type(uint160).max) {
        var product = UnsafeMath_divRoundingUp(amount <<[uint256] 96, liquidity);
        quotient = product;
      } else {
        var product = FullMath_mulDivRoundingUp(amount, 79228162514264337593543950336, liquidity);
        quotient = product;
      }
      require(sqrtPX96 > quotient);
      return uint160(sqrtPX96 - quotient);
    }
  }

  function SafeCast_toUint160(uint256 x) internal returns (uint160) {
    uint160 y = 0;
    y = uint160(x);
    if (y != x) {
      require(false);
    }
    return y;
  }

  function balanceOf(address arg0, uint256 arg1) external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return balanceOf[arg0][arg1];
  }

  function supportsInterface(bytes4 interfaceId) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return (interfaceId == bytes4(33540519)) || (interfaceId == bytes4(258158515));
  }

  function transfer(address receiver, uint256 id, uint256 amount) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    balanceOf[msg.sender][id] = ((balanceOf[msg.sender][id] - amount) as uint256);
    balanceOf[receiver][id] = ((balanceOf[receiver][id] + amount) as uint256);
    emit Transfer(msg.sender, msg.sender, receiver, id, amount);
    return true;
  }

  function settle() external payable returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = Lock_isUnlocked();
    if (!(__c0)) {
      require(false);
    }
    var __c1 = _settle(msg.sender);
    return __c1;
  }

  function «initialize»(PoolKey memory key, uint160 sqrtPriceX96) external returns (int24) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    PoolKey key = PoolKey({currency0: key.0, currency1: key.1, fee: key.2, tickSpacing: key.3, hooks: key.4});
    int24 tick = 0;
    var __c0 = checkNotDelegateCall();
    if (key.tickSpacing > ((type(int16).max))) {
      require(false);
    }
    if (key.tickSpacing < (1)) {
      require(false);
    }
    if (key.currency0 >= key.currency1) {
      require(false);
    }
    var __c1 = Hooks_isValidHookAddress(key.hooks, key.fee);
    if (!(__c1)) {
      require(false);
    }
    var lpFee = LPFeeLibrary_getInitialLPFee(key.fee);
    var __c3 = Hooks_beforeInitialize(key.hooks, key, sqrtPriceX96);
    var id = PoolIdLibrary_toId(key);
    var __c5 = Pool_initialize(_pools[id], sqrtPriceX96, lpFee);
    tick = __c5;
    emit Initialize(id, key.currency0, key.currency1, key.fee, key.tickSpacing, key.hooks, sqrtPriceX96, tick);
    var __c6 = Hooks_afterInitialize(key.hooks, key, sqrtPriceX96, tick);
    return tick;
  }

  function mint(address «to», uint256 id, uint256 amount) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = Lock_isUnlocked();
    if (!(__c0)) {
      require(false);
    }
    var currency = CurrencyLibrary_fromId(id);
    var __c2 = SafeCast_toInt128_uint256(amount);
    var __c3 = _accountDelta(currency, int128(0 - __c2), msg.sender);
    var __c4 = CurrencyLibrary_toId(currency);
    var __c5 = _mint(«to», __c4, amount);
  }

  function extsload(bytes32 slot) external returns (bytes32) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return bytes32(rawSlots[uint256(slot)]);
  }

  function extsload(bytes32 startSlot, uint256 nSlots) external returns (bytes32[]) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    -- The no-wrap domain is poolManagerWF, a refinement hypothesis, not a guard.
    bytes32[] result = new bytes32[](nSlots);
    uint256 first = rawSlots[uint256(startSlot)];
    if (nSlots == 0) {
      -- The assembly loop still performs its first SLOAD for the empty result.
      return result;
    }
    result[0] = bytes32(first);
    uint256 i = 1;
    while (i < nSlots) {
      result[i] = bytes32(rawSlots[uint256(uint256(startSlot) + i)]);
      i = i + 1;
    }
    return result;
  }

  function extsload(bytes32[] calldata slots) external returns (bytes32[]) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    bytes32[] result = new bytes32[](slots.length);
    if (slots.length == 0) {
      bytes data = msg.data;
      uint256 offset = uint256(abi.decode(data[4 : 36], (uint256))) + 36;
      var slot = calldataWordAt(offset);
      uint256 ignored = rawSlots[slot];
      return result;
    }
    uint256 i = 0;
    while (i < slots.length) {
      result[i] = bytes32(rawSlots[uint256(slots[i])]);
      i = i + 1;
    }
    return result;
  }

  function take(address currency, address «to», uint256 amount) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = Lock_isUnlocked();
    if (!(__c0)) {
      require(false);
    }
    var __c1 = SafeCast_toInt128_uint256(amount);
    var __c2 = _accountDelta(currency, int128(0 - __c1), msg.sender);
    var __c3 = CurrencyLibrary_transfer(currency, «to», amount);
  }

  function setProtocolFeeController(address controller) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(msg.sender == owner);
    protocolFeeController = controller;
    emit ProtocolFeeControllerUpdated(controller);
  }

  function collectProtocolFees(address recipient, address currency, uint256 amount) external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    uint256 amountCollected = 0;
    if (msg.sender != protocolFeeController) {
      require(false);
    }
    var __c0 = CurrencyLibrary_isAddressZero(currency);
    if (!(__c0)) {
      var syncedCurrency = CurrencyReserves_getSyncedCurrency();
      require(syncedCurrency != currency);
    }
    amountCollected = (amount == 0) ? protocolFeesAccrued[currency] : amount;
    protocolFeesAccrued[currency] = ((protocolFeesAccrued[currency] - amountCollected) as uint256);
    var __c2 = CurrencyLibrary_transfer(currency, recipient, amountCollected);
    return amountCollected;
  }

  function settleFor(address recipient) external payable returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = Lock_isUnlocked();
    if (!(__c0)) {
      require(false);
    }
    var __c1 = _settle(recipient);
    return __c1;
  }

  function approve(address spender, uint256 id, uint256 amount) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    allowance[msg.sender][spender][id] = amount;
    emit Approval(msg.sender, spender, id, amount);
    return true;
  }

  function unlock(bytes calldata data) external returns (bytes) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    bytes memory result = new bytes(0);
    var __c0 = Lock_isUnlocked();
    if (__c0) {
      require(false);
    }
    var __c1 = Lock_unlock();
    address caller = msg.sender;
    var __c2 = caller.unlockCallback(data);
    result = __c2;
    var __c3 = NonzeroDeltaCount_read();
    if (__c3 != 0) {
      require(false);
    }
    var __c4 = Lock_lock();
    return result;
  }

  function donate(PoolKey memory key, uint256 amount0, uint256 amount1, bytes calldata hookData) external returns (int256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    PoolKey key = PoolKey({currency0: key.0, currency1: key.1, fee: key.2, tickSpacing: key.3, hooks: key.4});
    int256 delta = 0;
    var __c0 = Lock_isUnlocked();
    if (!(__c0)) {
      require(false);
    }
    var __c1 = checkNotDelegateCall();
    var poolId = PoolIdLibrary_toId(key);
    var __c3 = _getPool(poolId);
    Pool_State storage pool = __c3;
    var __c4 = Pool_checkPoolInitialized(pool);
    var __c5 = Hooks_beforeDonate(key.hooks, key, amount0, amount1, hookData);
    var __c6 = Pool_donate(pool, amount0, amount1);
    delta = __c6;
    var __c7 = _accountPoolBalanceDelta(key, delta, msg.sender);
    emit Donate(poolId, msg.sender, amount0, amount1);
    var __c8 = Hooks_afterDonate(key.hooks, key, amount0, amount1, hookData);
    return delta;
  }

  function setOperator(address operator, bool approved) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    isOperator[msg.sender][operator] = approved;
    emit OperatorSet(msg.sender, operator, approved);
    return true;
  }

  function allowance(address arg0, address arg1, uint256 arg2) external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return allowance[arg0][arg1][arg2];
  }

  function modifyLiquidity(PoolKey memory key, ModifyLiquidityParams_8903 memory params, bytes calldata hookData) external returns (int256, int256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    PoolKey key = PoolKey({currency0: key.0, currency1: key.1, fee: key.2, tickSpacing: key.3, hooks: key.4});
    ModifyLiquidityParams_8903 params = ModifyLiquidityParams_8903({tickLower: params.0, tickUpper: params.1, liquidityDelta: params.2, salt: params.3});
    int256 callerDelta = 0;
    int256 feesAccrued = 0;
    var __c0 = Lock_isUnlocked();
    if (!(__c0)) {
      require(false);
    }
    var __c1 = checkNotDelegateCall();
    var id = PoolIdLibrary_toId(key);
    var __c3 = _getPool(id);
    Pool_State storage pool = __c3;
    var __c4 = Pool_checkPoolInitialized(pool);
    var __c5 = Hooks_beforeModifyLiquidity(key.hooks, key, params, hookData);
    int256 principalDelta = 0;
    var __c6 = SafeCast_toInt128(params.liquidityDelta);
    var __c7 = Pool_modifyLiquidity(pool, Pool_ModifyLiquidityParams({owner: msg.sender, tickLower: params.tickLower, tickUpper: params.tickUpper, liquidityDelta: __c6, tickSpacing: key.tickSpacing, salt: params.salt}));
    principalDelta = __c7.0;
    feesAccrued = __c7.1;
    var totalDelta = BalanceDelta_add(principalDelta, feesAccrued);
    callerDelta = totalDelta;
    emit ModifyLiquidity(id, msg.sender, params.tickLower, params.tickUpper, params.liquidityDelta, params.salt);
    int256 hookDelta = 0;
    var __c8 = Hooks_afterModifyLiquidity(key.hooks, key, params, callerDelta, feesAccrued, hookData);
    callerDelta = __c8.0;
    hookDelta = __c8.1;
    if (hookDelta != 0) {
      var ignored = _accountPoolBalanceDelta(key, hookDelta, key.hooks);
    }
    var __c9 = _accountPoolBalanceDelta(key, callerDelta, msg.sender);
    return (callerDelta, feesAccrued);
  }

  function sync(address currency) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = CurrencyLibrary_isAddressZero(currency);
    if (__c0) {
      var __c1 = CurrencyReserves_resetCurrency();
    } else {
      var balance = CurrencyLibrary_balanceOfSelf(currency);
      var __c3 = CurrencyReserves_syncCurrencyAndReserves(currency, balance);
    }
  }

  function owner() external returns (address) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return owner;
  }

  function updateDynamicLPFee(PoolKey memory key, uint24 newDynamicLPFee) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    PoolKey key = PoolKey({currency0: key.0, currency1: key.1, fee: key.2, tickSpacing: key.3, hooks: key.4});
    var __c0 = LPFeeLibrary_isDynamicFee(key.fee);
    if (!(__c0) || (msg.sender != key.hooks)) {
      require(false);
    }
    var __c1 = LPFeeLibrary_validate(newDynamicLPFee);
    var id = PoolIdLibrary_toId(key);
    var __c3 = Pool_setLPFee(_pools[id], newDynamicLPFee);
  }

  function exttload(bytes32[] calldata slots) external returns (bytes32[]) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    bytes32[] result = new bytes32[](slots.length);
    if (slots.length == 0) {
      -- The assembly reads once at the array's data offset even for zero length.
      bytes data = msg.data;
      uint256 offset = uint256(abi.decode(data[4 : 36], (uint256))) + 36;
      var slot = calldataWordAt(offset);
      uint256 ignored = rawTransient[slot];
      return result;
    }
    uint256 i = 0;
    while (i < slots.length) {
      result[i] = bytes32(rawTransient[uint256(slots[i])]);
      i = i + 1;
    }
    return result;
  }

  function exttload(bytes32 slot) external returns (bytes32) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return bytes32(rawTransient[uint256(slot)]);
  }

  function swap(PoolKey memory key, SwapParams_8914 memory params, bytes calldata hookData) external returns (int256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    PoolKey key = PoolKey({currency0: key.0, currency1: key.1, fee: key.2, tickSpacing: key.3, hooks: key.4});
    SwapParams_8914 params = SwapParams_8914({zeroForOne: params.0, amountSpecified: params.1, sqrtPriceLimitX96: params.2});
    int256 swapDelta = 0;
    var __c0 = Lock_isUnlocked();
    if (!(__c0)) {
      require(false);
    }
    var __c1 = checkNotDelegateCall();
    if (params.amountSpecified == 0) {
      require(false);
    }
    var id = PoolIdLibrary_toId(key);
    var __c3 = _getPool(id);
    Pool_State storage pool = __c3;
    var __c4 = Pool_checkPoolInitialized(pool);
    int256 beforeSwapDelta = 0;
    int256 amountToSwap = 0;
    uint24 lpFeeOverride = 0;
    var __c5 = Hooks_beforeSwap(key.hooks, key, params, hookData);
    amountToSwap = __c5.0;
    beforeSwapDelta = __c5.1;
    lpFeeOverride = __c5.2;
    var __c6 = _swap(pool, id, Pool_SwapParams({tickSpacing: key.tickSpacing, zeroForOne: params.zeroForOne, amountSpecified: amountToSwap, sqrtPriceLimitX96: params.sqrtPriceLimitX96, lpFeeOverride: lpFeeOverride}), (params.zeroForOne ? key.currency0 : key.currency1));
    swapDelta = __c6;
    int256 hookDelta = 0;
    var __c7 = Hooks_afterSwap(key.hooks, key, params, swapDelta, hookData, beforeSwapDelta);
    swapDelta = __c7.0;
    hookDelta = __c7.1;
    if (hookDelta != 0) {
      var ignored = _accountPoolBalanceDelta(key, hookDelta, key.hooks);
    }
    var __c8 = _accountPoolBalanceDelta(key, swapDelta, msg.sender);
    return swapDelta;
  }

  function isOperator(address arg0, address arg1) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return isOperator[arg0][arg1];
  }

  function clear(address currency, uint256 amount) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = Lock_isUnlocked();
    if (!(__c0)) {
      require(false);
    }
    var current = CurrencyDelta_getDelta(currency, msg.sender);
    var amountDelta = SafeCast_toInt128_uint256(amount);
    if (amountDelta != current) {
      require(false);
    }
    var __c3 = _accountDelta(currency, int128(0 - amountDelta), msg.sender);
  }

  function setProtocolFee(PoolKey memory key, uint24 newProtocolFee) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    PoolKey key = PoolKey({currency0: key.0, currency1: key.1, fee: key.2, tickSpacing: key.3, hooks: key.4});
    if (msg.sender != protocolFeeController) {
      require(false);
    }
    var __c0 = ProtocolFeeLibrary_isValidProtocolFee(newProtocolFee);
    if (!(__c0)) {
      require(false);
    }
    var id = PoolIdLibrary_toId(key);
    var __c2 = _getPool(id);
    var __c3 = Pool_setProtocolFee(__c2, newProtocolFee);
    emit ProtocolFeeUpdated(id, newProtocolFee);
  }

  function protocolFeeController() external returns (address) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return protocolFeeController;
  }

  function transferOwnership(address newOwner) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    require(msg.sender == owner);
    owner = newOwner;
    emit OwnershipTransferred(msg.sender, newOwner);
  }

  function burn(address «from», uint256 id, uint256 amount) external {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    var __c0 = Lock_isUnlocked();
    if (!(__c0)) {
      require(false);
    }
    var currency = CurrencyLibrary_fromId(id);
    var __c2 = SafeCast_toInt128_uint256(amount);
    var __c3 = _accountDelta(currency, __c2, msg.sender);
    var __c4 = CurrencyLibrary_toId(currency);
    var __c5 = _burnFrom(«from», __c4, amount);
  }

  function protocolFeesAccrued(address arg0) external returns (uint256) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    return protocolFeesAccrued[arg0];
  }

  function transferFrom(address sender, address receiver, uint256 id, uint256 amount) external returns (bool) {
    bytes __calldata = msg.data;
    require(__calldata.length < 57896044618658097711785492504343953926634992332820282019728792003956564819972);
    if ((msg.sender != sender) && !(isOperator[sender][msg.sender])) {
      uint256 allowed = allowance[sender][msg.sender][id];
      if (allowed != type(uint256).max) {
        allowance[sender][msg.sender][id] = (allowed - amount) as uint256;
      }
    }
    balanceOf[sender][id] = ((balanceOf[sender][id] - amount) as uint256);
    balanceOf[receiver][id] = ((balanceOf[receiver][id] + amount) as uint256);
    emit Transfer(msg.sender, sender, receiver, id, amount);
    return true;
  }

}

/-- Callee ABI from the pinned IHooks, IUnlockCallback and IERC20 interfaces.
Hook returns are parsed by the library helpers above, including their permissive
selector padding and truncated uint24 fee; the ABI decoder is only for typed calls. -/
def externalABI : ExternalCallABI where
  encode? := fun name args =>
    match name with
    | "balanceOf" => -- balanceOf(address)
      ABI.encodeCallWithSelector? ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
        [(.elem .address)] args
    | "unlockCallback" => -- unlockCallback(bytes)
      ABI.encodeCallWithSelector? ⟨#[0x91, 0xdd, 0x73, 0x46]⟩
        [.bytes] args
    | "beforeInitialize" => -- beforeInitialize(address,(address,address,uint24,int24,address),uint160)
      ABI.encodeCallWithSelector? ⟨#[0xdc, 0x98, 0x35, 0x4e]⟩
        [(.elem .address), (.tuple [(.elem .address), (.elem .address), (.elem (.int (.uint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨24, by decide⟩))), (.elem .address)]), (.elem (.int (.uint ⟨160, by decide⟩)))] args
    | "afterInitialize" => -- afterInitialize(address,(address,address,uint24,int24,address),uint160,int24)
      ABI.encodeCallWithSelector? ⟨#[0x6f, 0xe7, 0xe6, 0xeb]⟩
        [(.elem .address), (.tuple [(.elem .address), (.elem .address), (.elem (.int (.uint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨24, by decide⟩))), (.elem .address)]), (.elem (.int (.uint ⟨160, by decide⟩))), (.elem (.int (.sint ⟨24, by decide⟩)))] args
    | "beforeAddLiquidity" => -- beforeAddLiquidity(address,(address,address,uint24,int24,address),(int24,int24,int256,bytes32),bytes)
      ABI.encodeCallWithSelector? ⟨#[0x25, 0x99, 0x82, 0xe5]⟩
        [(.elem .address), (.tuple [(.elem .address), (.elem .address), (.elem (.int (.uint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨24, by decide⟩))), (.elem .address)]), (.tuple [(.elem (.int (.sint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨256, by decide⟩))), (.elem (.bytes ⟨31, by decide⟩))]), .bytes] args
    | "beforeRemoveLiquidity" => -- beforeRemoveLiquidity(address,(address,address,uint24,int24,address),(int24,int24,int256,bytes32),bytes)
      ABI.encodeCallWithSelector? ⟨#[0x21, 0xd0, 0xee, 0x70]⟩
        [(.elem .address), (.tuple [(.elem .address), (.elem .address), (.elem (.int (.uint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨24, by decide⟩))), (.elem .address)]), (.tuple [(.elem (.int (.sint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨256, by decide⟩))), (.elem (.bytes ⟨31, by decide⟩))]), .bytes] args
    | "afterAddLiquidity" => -- afterAddLiquidity(address,(address,address,uint24,int24,address),(int24,int24,int256,bytes32),int256,int256,bytes)
      ABI.encodeCallWithSelector? ⟨#[0x9f, 0x06, 0x3e, 0xfc]⟩
        [(.elem .address), (.tuple [(.elem .address), (.elem .address), (.elem (.int (.uint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨24, by decide⟩))), (.elem .address)]), (.tuple [(.elem (.int (.sint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨256, by decide⟩))), (.elem (.bytes ⟨31, by decide⟩))]), (.elem (.int (.sint ⟨256, by decide⟩))), (.elem (.int (.sint ⟨256, by decide⟩))), .bytes] args
    | "afterRemoveLiquidity" => -- afterRemoveLiquidity(address,(address,address,uint24,int24,address),(int24,int24,int256,bytes32),int256,int256,bytes)
      ABI.encodeCallWithSelector? ⟨#[0x6c, 0x2b, 0xbe, 0x7e]⟩
        [(.elem .address), (.tuple [(.elem .address), (.elem .address), (.elem (.int (.uint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨24, by decide⟩))), (.elem .address)]), (.tuple [(.elem (.int (.sint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨256, by decide⟩))), (.elem (.bytes ⟨31, by decide⟩))]), (.elem (.int (.sint ⟨256, by decide⟩))), (.elem (.int (.sint ⟨256, by decide⟩))), .bytes] args
    | "beforeSwap" => -- beforeSwap(address,(address,address,uint24,int24,address),(bool,int256,uint160),bytes)
      ABI.encodeCallWithSelector? ⟨#[0x57, 0x5e, 0x24, 0xb4]⟩
        [(.elem .address), (.tuple [(.elem .address), (.elem .address), (.elem (.int (.uint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨24, by decide⟩))), (.elem .address)]), (.tuple [(.elem .bool), (.elem (.int (.sint ⟨256, by decide⟩))), (.elem (.int (.uint ⟨160, by decide⟩)))]), .bytes] args
    | "afterSwap" => -- afterSwap(address,(address,address,uint24,int24,address),(bool,int256,uint160),int256,bytes)
      ABI.encodeCallWithSelector? ⟨#[0xb4, 0x7b, 0x2f, 0xb1]⟩
        [(.elem .address), (.tuple [(.elem .address), (.elem .address), (.elem (.int (.uint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨24, by decide⟩))), (.elem .address)]), (.tuple [(.elem .bool), (.elem (.int (.sint ⟨256, by decide⟩))), (.elem (.int (.uint ⟨160, by decide⟩)))]), (.elem (.int (.sint ⟨256, by decide⟩))), .bytes] args
    | "beforeDonate" => -- beforeDonate(address,(address,address,uint24,int24,address),uint256,uint256,bytes)
      ABI.encodeCallWithSelector? ⟨#[0xb6, 0xa8, 0xb0, 0xfa]⟩
        [(.elem .address), (.tuple [(.elem .address), (.elem .address), (.elem (.int (.uint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨24, by decide⟩))), (.elem .address)]), (.elem (.int (.uint ⟨256, by decide⟩))), (.elem (.int (.uint ⟨256, by decide⟩))), .bytes] args
    | "afterDonate" => -- afterDonate(address,(address,address,uint24,int24,address),uint256,uint256,bytes)
      ABI.encodeCallWithSelector? ⟨#[0xe1, 0xb4, 0xaf, 0x69]⟩
        [(.elem .address), (.tuple [(.elem .address), (.elem .address), (.elem (.int (.uint ⟨24, by decide⟩))), (.elem (.int (.sint ⟨24, by decide⟩))), (.elem .address)]), (.elem (.int (.uint ⟨256, by decide⟩))), (.elem (.int (.uint ⟨256, by decide⟩))), .bytes] args
    | _ => none
  decode? := fun name output =>
    match name with
    | "balanceOf" =>
      (ABI.decodeReturnValueWithMode? ABI.DecodeMode.modern (.elem (.int (.uint ⟨256, by decide⟩))) output).map (fun v => [v])
    | "unlockCallback" =>
      (ABI.decodeReturnValueWithMode? ABI.DecodeMode.modern .bytes output).map (fun v => [v])
    | _ => none

end Benchmarks.UniswapV4PoolManager.Syntax
