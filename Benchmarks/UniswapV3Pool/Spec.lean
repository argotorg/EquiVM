import Solm.Semantics
import Solm.SolidityLayout
import Benchmarks.UniswapV3Pool.Immutables

/-!
# UniswapV3Pool benchmark spec

Solm benchmark scaffold for upstream `Uniswap/v3-core` `Benchmarks/UniswapV3Pool/contracts/UniswapV3Pool.sol`.
The storage declarations and raw storage layout are transcribed from solc's storage-layout output.
Events and fallback/receive dispatch are omitted; the selector-dispatched ABI surface is explicit.

Some transition bodies are source-faithful Solm transcriptions (`collect`, `collectProtocol`,
`flash`, `increaseObservationCardinalityNext`, `initialize`, `burn`, `mint`, `observe`,
`snapshotCumulativesInside`, `swap`, public storage/immutable getters) together with the helper
library stack those transitions call. Events and fallback/receive dispatch remain intentionally
outside this benchmark surface.
-/

open Solm ABI Benchmarks.UniswapV3Pool.Immutables

namespace Benchmarks.UniswapV3Pool

/-! ## Types -/

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint16Int : IntType := .uint ⟨16, by decide⟩
def uint24Int : IntType := .uint ⟨24, by decide⟩
def uint32Int : IntType := .uint ⟨32, by decide⟩
def uint128Int : IntType := .uint ⟨128, by decide⟩
def uint160Int : IntType := .uint ⟨160, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩
def int16Int : IntType := .sint ⟨16, by decide⟩
def int24Int : IntType := .sint ⟨24, by decide⟩
def int56Int : IntType := .sint ⟨56, by decide⟩
def int128Int : IntType := .sint ⟨128, by decide⟩
def int256Int : IntType := .sint ⟨256, by decide⟩

def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint8 : ABIType := .elem (.int uint8Int)
def uint16 : ABIType := .elem (.int uint16Int)
def uint24 : ABIType := .elem (.int uint24Int)
def uint32 : ABIType := .elem (.int uint32Int)
def uint128 : ABIType := .elem (.int uint128Int)
def uint160 : ABIType := .elem (.int uint160Int)
def uint256 : ABIType := .elem (.int uint256Int)
def int16 : ABIType := .elem (.int int16Int)
def int24 : ABIType := .elem (.int int24Int)
def int56 : ABIType := .elem (.int int56Int)
def int128 : ABIType := .elem (.int int128Int)
def int256 : ABIType := .elem (.int int256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytesTy : ABIType := .bytes
def bytes32 : ABIType := .elem (.bytes bytes32Width)

def uint8St : StorageType := .elem (.int uint8Int)
def uint16St : StorageType := .elem (.int uint16Int)
def uint32St : StorageType := .elem (.int uint32Int)
def uint128St : StorageType := .elem (.int uint128Int)
def uint160St : StorageType := .elem (.int uint160Int)
def uint256St : StorageType := .elem (.int uint256Int)
def int16St : StorageType := .elem (.int int16Int)
def int24St : StorageType := .elem (.int int24Int)
def int56St : StorageType := .elem (.int int56Int)
def int128St : StorageType := .elem (.int int128Int)
def addrSt : StorageType := .elem .address
def boolSt : StorageType := .elem .bool
def bytes32St : StorageType := .elem (.bytes bytes32Width)

def int56ArrayTy : ABIType := .dynamicArray int56
def uint160ArrayTy : ABIType := .dynamicArray uint160

def zeroAddr : Expr := .cast (.intLit 0) addrSt

/-- An address value as an `Expr` literal (cast a `uint160` literal to `address`). -/
def addrLit (a : EVM.Address) : Expr := .cast (.intLit (Int.ofNat a.toNat)) addrSt

/-! ## External ABI surface used by high-level and low-level calls -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def parametersSelector : ByteArray := selectorBytes 0x89 0x03 0x57 0x30
def ownerSelector : ByteArray := selectorBytes 0x8d 0xa5 0xcb 0x5b
def balanceOfSelector : ByteArray := selectorBytes 0x70 0xa0 0x82 0x31
def transferSelector : ByteArray := selectorBytes 0xa9 0x05 0x9c 0xbb
def mintCallbackSelector : ByteArray := selectorBytes 0xd3 0x48 0x79 0x97
def swapCallbackSelector : ByteArray := selectorBytes 0xfa 0x46 0x1e 0x33
def flashCallbackSelector : ByteArray := selectorBytes 0xe9 0xcb 0xaf 0xb0

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 ty out).map (fun v => [v])

def decodeReturns? (tys : List ABIType) (out : EVM.Bytes) : Option (List Value) :=
  ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 tys out

def decodeVoid? (_out : EVM.Bytes) : Option (List Value) :=
  some []

def poolExternalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "parameters" then
      match args with
      | [] => some parametersSelector
      | _ => none
    else if name = "owner" then
      match args with
      | [] => some ownerSelector
      | _ => none
    else if name = "balanceOf" then
      ABI.encodeCallWithSelector? balanceOfSelector [addr] args
    else if name = "transfer" then
      ABI.encodeCallWithSelector? transferSelector [addr, uint256] args
    else if name = "uniswapV3MintCallback" then
      ABI.encodeCallWithSelector? mintCallbackSelector [uint256, uint256, bytesTy] args
    else if name = "uniswapV3SwapCallback" then
      ABI.encodeCallWithSelector? swapCallbackSelector [int256, int256, bytesTy] args
    else if name = "uniswapV3FlashCallback" then
      ABI.encodeCallWithSelector? flashCallbackSelector [uint256, uint256, bytesTy] args
    else
      none
  decode? := fun name out =>
    if name = "parameters" then
      decodeReturns? [addr, addr, addr, uint24, int24] out
    else if name = "owner" then
      decodeReturn? addr out
    else if name = "balanceOf" then
      decodeReturn? uint256 out
    else if name = "transfer" then
      decodeReturn? boolTy out
    else if name = "uniswapV3MintCallback" then
      decodeVoid? out
    else if name = "uniswapV3SwapCallback" then
      decodeVoid? out
    else if name = "uniswapV3FlashCallback" then
      decodeVoid? out
    else
      none

/-! ## Storage references -/

def slot0F (field : Ident) : StorageRef := { base := "slot0", steps := [.field field] }
def protocolFeesF (field : Ident) : StorageRef := { base := "protocolFees", steps := [.field field] }
def ticksF (tick : Expr) (field : Ident) : StorageRef :=
  { base := "ticks", steps := [.mindex tick, .field field] }
def ticksRef (tick : Expr) : StorageRef :=
  { base := "ticks", steps := [.mindex tick] }
def tickBitmapRef (wordPosition : Expr) : StorageRef :=
  { base := "tickBitmap", steps := [.mindex wordPosition] }
def positionsRef (key : Expr) : StorageRef :=
  { base := "positions", steps := [.mindex key] }
def positionsF (key : Expr) (field : Ident) : StorageRef :=
  { base := "positions", steps := [.mindex key, .field field] }
def observationsRef (index : Expr) : StorageRef :=
  { base := "observations", steps := [.aindex index] }
def observationsF (index : Expr) (field : Ident) : StorageRef :=
  { base := "observations", steps := [.aindex index, .field field] }
def observationsRawF (index : Expr) (field : Ident) : StorageRef :=
  { base := "observationsRaw", steps := [.mindex index, .field field] }
def feeGrowthGlobal0X128Ref : StorageRef := { base := "feeGrowthGlobal0X128" }
def feeGrowthGlobal1X128Ref : StorageRef := { base := "feeGrowthGlobal1X128" }
def liquidityRef : StorageRef := { base := "liquidity" }

/-! ## Storage declarations and layout -/

def slot0StructTy : StorageType :=
  .struct "Slot0"
    [ ("sqrtPriceX96", uint160St), ("tick", int24St), ("observationIndex", uint16St),
      ("observationCardinality", uint16St), ("observationCardinalityNext", uint16St),
      ("feeProtocol", uint8St), ("unlocked", boolSt) ]

def protocolFeesStructTy : StorageType :=
  .struct "ProtocolFees" [("token0", uint128St), ("token1", uint128St)]

def tickInfoStructTy : StorageType :=
  .struct "Tick.Info"
    [ ("liquidityGross", uint128St), ("liquidityNet", int128St),
      ("feeGrowthOutside0X128", uint256St), ("feeGrowthOutside1X128", uint256St),
      ("tickCumulativeOutside", int56St), ("secondsPerLiquidityOutsideX128", uint160St),
      ("secondsOutside", uint32St), ("initialized", boolSt) ]

def positionInfoStructTy : StorageType :=
  .struct "Position.Info"
    [ ("liquidity", uint128St), ("feeGrowthInside0LastX128", uint256St),
      ("feeGrowthInside1LastX128", uint256St), ("tokensOwed0", uint128St),
      ("tokensOwed1", uint128St) ]

def observationStructTy : StorageType :=
  .struct "Oracle.Observation"
    [ ("blockTimestamp", uint32St), ("tickCumulative", int56St),
      ("secondsPerLiquidityCumulativeX128", uint160St), ("initialized", boolSt) ]

def slot0StructDecl : StructDecl :=
  { name := "Slot0"
    fields :=
      [ { name := "sqrtPriceX96", ty := uint160St }, { name := "tick", ty := int24St },
        { name := "observationIndex", ty := uint16St },
        { name := "observationCardinality", ty := uint16St },
        { name := "observationCardinalityNext", ty := uint16St },
        { name := "feeProtocol", ty := uint8St }, { name := "unlocked", ty := boolSt } ] }

def protocolFeesStructDecl : StructDecl :=
  { name := "ProtocolFees"
    fields := [ { name := "token0", ty := uint128St }, { name := "token1", ty := uint128St } ] }

def tickInfoStructDecl : StructDecl :=
  { name := "Tick.Info"
    fields :=
      [ { name := "liquidityGross", ty := uint128St }, { name := "liquidityNet", ty := int128St },
        { name := "feeGrowthOutside0X128", ty := uint256St },
        { name := "feeGrowthOutside1X128", ty := uint256St },
        { name := "tickCumulativeOutside", ty := int56St },
        { name := "secondsPerLiquidityOutsideX128", ty := uint160St },
        { name := "secondsOutside", ty := uint32St }, { name := "initialized", ty := boolSt } ] }

def positionInfoStructDecl : StructDecl :=
  { name := "Position.Info"
    fields :=
      [ { name := "liquidity", ty := uint128St },
        { name := "feeGrowthInside0LastX128", ty := uint256St },
        { name := "feeGrowthInside1LastX128", ty := uint256St },
        { name := "tokensOwed0", ty := uint128St }, { name := "tokensOwed1", ty := uint128St } ] }

def observationStructDecl : StructDecl :=
  { name := "Oracle.Observation"
    fields :=
      [ { name := "blockTimestamp", ty := uint32St }, { name := "tickCumulative", ty := int56St },
        { name := "secondsPerLiquidityCumulativeX128", ty := uint160St },
        { name := "initialized", ty := boolSt } ] }

def storageDecls : List StorageDecl :=
  [ { name := "slot0", ty := slot0StructTy },
    { name := "feeGrowthGlobal0X128", ty := uint256St },
    { name := "feeGrowthGlobal1X128", ty := uint256St },
    { name := "protocolFees", ty := protocolFeesStructTy },
    { name := "liquidity", ty := uint128St },
    { name := "ticks", ty := .mapping (.int int24Int) tickInfoStructTy },
    { name := "tickBitmap", ty := .mapping (.int int16Int) uint256St },
    { name := "positions", ty := .mapping (.bytes bytes32Width) positionInfoStructTy },
    { name := "observations", ty := .array observationStructTy 65535 },
    { name := "observationsRaw", ty := .mapping (.int uint256Int) observationStructTy } ]

def structs : List StructDecl :=
  [ slot0StructDecl, protocolFeesStructDecl, tickInfoStructDecl, positionInfoStructDecl,
    observationStructDecl ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def ticksBase (tick : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord tick) ⟨5⟩

def tickBitmapSlot (wordPosition : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord wordPosition) ⟨6⟩

def positionsBase (key : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord key) ⟨7⟩

def observationBase (index : KeyValue) : Ethereum.UInt256 :=
  ⟨8⟩ + Ethereum.UInt256.ofNat (keyValueToWord index).toNat

def loc (slot : Ethereum.UInt256) (offset : Fin 32) (size : Fin 33)
    (hbound : offset.val + size.val - 1 < 32) (ty : ElemType) : StorageLoc :=
  { slot := slot, offset := offset, size := size, hbound := hbound, type := ty }

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "slot0", steps := [.field "sqrtPriceX96"] }, _ =>
      some (loc ⟨0⟩ ⟨0, by decide⟩ ⟨20, by decide⟩ (by decide) (.int uint160Int))
  | { base := "slot0", steps := [.field "tick"] }, _ =>
      some (loc ⟨0⟩ ⟨20, by decide⟩ ⟨3, by decide⟩ (by decide) (.int int24Int))
  | { base := "slot0", steps := [.field "observationIndex"] }, _ =>
      some (loc ⟨0⟩ ⟨23, by decide⟩ ⟨2, by decide⟩ (by decide) (.int uint16Int))
  | { base := "slot0", steps := [.field "observationCardinality"] }, _ =>
      some (loc ⟨0⟩ ⟨25, by decide⟩ ⟨2, by decide⟩ (by decide) (.int uint16Int))
  | { base := "slot0", steps := [.field "observationCardinalityNext"] }, _ =>
      some (loc ⟨0⟩ ⟨27, by decide⟩ ⟨2, by decide⟩ (by decide) (.int uint16Int))
  | { base := "slot0", steps := [.field "feeProtocol"] }, _ =>
      some (loc ⟨0⟩ ⟨29, by decide⟩ ⟨1, by decide⟩ (by decide) (.int uint8Int))
  | { base := "slot0", steps := [.field "unlocked"] }, _ =>
      some (loc ⟨0⟩ ⟨30, by decide⟩ ⟨1, by decide⟩ (by decide) .bool)
  | { base := "feeGrowthGlobal0X128", steps := [] }, _ =>
      some (loc ⟨1⟩ ⟨0, by decide⟩ ⟨32, by decide⟩ (by decide) (.int uint256Int))
  | { base := "feeGrowthGlobal1X128", steps := [] }, _ =>
      some (loc ⟨2⟩ ⟨0, by decide⟩ ⟨32, by decide⟩ (by decide) (.int uint256Int))
  | { base := "protocolFees", steps := [.field "token0"] }, _ =>
      some (loc ⟨3⟩ ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide) (.int uint128Int))
  | { base := "protocolFees", steps := [.field "token1"] }, _ =>
      some (loc ⟨3⟩ ⟨16, by decide⟩ ⟨16, by decide⟩ (by decide) (.int uint128Int))
  | { base := "liquidity", steps := [] }, _ =>
      some (loc ⟨4⟩ ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide) (.int uint128Int))
  | { base := "ticks", steps := [.mindex tick, .field "liquidityGross"] }, _ =>
      some (loc (ticksBase tick) ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide) (.int uint128Int))
  | { base := "ticks", steps := [.mindex tick, .field "liquidityNet"] }, _ =>
      some (loc (ticksBase tick) ⟨16, by decide⟩ ⟨16, by decide⟩ (by decide) (.int int128Int))
  | { base := "ticks", steps := [.mindex tick, .field "feeGrowthOutside0X128"] }, _ =>
      some (loc (ticksBase tick + ⟨1⟩) ⟨0, by decide⟩ ⟨32, by decide⟩ (by decide) (.int uint256Int))
  | { base := "ticks", steps := [.mindex tick, .field "feeGrowthOutside1X128"] }, _ =>
      some (loc (ticksBase tick + ⟨2⟩) ⟨0, by decide⟩ ⟨32, by decide⟩ (by decide) (.int uint256Int))
  | { base := "ticks", steps := [.mindex tick, .field "tickCumulativeOutside"] }, _ =>
      some (loc (ticksBase tick + ⟨3⟩) ⟨0, by decide⟩ ⟨7, by decide⟩ (by decide) (.int int56Int))
  | { base := "ticks", steps := [.mindex tick, .field "secondsPerLiquidityOutsideX128"] }, _ =>
      some (loc (ticksBase tick + ⟨3⟩) ⟨7, by decide⟩ ⟨20, by decide⟩ (by decide) (.int uint160Int))
  | { base := "ticks", steps := [.mindex tick, .field "secondsOutside"] }, _ =>
      some (loc (ticksBase tick + ⟨3⟩) ⟨27, by decide⟩ ⟨4, by decide⟩ (by decide) (.int uint32Int))
  | { base := "ticks", steps := [.mindex tick, .field "initialized"] }, _ =>
      some (loc (ticksBase tick + ⟨3⟩) ⟨31, by decide⟩ ⟨1, by decide⟩ (by decide) .bool)
  | { base := "tickBitmap", steps := [.mindex wordPosition] }, _ =>
      some (loc (tickBitmapSlot wordPosition) ⟨0, by decide⟩ ⟨32, by decide⟩ (by decide) (.int uint256Int))
  | { base := "positions", steps := [.mindex key, .field "liquidity"] }, _ =>
      some (loc (positionsBase key) ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide) (.int uint128Int))
  | { base := "positions", steps := [.mindex key, .field "feeGrowthInside0LastX128"] }, _ =>
      some (loc (positionsBase key + ⟨1⟩) ⟨0, by decide⟩ ⟨32, by decide⟩ (by decide) (.int uint256Int))
  | { base := "positions", steps := [.mindex key, .field "feeGrowthInside1LastX128"] }, _ =>
      some (loc (positionsBase key + ⟨2⟩) ⟨0, by decide⟩ ⟨32, by decide⟩ (by decide) (.int uint256Int))
  | { base := "positions", steps := [.mindex key, .field "tokensOwed0"] }, _ =>
      some (loc (positionsBase key + ⟨3⟩) ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide) (.int uint128Int))
  | { base := "positions", steps := [.mindex key, .field "tokensOwed1"] }, _ =>
      some (loc (positionsBase key + ⟨3⟩) ⟨16, by decide⟩ ⟨16, by decide⟩ (by decide) (.int uint128Int))
  | { base := "observations", steps := [.aindex index, .field "blockTimestamp"] }, _ =>
      some (loc (observationBase index) ⟨0, by decide⟩ ⟨4, by decide⟩ (by decide) (.int uint32Int))
  | { base := "observations", steps := [.aindex index, .field "tickCumulative"] }, _ =>
      some (loc (observationBase index) ⟨4, by decide⟩ ⟨7, by decide⟩ (by decide) (.int int56Int))
  | { base := "observations", steps := [.aindex index, .field "secondsPerLiquidityCumulativeX128"] }, _ =>
      some (loc (observationBase index) ⟨11, by decide⟩ ⟨20, by decide⟩ (by decide) (.int uint160Int))
  | { base := "observations", steps := [.aindex index, .field "initialized"] }, _ =>
      some (loc (observationBase index) ⟨31, by decide⟩ ⟨1, by decide⟩ (by decide) .bool)
  | { base := "observationsRaw", steps := [.mindex index, .field "blockTimestamp"] }, _ =>
      some (loc (observationBase index) ⟨0, by decide⟩ ⟨4, by decide⟩ (by decide) (.int uint32Int))
  | { base := "observationsRaw", steps := [.mindex index, .field "tickCumulative"] }, _ =>
      some (loc (observationBase index) ⟨4, by decide⟩ ⟨7, by decide⟩ (by decide) (.int int56Int))
  | { base := "observationsRaw", steps := [.mindex index, .field "secondsPerLiquidityCumulativeX128"] }, _ =>
      some (loc (observationBase index) ⟨11, by decide⟩ ⟨20, by decide⟩ (by decide) (.int uint160Int))
  | { base := "observationsRaw", steps := [.mindex index, .field "initialized"] }, _ =>
      some (loc (observationBase index) ⟨31, by decide⟩ ⟨1, by decide⟩ (by decide) .bool)
  | _, _ => none

def storageLayout : StorageLayout :=
  solidityStorageLayout storageLayoutRaw

/-! ## Shared source patterns -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def varRef (name : Ident) : StorageRef :=
  { base := name }

def tuple0 (e : Expr) : Expr := .tupleGet e 0
def tuple1 (e : Expr) : Expr := .tupleGet e 1
def tuple2 (e : Expr) : Expr := .tupleGet e 2
def tuple3 (e : Expr) : Expr := .tupleGet e 3
def tuple4 (e : Expr) : Expr := .tupleGet e 4
def tuple5 (e : Expr) : Expr := .tupleGet e 5
def tuple6 (e : Expr) : Expr := .tupleGet e 6
def tuple7 (e : Expr) : Expr := .tupleGet e 7

def andE (lhs rhs : Expr) : Expr := .binary .and lhs rhs
def orE (lhs rhs : Expr) : Expr := .binary .or lhs rhs
def eqE (lhs rhs : Expr) : Expr := .binary .eq lhs rhs
def neE (lhs rhs : Expr) : Expr := .binary .ne lhs rhs
def ltE (lhs rhs : Expr) : Expr := .binary .lt lhs rhs
def leE (lhs rhs : Expr) : Expr := .binary .le lhs rhs
def gtE (lhs rhs : Expr) : Expr := .binary .gt lhs rhs
def geE (lhs rhs : Expr) : Expr := .binary .ge lhs rhs
def addE (lhs rhs : Expr) : Expr := .binary .add lhs rhs
def subE (lhs rhs : Expr) : Expr := .binary .sub lhs rhs
def mulE (lhs rhs : Expr) : Expr := .binary .mul lhs rhs
def divE (lhs rhs : Expr) : Expr := .binary .div lhs rhs
def modE (lhs rhs : Expr) : Expr := .binary .mod lhs rhs
def shlE (lhs rhs : Expr) : Expr := .binary .shl lhs rhs
def shrE (lhs rhs : Expr) : Expr := .binary .shr lhs rhs
def bitAndE (lhs rhs : Expr) : Expr := .binary .bitAnd lhs rhs
def bitXorE (lhs rhs : Expr) : Expr := .binary .bitXor lhs rhs
def notE (e : Expr) : Expr := .unary .not e

def sdivTowardZeroE (lhs rhs : Expr) : Expr :=
  .ite (ltE lhs (.intLit 0))
    (subE (.intLit 0) (divE (subE (.intLit 0) lhs) rhs))
    (divE lhs rhs)

def uint256Modulus : Expr := .intLit (2 ^ 256)
def uint256MaxExpr : Expr := .intLit (2 ^ 256 - 1)
def uint128Modulus : Expr := .intLit (2 ^ 128)
def uint32Modulus : Expr := .intLit (2 ^ 32)
def uint160Modulus : Expr := .intLit (2 ^ 160)
def uint160MaxExpr : Expr := .intLit (2 ^ 160 - 1)
def fixedPoint128Q128 : Expr := .intLit (2 ^ 128)
def shift128 : Expr := .intLit 128
def shift32 : Expr := .intLit 32
def shift96 : Expr := .intLit 96
def feeDenominator : Expr := .intLit 1000000
def minTick : Expr := .intLit (-887272)
def maxTick : Expr := .intLit 887272
def minSqrtRatio : Expr := .intLit 4295128739
def maxSqrtRatio : Expr := .intLit 1461446703485210103287273052203988822378723970342

def localBytesLength (name : Ident) : Expr :=
  .arrayLength .localVar (varRef name)

def localArrayLength (name : Ident) : Expr :=
  .arrayLength .localVar (varRef name)

def localArrayElem (name : Ident) (idx : Expr) : StorageRef :=
  { base := name, steps := [.aindex idx] }

def uint32Wrap (e : Expr) : Expr :=
  modE e uint32Modulus

def uint160Wrap (e : Expr) : Expr :=
  modE e uint160Modulus

def uint256Wrap (e : Expr) : Expr :=
  modE e uint256Modulus

def int56Wrap (e : Expr) : Expr :=
  let modulus : Expr := .intLit (2 ^ 56)
  let half : Expr := .intLit (2 ^ 55)
  let wrapped : Expr := modE e modulus
  .ite (geE wrapped half) (subE wrapped modulus) wrapped

def blockTimestamp32 : Expr :=
  uint32Wrap (.env .timestamp)

def noDelegateCall (v : PoolImmutables) : List Stmt :=
  [ .require (eqE (.env .this) (addrLit v.original)) ]

def lockPrefix : List Stmt :=
  [ .require (.storage (slot0F "unlocked")),
    .assign .storage (slot0F "unlocked") (.boolLit false) ]

def lockSuffix : List Stmt :=
  [ .assign .storage (slot0F "unlocked") (.boolLit true) ]

def onlyFactoryOwner (v : PoolImmutables) : List Stmt :=
  [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
    .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner" (perm := false),
    .require (eqE (.env .caller) (.var "_factoryOwner")) ]

def safeTransfer (token recipient amount : Expr) (tag : Ident) : List Stmt :=
  [ .lowLevelCall token (.intLit 0) (.abiEncodeCall "transfer" [recipient, amount])
      (tag ++ "_success") (tag ++ "_data"),
    .require
      (andE (.var (tag ++ "_success"))
        (orE (eqE (localBytesLength (tag ++ "_data")) (.intLit 0))
          (.abiDecode boolTy (.var (tag ++ "_data"))))) ]

def feeProtocolEnabled (feeProtocol : Expr) : Expr :=
  orE (eqE feeProtocol (.intLit 0))
    (andE (geE feeProtocol (.intLit 4)) (leE feeProtocol (.intLit 10)))

def positionKey (owner tickLower tickUpper : Expr) : Expr :=
  .keccak256 (.abiEncodePacked [(addr, owner), (int24, tickLower), (int24, tickUpper)])

def wordAdd (lhs rhs : Expr) : Expr :=
  modE (addE lhs rhs) uint256Modulus

def wordSub (lhs rhs : Expr) : Expr :=
  modE (subE lhs rhs) uint256Modulus

def wordMul (lhs rhs : Expr) : Expr :=
  modE (mulE lhs rhs) uint256Modulus

def checkedWordAddLe (lhs rhs upper : Expr) : List Stmt :=
  [ .require (geE (wordAdd lhs rhs) lhs),
    .require (leE (wordAdd lhs rhs) upper) ]

def balanceOfInto (token : Expr) (out tag : Ident) : List Stmt :=
  [ .lowLevelCall token (.intLit 0) (.abiEncodeCall "balanceOf" [.env .this])
      (tag ++ "_success") (tag ++ "_data") (perm := false),
    .require
      (andE (.var (tag ++ "_success"))
        (geE (localBytesLength (tag ++ "_data")) (.intLit 32))),
    .letDecl out (some uint256) (.abiDecode uint256 (.var (tag ++ "_data"))) ]

def mulDivLet (out : Ident) (a b denominator : Expr) : List Stmt :=
  [ .require (gtE denominator (.intLit 0)),
    .letDecl out (some uint256) (divE (mulE a b) denominator),
    .require (leE (.var out) uint256MaxExpr) ]

def mulDivRoundingUpLet (out : Ident) (a b denominator : Expr) : List Stmt :=
  mulDivLet out a b denominator ++
  [ Stmt.ite (gtE (modE (mulE a b) denominator) (.intLit 0))
      [ .require (ltE (.var out) uint256MaxExpr),
        .assign .localVar (varRef out) (addE (.var out) (.intLit 1)) ]
      [] ]

def divRoundingUpLet (out : Ident) (numerator denominator : Expr) : List Stmt :=
  [ .require (gtE denominator (.intLit 0)),
    .letDecl out (some uint256) (divE numerator denominator),
    Stmt.ite (gtE (modE numerator denominator) (.intLit 0))
      [ .require (ltE (.var out) uint256MaxExpr),
        .assign .localVar (varRef out) (addE (.var out) (.intLit 1)) ]
      [] ]

def uint128Wrap (e : Expr) : Expr :=
  modE e uint128Modulus

def checkTicksBody (tickLower tickUpper : Expr) : List Stmt :=
  [ .require (ltE tickLower tickUpper),
    .require (geE tickLower minTick),
    .require (leE tickUpper maxTick) ]

def tickRatioStep (mask constant : Int) : List Stmt :=
  [ Stmt.ite (neE (bitAndE (.var "absTick") (.intLit mask)) (.intLit 0))
      [ .assign .localVar (varRef "ratio")
          (shrE (mulE (.var "ratio") (.intLit constant)) shift128) ]
      [] ]

def msbStep (shift : Nat) (threshold : Int) : List Stmt :=
  [ .letDecl "f" (some uint256)
      (.ite (gtE (.var "r") (.intLit threshold)) (.intLit (2 ^ shift)) (.intLit 0)),
    .assign .localVar (varRef "msb") (addE (.var "msb") (.var "f")),
    .assign .localVar (varRef "r") (shrE (.var "r") (.var "f")) ]

def logStep (bit : Nat) (shiftAfter : Bool) : List Stmt :=
  [ .assign .localVar (varRef "r") (shrE (mulE (.var "r") (.var "r")) (.intLit 127)),
    .letDecl "f" (some uint256) (shrE (.var "r") shift128),
    .assign .localVar (varRef "log_2")
      (addE (.var "log_2") (mulE (.var "f") (.intLit (2 ^ bit)))) ] ++
  (if shiftAfter then
    [ .assign .localVar (varRef "r") (shrE (.var "r") (.var "f")) ]
  else
    [])

/-! ## Internal library/helper functions -/

def getSqrtRatioAtTickFunction : FunctionDecl :=
  { name := "getSqrtRatioAtTick"
    params := [{ name := "tick", ty := int24 }]
    returnType := [uint160]
    body :=
      [ .letDecl "absTick" (some uint256)
          (.ite (ltE (.var "tick") (.intLit 0))
            (subE (.intLit 0) (.var "tick"))
            (.var "tick")),
        .require (leE (.var "absTick") maxTick),
        .letDecl "ratio" (some uint256)
          (.ite (neE (bitAndE (.var "absTick") (.intLit 0x1)) (.intLit 0))
            (.intLit 0xfffcb933bd6fad37aa2d162d1a594001)
            fixedPoint128Q128) ] ++
      tickRatioStep 0x2 0xfff97272373d413259a46990580e213a ++
      tickRatioStep 0x4 0xfff2e50f5f656932ef12357cf3c7fdcc ++
      tickRatioStep 0x8 0xffe5caca7e10e4e61c3624eaa0941cd0 ++
      tickRatioStep 0x10 0xffcb9843d60f6159c9db58835c926644 ++
      tickRatioStep 0x20 0xff973b41fa98c081472e6896dfb254c0 ++
      tickRatioStep 0x40 0xff2ea16466c96a3843ec78b326b52861 ++
      tickRatioStep 0x80 0xfe5dee046a99a2a811c461f1969c3053 ++
      tickRatioStep 0x100 0xfcbe86c7900a88aedcffc83b479aa3a4 ++
      tickRatioStep 0x200 0xf987a7253ac413176f2b074cf7815e54 ++
      tickRatioStep 0x400 0xf3392b0822b70005940c7a398e4b70f3 ++
      tickRatioStep 0x800 0xe7159475a2c29b7443b29c7fa6e889d9 ++
      tickRatioStep 0x1000 0xd097f3bdfd2022b8845ad8f792aa5825 ++
      tickRatioStep 0x2000 0xa9f746462d870fdf8a65dc1f90e061e5 ++
      tickRatioStep 0x4000 0x70d869a156d2a1b890bb3df62baf32f7 ++
      tickRatioStep 0x8000 0x31be135f97d08fd981231505542fcfa6 ++
      tickRatioStep 0x10000 0x9aa508b5b7a84e1c677de54f3e99bc9 ++
      tickRatioStep 0x20000 0x5d6af8dedb81196699c329225ee604 ++
      tickRatioStep 0x40000 0x2216e584f5fa1ea926041bedfe98 ++
      tickRatioStep 0x80000 0x48a170391f7dc42444e8fa2 ++
      [ Stmt.ite (gtE (.var "tick") (.intLit 0))
          [ .assign .localVar (varRef "ratio") (divE uint256MaxExpr (.var "ratio")) ]
          [],
        .return
          [ addE (shrE (.var "ratio") shift32)
              (.ite (eqE (modE (.var "ratio") uint32Modulus) (.intLit 0))
                (.intLit 0)
                (.intLit 1)) ] ] }

def getTickAtSqrtRatioFunction : FunctionDecl :=
  { name := "getTickAtSqrtRatio"
    params := [{ name := "sqrtPriceX96", ty := uint160 }]
    returnType := [int24]
    body :=
      [ .require (andE (geE (.var "sqrtPriceX96") minSqrtRatio)
          (ltE (.var "sqrtPriceX96") maxSqrtRatio)),
        .letDecl "ratio" (some uint256) (shlE (.var "sqrtPriceX96") shift32),
        .letDecl "r" (some uint256) (.var "ratio"),
        .letDecl "msb" (some uint256) (.intLit 0) ] ++
      msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ++
      msbStep 6 0xFFFFFFFFFFFFFFFF ++
      msbStep 5 0xFFFFFFFF ++
      msbStep 4 0xFFFF ++
      msbStep 3 0xFF ++
      msbStep 2 0xF ++
      msbStep 1 0x3 ++
      [ .letDecl "f" (some uint256)
          (.ite (gtE (.var "r") (.intLit 0x1)) (.intLit 1) (.intLit 0)),
        .assign .localVar (varRef "msb") (addE (.var "msb") (.var "f")),
        Stmt.ite (geE (.var "msb") (.intLit 128))
          [ .assign .localVar (varRef "r")
              (shrE (.var "ratio") (subE (.var "msb") (.intLit 127))) ]
          [ .assign .localVar (varRef "r")
              (shlE (.var "ratio") (subE (.intLit 127) (.var "msb"))) ],
        .letDecl "log_2" (some int256)
          (mulE (subE (.var "msb") (.intLit 128)) (.intLit (2 ^ 64))) ] ++
      logStep 63 true ++
      logStep 62 true ++
      logStep 61 true ++
      logStep 60 true ++
      logStep 59 true ++
      logStep 58 true ++
      logStep 57 true ++
      logStep 56 true ++
      logStep 55 true ++
      logStep 54 true ++
      logStep 53 true ++
      logStep 52 true ++
      logStep 51 true ++
      logStep 50 false ++
      [ .letDecl "log_sqrt10001" (some int256)
          (mulE (.var "log_2") (.intLit 255738958999603826347141)),
        .letDecl "tickLow" (some int24)
          (divE
            (subE (.var "log_sqrt10001") (.intLit 3402992956809132418596140100660247210))
            fixedPoint128Q128),
        .letDecl "tickHi" (some int24)
          (divE
            (addE (.var "log_sqrt10001") (.intLit 291339464771989622907027621153398088495))
            fixedPoint128Q128),
        .internalCall "getSqrtRatioAtTick" [.var "tickHi"] "sqrtRatioAtTickHi",
        .return
          [ .ite (eqE (.var "tickLow") (.var "tickHi"))
              (.var "tickLow")
              (.ite (leE (.var "sqrtRatioAtTickHi") (.var "sqrtPriceX96"))
                (.var "tickHi")
                (.var "tickLow")) ] ] }

def oracleLteFunction : FunctionDecl :=
  { name := "oracleLte"
    params :=
      [ { name := "time", ty := uint32 }, { name := "a", ty := uint32 },
        { name := "b", ty := uint32 } ]
    returnType := [boolTy]
    body :=
      [ Stmt.ite (andE (leE (.var "a") (.var "time")) (leE (.var "b") (.var "time")))
          [ .return [leE (.var "a") (.var "b")] ]
          [],
        .letDecl "aAdjusted" (some uint256)
          (.ite (gtE (.var "a") (.var "time"))
            (.var "a")
            (addE (.var "a") uint32Modulus)),
        .letDecl "bAdjusted" (some uint256)
          (.ite (gtE (.var "b") (.var "time"))
            (.var "b")
            (addE (.var "b") uint32Modulus)),
        .return [leE (.var "aAdjusted") (.var "bAdjusted")] ] }

def oracleTransformFunction : FunctionDecl :=
  { name := "oracleTransform"
    params :=
      [ { name := "lastBlockTimestamp", ty := uint32 },
        { name := "lastTickCumulative", ty := int56 },
        { name := "lastSecondsPerLiquidityCumulativeX128", ty := uint160 },
        { name := "blockTimestamp", ty := uint32 }, { name := "tick", ty := int24 },
        { name := "liquidity", ty := uint128 } ]
    returnType := [uint32, int56, uint160, boolTy]
    body :=
      [ .letDecl "delta" (some uint32)
          (uint32Wrap (subE (.var "blockTimestamp") (.var "lastBlockTimestamp"))),
        .letDecl "liquidityDenominator" (some uint128)
          (.ite (gtE (.var "liquidity") (.intLit 0)) (.var "liquidity") (.intLit 1)),
        .letDecl "tickCumulative" (some int56)
          (int56Wrap
            (addE (.var "lastTickCumulative") (mulE (.var "tick") (.var "delta")))),
        .letDecl "secondsPerLiquidityCumulativeX128" (some uint160)
          (uint160Wrap
            (addE (.var "lastSecondsPerLiquidityCumulativeX128")
              (divE (shlE (.var "delta") shift128) (.var "liquidityDenominator")))),
        .return
          [ .var "blockTimestamp", .var "tickCumulative",
            .var "secondsPerLiquidityCumulativeX128", .boolLit true ] ] }

def getSurroundingObservationsFunction : FunctionDecl :=
  { name := "getSurroundingObservations"
    params :=
      [ { name := "time", ty := uint32 }, { name := "target", ty := uint32 },
        { name := "tick", ty := int24 }, { name := "index", ty := uint16 },
        { name := "liquidity", ty := uint128 }, { name := "cardinality", ty := uint16 } ]
    returnType := [uint32, int56, uint160, boolTy, uint32, int56, uint160, boolTy]
    body :=
      [ .letStorage "beforeOrAt" (observationsRef (.var "index")),
        .letDecl "atOrAfterBlockTimestamp" (some uint32) (.intLit 0),
        .letDecl "atOrAfterTickCumulative" (some int56) (.intLit 0),
        .letDecl "atOrAfterSecondsPerLiquidityCumulativeX128" (some uint160) (.intLit 0),
        .letDecl "atOrAfterInitialized" (some boolTy) (.boolLit false),
        .internalCall "oracleLte"
          [.var "time", .field (.var "beforeOrAt") "blockTimestamp", .var "target"]
          "targetAtOrAfterNewest",
        Stmt.ite (.var "targetAtOrAfterNewest")
          [ Stmt.ite (eqE (.field (.var "beforeOrAt") "blockTimestamp") (.var "target"))
              [ .return
                  [ .field (.var "beforeOrAt") "blockTimestamp",
                    .field (.var "beforeOrAt") "tickCumulative",
                    .field (.var "beforeOrAt") "secondsPerLiquidityCumulativeX128",
                    .field (.var "beforeOrAt") "initialized",
                    .var "atOrAfterBlockTimestamp", .var "atOrAfterTickCumulative",
                    .var "atOrAfterSecondsPerLiquidityCumulativeX128",
                    .var "atOrAfterInitialized" ] ]
              [],
            .internalCall "oracleTransform"
              [ .field (.var "beforeOrAt") "blockTimestamp",
                .field (.var "beforeOrAt") "tickCumulative",
                .field (.var "beforeOrAt") "secondsPerLiquidityCumulativeX128",
                .var "target", .var "tick", .var "liquidity" ]
              "transformed",
            .return
              [ .field (.var "beforeOrAt") "blockTimestamp",
                .field (.var "beforeOrAt") "tickCumulative",
                .field (.var "beforeOrAt") "secondsPerLiquidityCumulativeX128",
                .field (.var "beforeOrAt") "initialized",
                tuple0 (.var "transformed"), tuple1 (.var "transformed"),
                tuple2 (.var "transformed"), tuple3 (.var "transformed") ] ]
          [],
        .letDecl "oldestIndex" (some uint256)
          (modE (addE (.var "index") (.intLit 1)) (.var "cardinality")),
        .letStorage "oldest" (observationsRef (.var "oldestIndex")),
        Stmt.ite (.unary .not (.field (.var "oldest") "initialized"))
          [ .letStorage "oldest" (observationsRef (.intLit 0)) ]
          [],
        .internalCall "oracleLte"
          [.var "time", .field (.var "oldest") "blockTimestamp", .var "target"]
          "targetAtOrAfterOldest",
        .require (.var "targetAtOrAfterOldest"),
        .letDecl "l" (some uint256) (.var "oldestIndex"),
        .letDecl "r" (some uint256) (addE (.var "l") (subE (.var "cardinality") (.intLit 1))),
        .while (.boolLit true)
          [ .letDecl "i" (some uint256) (divE (addE (.var "l") (.var "r")) (.intLit 2)),
            .letStorage "beforeOrAt" (observationsRef (modE (.var "i") (.var "cardinality"))),
            Stmt.ite (.unary .not (.field (.var "beforeOrAt") "initialized"))
              [ .assign .localVar (varRef "l") (addE (.var "i") (.intLit 1)),
                .continue ]
              [],
            .letStorage "atOrAfter"
              (observationsRef (modE (addE (.var "i") (.intLit 1)) (.var "cardinality"))),
            .internalCall "oracleLte"
              [.var "time", .field (.var "beforeOrAt") "blockTimestamp", .var "target"]
              "targetAtOrAfter",
            .internalCall "oracleLte"
              [.var "time", .var "target", .field (.var "atOrAfter") "blockTimestamp"]
              "targetAtOrBeforeAfter",
            Stmt.ite (andE (.var "targetAtOrAfter") (.var "targetAtOrBeforeAfter"))
              [ .return
                  [ .field (.var "beforeOrAt") "blockTimestamp",
                    .field (.var "beforeOrAt") "tickCumulative",
                    .field (.var "beforeOrAt") "secondsPerLiquidityCumulativeX128",
                    .field (.var "beforeOrAt") "initialized",
                    .field (.var "atOrAfter") "blockTimestamp",
                    .field (.var "atOrAfter") "tickCumulative",
                    .field (.var "atOrAfter") "secondsPerLiquidityCumulativeX128",
                    .field (.var "atOrAfter") "initialized" ] ]
              [],
            Stmt.ite (.unary .not (.var "targetAtOrAfter"))
              [ .assign .localVar (varRef "r") (subE (.var "i") (.intLit 1)) ]
              [ .assign .localVar (varRef "l") (addE (.var "i") (.intLit 1)) ] ],
        .return
          [ .field (.var "oldest") "blockTimestamp",
            .field (.var "oldest") "tickCumulative",
            .field (.var "oldest") "secondsPerLiquidityCumulativeX128",
            .field (.var "oldest") "initialized",
            .var "atOrAfterBlockTimestamp", .var "atOrAfterTickCumulative",
            .var "atOrAfterSecondsPerLiquidityCumulativeX128", .var "atOrAfterInitialized" ] ] }

def observeSingleFunction : FunctionDecl :=
  { name := "observeSingle"
    params :=
      [ { name := "time", ty := uint32 }, { name := "secondsAgo", ty := uint32 },
        { name := "tick", ty := int24 }, { name := "index", ty := uint16 },
        { name := "liquidity", ty := uint128 }, { name := "cardinality", ty := uint16 } ]
    returnType := [int56, uint160]
    body :=
      [ Stmt.ite (eqE (.var "secondsAgo") (.intLit 0))
          [ .letStorage "last" (observationsRef (.var "index")),
            Stmt.ite (neE (.field (.var "last") "blockTimestamp") (.var "time"))
              [ .internalCall "oracleTransform"
                  [ .field (.var "last") "blockTimestamp",
                    .field (.var "last") "tickCumulative",
                    .field (.var "last") "secondsPerLiquidityCumulativeX128",
                    .var "time", .var "tick", .var "liquidity" ]
                  "lastTransformed",
                .return [tuple1 (.var "lastTransformed"), tuple2 (.var "lastTransformed")] ]
              [ .return
                  [ .field (.var "last") "tickCumulative",
                    .field (.var "last") "secondsPerLiquidityCumulativeX128" ] ] ]
          [],
        .letDecl "target" (some uint32) (uint32Wrap (subE (.var "time") (.var "secondsAgo"))),
        .internalCall "getSurroundingObservations"
          [.var "time", .var "target", .var "tick", .var "index", .var "liquidity",
            .var "cardinality"]
          "surrounding",
        Stmt.ite (eqE (.var "target") (tuple0 (.var "surrounding")))
          [ .return [tuple1 (.var "surrounding"), tuple2 (.var "surrounding")] ]
          [],
        Stmt.ite (eqE (.var "target") (tuple4 (.var "surrounding")))
          [ .return [tuple5 (.var "surrounding"), tuple6 (.var "surrounding")] ]
          [],
        .letDecl "observationTimeDelta" (some uint32)
          (uint32Wrap (subE (tuple4 (.var "surrounding")) (tuple0 (.var "surrounding")))),
        .letDecl "targetDelta" (some uint32)
          (uint32Wrap (subE (.var "target") (tuple0 (.var "surrounding")))),
        .return
          [ int56Wrap
              (addE (tuple1 (.var "surrounding"))
                (mulE
                  (sdivTowardZeroE
                    (subE (tuple5 (.var "surrounding")) (tuple1 (.var "surrounding")))
                    (.var "observationTimeDelta"))
                  (.var "targetDelta"))),
            uint160Wrap
              (addE (tuple2 (.var "surrounding"))
                (divE
                  (mulE (subE (tuple6 (.var "surrounding")) (tuple2 (.var "surrounding")))
                    (.var "targetDelta"))
                  (.var "observationTimeDelta"))) ] ] }

def observeBodyFunction : FunctionDecl :=
  { name := "observeBody"
    params :=
      [ { name := "time", ty := uint32 },
        { name := "secondsAgos", ty := .dynamicArray uint32 },
        { name := "tick", ty := int24 }, { name := "index", ty := uint16 },
        { name := "liquidity", ty := uint128 }, { name := "cardinality", ty := uint16 } ]
    returnType := [.dynamicArray int56, .dynamicArray uint160]
    body :=
      [ .require (gtE (.var "cardinality") (.intLit 0)),
        .letDecl "tickCumulatives" (some (.dynamicArray int56))
          (.newArray int56St (localArrayLength "secondsAgos")),
        .letDecl "secondsPerLiquidityCumulativeX128s" (some (.dynamicArray uint160))
          (.newArray uint160St (localArrayLength "secondsAgos")),
        .letDecl "i" (some uint256) (.intLit 0),
        .while (ltE (.var "i") (localArrayLength "secondsAgos"))
          [ .internalCall "observeSingle"
              [ .var "time", .index (.var "secondsAgos") (.var "i"), .var "tick",
                .var "index", .var "liquidity", .var "cardinality" ]
              "observed",
            .assign .localVar (localArrayElem "tickCumulatives" (.var "i"))
              (tuple0 (.var "observed")),
            .assign .localVar (localArrayElem "secondsPerLiquidityCumulativeX128s" (.var "i"))
              (tuple1 (.var "observed")),
            .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ],
        .return [.var "tickCumulatives", .var "secondsPerLiquidityCumulativeX128s"] ] }

def liquidityAddDeltaFunction : FunctionDecl :=
  { name := "liquidityAddDelta"
    params := [{ name := "x", ty := uint128 }, { name := "y", ty := int128 }]
    returnType := [uint128]
    body :=
      [ Stmt.ite (ltE (.var "y") (.intLit 0))
          [ .letDecl "z" (some uint128) (uint128Wrap (subE (.var "x") (subE (.intLit 0) (.var "y")))),
            .require (ltE (.var "z") (.var "x")),
            .return [.var "z"] ]
          [ .letDecl "z" (some uint128) (uint128Wrap (addE (.var "x") (.var "y"))),
            .require (geE (.var "z") (.var "x")),
            .return [.var "z"] ] ] }

def oracleWriteFunction : FunctionDecl :=
  { name := "oracleWrite"
    params :=
      [ { name := "index", ty := uint16 }, { name := "blockTimestamp", ty := uint32 },
        { name := "tick", ty := int24 }, { name := "liquidity", ty := uint128 },
        { name := "cardinality", ty := uint16 }, { name := "cardinalityNext", ty := uint16 } ]
    returnType := [uint16, uint16]
    body :=
      [ .letStorage "last" (observationsRef (.var "index")),
        Stmt.ite (eqE (.field (.var "last") "blockTimestamp") (.var "blockTimestamp"))
          [ .return [.var "index", .var "cardinality"] ]
          [],
        .letDecl "cardinalityUpdated" (some uint16)
          (.ite (andE (gtE (.var "cardinalityNext") (.var "cardinality"))
              (eqE (.var "index") (subE (.var "cardinality") (.intLit 1))))
            (.var "cardinalityNext")
            (.var "cardinality")),
        .letDecl "indexUpdated" (some uint16)
          (modE (addE (.var "index") (.intLit 1)) (.var "cardinalityUpdated")),
        .internalCall "oracleTransform"
          [ .field (.var "last") "blockTimestamp",
            .field (.var "last") "tickCumulative",
            .field (.var "last") "secondsPerLiquidityCumulativeX128",
            .var "blockTimestamp", .var "tick", .var "liquidity" ]
          "transformed",
        .assign .storage (observationsF (.var "indexUpdated") "blockTimestamp")
          (tuple0 (.var "transformed")),
        .assign .storage (observationsF (.var "indexUpdated") "tickCumulative")
          (tuple1 (.var "transformed")),
        .assign .storage (observationsF (.var "indexUpdated") "secondsPerLiquidityCumulativeX128")
          (tuple2 (.var "transformed")),
        .assign .storage (observationsF (.var "indexUpdated") "initialized")
          (tuple3 (.var "transformed")),
        .return [.var "indexUpdated", .var "cardinalityUpdated"] ] }

def tickGetFeeGrowthInsideFunction : FunctionDecl :=
  { name := "tickGetFeeGrowthInside"
    params :=
      [ { name := "tickLower", ty := int24 }, { name := "tickUpper", ty := int24 },
        { name := "tickCurrent", ty := int24 },
        { name := "feeGrowthGlobal0X128", ty := uint256 },
        { name := "feeGrowthGlobal1X128", ty := uint256 } ]
    returnType := [uint256, uint256]
    body :=
      [ .letStorage "lower" (ticksRef (.var "tickLower")),
        .letStorage "upper" (ticksRef (.var "tickUpper")),
        .letDecl "feeGrowthBelow0X128" (some uint256)
          (.ite (geE (.var "tickCurrent") (.var "tickLower"))
            (.field (.var "lower") "feeGrowthOutside0X128")
            (wordSub (.var "feeGrowthGlobal0X128") (.field (.var "lower") "feeGrowthOutside0X128"))),
        .letDecl "feeGrowthBelow1X128" (some uint256)
          (.ite (geE (.var "tickCurrent") (.var "tickLower"))
            (.field (.var "lower") "feeGrowthOutside1X128")
            (wordSub (.var "feeGrowthGlobal1X128") (.field (.var "lower") "feeGrowthOutside1X128"))),
        .letDecl "feeGrowthAbove0X128" (some uint256)
          (.ite (ltE (.var "tickCurrent") (.var "tickUpper"))
            (.field (.var "upper") "feeGrowthOutside0X128")
            (wordSub (.var "feeGrowthGlobal0X128") (.field (.var "upper") "feeGrowthOutside0X128"))),
        .letDecl "feeGrowthAbove1X128" (some uint256)
          (.ite (ltE (.var "tickCurrent") (.var "tickUpper"))
            (.field (.var "upper") "feeGrowthOutside1X128")
            (wordSub (.var "feeGrowthGlobal1X128") (.field (.var "upper") "feeGrowthOutside1X128"))),
        .return
          [ wordSub (wordSub (.var "feeGrowthGlobal0X128") (.var "feeGrowthBelow0X128"))
              (.var "feeGrowthAbove0X128"),
            wordSub (wordSub (.var "feeGrowthGlobal1X128") (.var "feeGrowthBelow1X128"))
              (.var "feeGrowthAbove1X128") ] ] }

def tickUpdateFunction : FunctionDecl :=
  { name := "tickUpdate"
    params :=
      [ { name := "tick", ty := int24 }, { name := "tickCurrent", ty := int24 },
        { name := "liquidityDelta", ty := int128 },
        { name := "feeGrowthGlobal0X128", ty := uint256 },
        { name := "feeGrowthGlobal1X128", ty := uint256 },
        { name := "secondsPerLiquidityCumulativeX128", ty := uint160 },
        { name := "tickCumulative", ty := int56 }, { name := "time", ty := uint32 },
        { name := "upper", ty := boolTy }, { name := "maxLiquidity", ty := uint128 } ]
    returnType := [boolTy]
    body :=
      [ .letStorage "info" (ticksRef (.var "tick")),
        .letDecl "liquidityGrossBefore" (some uint128)
          (.field (.var "info") "liquidityGross"),
        .internalCall "liquidityAddDelta"
          [.var "liquidityGrossBefore", .var "liquidityDelta"] "liquidityGrossAfter",
        .require (leE (.var "liquidityGrossAfter") (.var "maxLiquidity")),
        .letDecl "flipped" (some boolTy)
          (neE (eqE (.var "liquidityGrossAfter") (.intLit 0))
            (eqE (.var "liquidityGrossBefore") (.intLit 0))),
        Stmt.ite (eqE (.var "liquidityGrossBefore") (.intLit 0))
          [ Stmt.ite (leE (.var "tick") (.var "tickCurrent"))
              [ .assign .storage { base := "info", steps := [.field "feeGrowthOutside0X128"] }
                  (.var "feeGrowthGlobal0X128"),
                .assign .storage { base := "info", steps := [.field "feeGrowthOutside1X128"] }
                  (.var "feeGrowthGlobal1X128"),
                .assign .storage { base := "info", steps := [.field "secondsPerLiquidityOutsideX128"] }
                  (.var "secondsPerLiquidityCumulativeX128"),
                .assign .storage { base := "info", steps := [.field "tickCumulativeOutside"] }
                  (.var "tickCumulative"),
                .assign .storage { base := "info", steps := [.field "secondsOutside"] }
                  (.var "time") ]
              [],
            .assign .storage { base := "info", steps := [.field "initialized"] } (.boolLit true) ]
          [],
        .assign .storage { base := "info", steps := [.field "liquidityGross"] }
          (.var "liquidityGrossAfter"),
        .assign .storage { base := "info", steps := [.field "liquidityNet"] }
          (.inRange int128Int
            (.ite (.var "upper")
              (subE (.field (.var "info") "liquidityNet") (.var "liquidityDelta"))
              (addE (.field (.var "info") "liquidityNet") (.var "liquidityDelta")))),
        .return [.var "flipped"] ] }

def tickClearFunction : FunctionDecl :=
  { name := "tickClear"
    params := [{ name := "tick", ty := int24 }]
    returnType := []
    body := [ .delete (ticksRef (.var "tick")) ] }

def tickBitmapFlipFunction : FunctionDecl :=
  { name := "tickBitmapFlip"
    params := [{ name := "tick", ty := int24 }, { name := "tickSpacing", ty := int24 }]
    returnType := []
    body :=
      [ .require (eqE (modE (.var "tick") (.var "tickSpacing")) (.intLit 0)),
        .letDecl "compressed" (some int24) (divE (.var "tick") (.var "tickSpacing")),
        .letDecl "wordPos" (some int16) (divE (.var "compressed") (.intLit 256)),
        .letDecl "bitPos" (some uint8) (modE (.var "compressed") (.intLit 256)),
        .letDecl "mask" (some uint256) (shlE (.intLit 1) (.var "bitPos")),
        .assign .storage (tickBitmapRef (.var "wordPos"))
          (bitXorE (.storage (tickBitmapRef (.var "wordPos"))) (.var "mask")) ] }

def positionUpdateFunction : FunctionDecl :=
  { name := "positionUpdate"
    params :=
      [ { name := "positionKey", ty := bytes32 }, { name := "liquidityDelta", ty := int128 },
        { name := "feeGrowthInside0X128", ty := uint256 },
        { name := "feeGrowthInside1X128", ty := uint256 } ]
    returnType := []
    body :=
      [ .letStorage "position" (positionsRef (.var "positionKey")),
        Stmt.ite (eqE (.var "liquidityDelta") (.intLit 0))
          [ .require (gtE (.field (.var "position") "liquidity") (.intLit 0)),
            .letDecl "liquidityNext" (some uint128)
              (.field (.var "position") "liquidity") ]
          [ .internalCall "liquidityAddDelta"
              [.field (.var "position") "liquidity", .var "liquidityDelta"]
              "liquidityNext" ],
        .letDecl "tokensOwed0" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside0X128")
                  (.field (.var "position") "feeGrowthInside0LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)),
        .letDecl "tokensOwed1" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside1X128")
                  (.field (.var "position") "feeGrowthInside1LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)),
        Stmt.ite (neE (.var "liquidityDelta") (.intLit 0))
          [ .assign .storage { base := "position", steps := [.field "liquidity"] }
              (.var "liquidityNext") ]
          [],
        .assign .storage { base := "position", steps := [.field "feeGrowthInside0LastX128"] }
          (.var "feeGrowthInside0X128"),
        .assign .storage { base := "position", steps := [.field "feeGrowthInside1LastX128"] }
          (.var "feeGrowthInside1X128"),
        Stmt.ite (orE (gtE (.var "tokensOwed0") (.intLit 0))
            (gtE (.var "tokensOwed1") (.intLit 0)))
          [ .assign .storage { base := "position", steps := [.field "tokensOwed0"] }
              (addE (.field (.var "position") "tokensOwed0") (.var "tokensOwed0")),
            .assign .storage { base := "position", steps := [.field "tokensOwed1"] }
              (addE (.field (.var "position") "tokensOwed1") (.var "tokensOwed1")) ]
          [] ] }

def getAmount0DeltaUnsignedFunction : FunctionDecl :=
  { name := "getAmount0DeltaUnsigned"
    params :=
      [ { name := "sqrtRatioAX96", ty := uint160 },
        { name := "sqrtRatioBX96", ty := uint160 },
        { name := "liquidity", ty := uint128 }, { name := "roundUp", ty := boolTy } ]
    returnType := [uint256]
    body :=
      [ .letDecl "sqrtRatioA" (some uint160) (.var "sqrtRatioAX96"),
        .letDecl "sqrtRatioB" (some uint160) (.var "sqrtRatioBX96"),
        Stmt.ite (gtE (.var "sqrtRatioA") (.var "sqrtRatioB"))
          [ .assign .localVar (varRef "sqrtRatioA") (.var "sqrtRatioBX96"),
            .assign .localVar (varRef "sqrtRatioB") (.var "sqrtRatioAX96") ]
          [],
        .letDecl "numerator1" (some uint256) (shlE (.var "liquidity") shift96),
        .letDecl "numerator2" (some uint256)
          (subE (.var "sqrtRatioB") (.var "sqrtRatioA")),
        .require (gtE (.var "sqrtRatioA") (.intLit 0)),
        Stmt.ite (.var "roundUp")
          (mulDivRoundingUpLet "product" (.var "numerator1") (.var "numerator2")
              (.var "sqrtRatioB") ++
            divRoundingUpLet "amount0" (.var "product") (.var "sqrtRatioA") ++
            [ .return [.var "amount0"] ])
          (mulDivLet "product" (.var "numerator1") (.var "numerator2")
              (.var "sqrtRatioB") ++
            [ .return [divE (.var "product") (.var "sqrtRatioA")] ]) ] }

def getAmount1DeltaUnsignedFunction : FunctionDecl :=
  { name := "getAmount1DeltaUnsigned"
    params :=
      [ { name := "sqrtRatioAX96", ty := uint160 },
        { name := "sqrtRatioBX96", ty := uint160 },
        { name := "liquidity", ty := uint128 }, { name := "roundUp", ty := boolTy } ]
    returnType := [uint256]
    body :=
      [ .letDecl "sqrtRatioA" (some uint160) (.var "sqrtRatioAX96"),
        .letDecl "sqrtRatioB" (some uint160) (.var "sqrtRatioBX96"),
        Stmt.ite (gtE (.var "sqrtRatioA") (.var "sqrtRatioB"))
          [ .assign .localVar (varRef "sqrtRatioA") (.var "sqrtRatioBX96"),
            .assign .localVar (varRef "sqrtRatioB") (.var "sqrtRatioAX96") ]
          [],
        Stmt.ite (.var "roundUp")
          (mulDivRoundingUpLet "amount1" (.var "liquidity")
              (subE (.var "sqrtRatioB") (.var "sqrtRatioA")) (.intLit (2 ^ 96)) ++
            [ .return [.var "amount1"] ])
          (mulDivLet "amount1" (.var "liquidity")
              (subE (.var "sqrtRatioB") (.var "sqrtRatioA")) (.intLit (2 ^ 96)) ++
            [ .return [.var "amount1"] ]) ] }

def getAmount0DeltaSignedFunction : FunctionDecl :=
  { name := "getAmount0DeltaSigned"
    params :=
      [ { name := "sqrtRatioAX96", ty := uint160 },
        { name := "sqrtRatioBX96", ty := uint160 }, { name := "liquidity", ty := int128 } ]
    returnType := [int256]
    body :=
      [ Stmt.ite (ltE (.var "liquidity") (.intLit 0))
          [ .internalCall "getAmount0DeltaUnsigned"
              [ .var "sqrtRatioAX96", .var "sqrtRatioBX96",
                uint128Wrap (subE (.intLit 0) (.var "liquidity")), .boolLit false ]
              "amount0Unsigned",
            .return [subE (.intLit 0) (.var "amount0Unsigned")] ]
          [ .internalCall "getAmount0DeltaUnsigned"
              [ .var "sqrtRatioAX96", .var "sqrtRatioBX96", uint128Wrap (.var "liquidity"),
                .boolLit true ]
              "amount0Unsigned",
            .return [.var "amount0Unsigned"] ] ] }

def getAmount1DeltaSignedFunction : FunctionDecl :=
  { name := "getAmount1DeltaSigned"
    params :=
      [ { name := "sqrtRatioAX96", ty := uint160 },
        { name := "sqrtRatioBX96", ty := uint160 }, { name := "liquidity", ty := int128 } ]
    returnType := [int256]
    body :=
      [ Stmt.ite (ltE (.var "liquidity") (.intLit 0))
          [ .internalCall "getAmount1DeltaUnsigned"
              [ .var "sqrtRatioAX96", .var "sqrtRatioBX96",
                uint128Wrap (subE (.intLit 0) (.var "liquidity")), .boolLit false ]
              "amount1Unsigned",
            .return [subE (.intLit 0) (.var "amount1Unsigned")] ]
          [ .internalCall "getAmount1DeltaUnsigned"
              [ .var "sqrtRatioAX96", .var "sqrtRatioBX96", uint128Wrap (.var "liquidity"),
                .boolLit true ]
              "amount1Unsigned",
            .return [.var "amount1Unsigned"] ] ] }

def modifyPositionFunction (v : PoolImmutables) : FunctionDecl :=
  { name := "modifyPosition"
    params :=
      [ { name := "owner", ty := addr }, { name := "tickLower", ty := int24 },
        { name := "tickUpper", ty := int24 }, { name := "liquidityDelta", ty := int128 } ]
    returnType := [bytes32, int256, int256]
    body := noDelegateCall v ++
      checkTicksBody (.var "tickLower") (.var "tickUpper") ++
      [ .letDecl "_slot0sqrtPriceX96" (some uint160) (.storage (slot0F "sqrtPriceX96")),
        .letDecl "_slot0tick" (some int24) (.storage (slot0F "tick")),
        .letDecl "_slot0observationIndex" (some uint16) (.storage (slot0F "observationIndex")),
        .letDecl "_slot0observationCardinality" (some uint16)
          (.storage (slot0F "observationCardinality")),
        .letDecl "_slot0observationCardinalityNext" (some uint16)
          (.storage (slot0F "observationCardinalityNext")),
        .letDecl "_positionKey" (some bytes32)
          (positionKey (.var "owner") (.var "tickLower") (.var "tickUpper")),
        .letDecl "_feeGrowthGlobal0X128" (some uint256) (.storage feeGrowthGlobal0X128Ref),
        .letDecl "_feeGrowthGlobal1X128" (some uint256) (.storage feeGrowthGlobal1X128Ref),
        .letDecl "flippedLower" (some boolTy) (.boolLit false),
        .letDecl "flippedUpper" (some boolTy) (.boolLit false),
        Stmt.ite (neE (.var "liquidityDelta") (.intLit 0))
          [ .letDecl "time" (some uint32) blockTimestamp32,
            .internalCall "observeSingle"
              [ .var "time", .intLit 0, .storage (slot0F "tick"),
                .storage (slot0F "observationIndex"), .storage liquidityRef,
                .storage (slot0F "observationCardinality") ]
              "observedForUpdate",
            .internalCall "tickUpdate"
              [ .var "tickLower", .var "_slot0tick", .var "liquidityDelta",
                .var "_feeGrowthGlobal0X128", .var "_feeGrowthGlobal1X128",
                tuple1 (.var "observedForUpdate"), tuple0 (.var "observedForUpdate"),
                .var "time", .boolLit false, .intLit v.maxLiquidityPerTick ]
              "flippedLowerCall",
            .assign .localVar (varRef "flippedLower") (.var "flippedLowerCall"),
            .internalCall "tickUpdate"
              [ .var "tickUpper", .var "_slot0tick", .var "liquidityDelta",
                .var "_feeGrowthGlobal0X128", .var "_feeGrowthGlobal1X128",
                tuple1 (.var "observedForUpdate"), tuple0 (.var "observedForUpdate"),
                .var "time", .boolLit true, .intLit v.maxLiquidityPerTick ]
              "flippedUpperCall",
            .assign .localVar (varRef "flippedUpper") (.var "flippedUpperCall"),
            Stmt.ite (.var "flippedLower")
              [ .internalCall "tickBitmapFlip" [.var "tickLower", .intLit v.tickSpacing]
                  "_flipLower" ]
              [],
            Stmt.ite (.var "flippedUpper")
              [ .internalCall "tickBitmapFlip" [.var "tickUpper", .intLit v.tickSpacing]
                  "_flipUpper" ]
              [] ]
          [],
        .internalCall "tickGetFeeGrowthInside"
          [ .var "tickLower", .var "tickUpper", .var "_slot0tick",
            .var "_feeGrowthGlobal0X128", .var "_feeGrowthGlobal1X128" ]
          "feeGrowthInside",
        .internalCall "positionUpdate"
          [ .var "_positionKey", .var "liquidityDelta", tuple0 (.var "feeGrowthInside"),
            tuple1 (.var "feeGrowthInside") ]
          "_positionUpdated",
        Stmt.ite (ltE (.var "liquidityDelta") (.intLit 0))
          [ Stmt.ite (.var "flippedLower")
              [ .internalCall "tickClear" [.var "tickLower"] "_clearLower" ]
              [],
            Stmt.ite (.var "flippedUpper")
              [ .internalCall "tickClear" [.var "tickUpper"] "_clearUpper" ]
              [] ]
          [],
        .letDecl "amount0" (some int256) (.intLit 0),
        .letDecl "amount1" (some int256) (.intLit 0),
        Stmt.ite (neE (.var "liquidityDelta") (.intLit 0))
          [ Stmt.ite (ltE (.var "_slot0tick") (.var "tickLower"))
              [ .internalCall "getSqrtRatioAtTick" [.var "tickLower"] "sqrtRatioLowerBelow",
                .internalCall "getSqrtRatioAtTick" [.var "tickUpper"] "sqrtRatioUpperBelow",
                .internalCall "getAmount0DeltaSigned"
                  [ .var "sqrtRatioLowerBelow", .var "sqrtRatioUpperBelow",
                    .var "liquidityDelta" ]
                  "amount0Below",
                .assign .localVar (varRef "amount0") (.var "amount0Below") ]
              [ Stmt.ite (ltE (.var "_slot0tick") (.var "tickUpper"))
                  [ .letDecl "liquidityBefore" (some uint128) (.storage liquidityRef),
                    .internalCall "oracleWrite"
                      [ .var "_slot0observationIndex", blockTimestamp32, .var "_slot0tick",
                        .var "liquidityBefore", .var "_slot0observationCardinality",
                        .var "_slot0observationCardinalityNext" ]
                      "oracleUpdated",
                    .assign .storage (slot0F "observationIndex") (tuple0 (.var "oracleUpdated")),
                    .assign .storage (slot0F "observationCardinality")
                      (tuple1 (.var "oracleUpdated")),
                    .internalCall "getSqrtRatioAtTick" [.var "tickUpper"]
                      "sqrtRatioUpperInside",
                    .internalCall "getAmount0DeltaSigned"
                      [ .var "_slot0sqrtPriceX96", .var "sqrtRatioUpperInside",
                        .var "liquidityDelta" ]
                      "amount0Inside",
                    .assign .localVar (varRef "amount0") (.var "amount0Inside"),
                    .internalCall "getSqrtRatioAtTick" [.var "tickLower"]
                      "sqrtRatioLowerInside",
                    .internalCall "getAmount1DeltaSigned"
                      [ .var "sqrtRatioLowerInside", .var "_slot0sqrtPriceX96",
                        .var "liquidityDelta" ]
                      "amount1Inside",
                    .assign .localVar (varRef "amount1") (.var "amount1Inside"),
                    .internalCall "liquidityAddDelta"
                      [ .var "liquidityBefore", .var "liquidityDelta" ]
                      "liquidityAfter",
                    .assign .storage liquidityRef (.var "liquidityAfter") ]
                  [ .internalCall "getSqrtRatioAtTick" [.var "tickLower"]
                      "sqrtRatioLowerAbove",
                    .internalCall "getSqrtRatioAtTick" [.var "tickUpper"]
                      "sqrtRatioUpperAbove",
                    .internalCall "getAmount1DeltaSigned"
                      [ .var "sqrtRatioLowerAbove", .var "sqrtRatioUpperAbove",
                        .var "liquidityDelta" ]
                      "amount1Above",
                    .assign .localVar (varRef "amount1") (.var "amount1Above") ] ] ]
          [],
        .return [.var "_positionKey", .var "amount0", .var "amount1"] ] }

def mostSignificantBitStep (threshold : Int) (shift : Int) : List Stmt :=
  [ Stmt.ite (geE (.var "x") (.intLit threshold))
      [ .assign .localVar (varRef "x") (shrE (.var "x") (.intLit shift)),
        .assign .localVar (varRef "r") (addE (.var "r") (.intLit shift)) ]
      [] ]

def mostSignificantBitFunction : FunctionDecl :=
  { name := "mostSignificantBit"
    params := [{ name := "x", ty := uint256 }]
    returnType := [uint8]
    body :=
      [ .require (gtE (.var "x") (.intLit 0)),
        .letDecl "r" (some uint8) (.intLit 0) ] ++
      mostSignificantBitStep (2 ^ 128) 128 ++
      mostSignificantBitStep (2 ^ 64) 64 ++
      mostSignificantBitStep (2 ^ 32) 32 ++
      mostSignificantBitStep (2 ^ 16) 16 ++
      mostSignificantBitStep (2 ^ 8) 8 ++
      mostSignificantBitStep (2 ^ 4) 4 ++
      mostSignificantBitStep (2 ^ 2) 2 ++
      [ Stmt.ite (geE (.var "x") (.intLit 2))
          [ .assign .localVar (varRef "r") (addE (.var "r") (.intLit 1)) ]
          [],
        .return [.var "r"] ] }

def leastSignificantBitStep (mask shift : Int) : List Stmt :=
  [ Stmt.ite (gtE (bitAndE (.var "x") (.intLit mask)) (.intLit 0))
      [ .assign .localVar (varRef "r") (subE (.var "r") (.intLit shift)) ]
      [ .assign .localVar (varRef "x") (shrE (.var "x") (.intLit shift)) ] ]

def leastSignificantBitFunction : FunctionDecl :=
  { name := "leastSignificantBit"
    params := [{ name := "x", ty := uint256 }]
    returnType := [uint8]
    body :=
      [ .require (gtE (.var "x") (.intLit 0)),
        .letDecl "r" (some uint8) (.intLit 255) ] ++
      leastSignificantBitStep (2 ^ 128 - 1) 128 ++
      leastSignificantBitStep (2 ^ 64 - 1) 64 ++
      leastSignificantBitStep (2 ^ 32 - 1) 32 ++
      leastSignificantBitStep (2 ^ 16 - 1) 16 ++
      leastSignificantBitStep (2 ^ 8 - 1) 8 ++
      leastSignificantBitStep 0xf 4 ++
      leastSignificantBitStep 0x3 2 ++
      [ Stmt.ite (gtE (bitAndE (.var "x") (.intLit 0x1)) (.intLit 0))
          [ .assign .localVar (varRef "r") (subE (.var "r") (.intLit 1)) ]
          [],
        .return [.var "r"] ] }

def tickBitmapNextInitializedTickWithinOneWordFunction : FunctionDecl :=
  { name := "tickBitmapNextInitializedTickWithinOneWord"
    params :=
      [ { name := "tick", ty := int24 }, { name := "tickSpacing", ty := int24 },
        { name := "lte", ty := boolTy } ]
    returnType := [int24, boolTy]
    body :=
      [ .letDecl "compressed" (some int24) (divE (.var "tick") (.var "tickSpacing")),
        Stmt.ite (.var "lte")
          [ .letDecl "wordPos" (some int16) (divE (.var "compressed") (.intLit 256)),
            .letDecl "bitPos" (some uint8) (modE (.var "compressed") (.intLit 256)),
            .letDecl "oneAtBit" (some uint256) (shlE (.intLit 1) (.var "bitPos")),
            .letDecl "mask" (some uint256)
              (addE (subE (.var "oneAtBit") (.intLit 1)) (.var "oneAtBit")),
            .letDecl "masked" (some uint256)
              (bitAndE (.storage (tickBitmapRef (.var "wordPos"))) (.var "mask")),
            .letDecl "initialized" (some boolTy) (neE (.var "masked") (.intLit 0)),
            Stmt.ite (.var "initialized")
              [ .internalCall "mostSignificantBit" [.var "masked"] "msb",
                .return
                  [ .inRange int24Int
                      (mulE (subE (.var "compressed") (subE (.var "bitPos") (.var "msb")))
                        (.var "tickSpacing")),
                    .var "initialized" ] ]
              [ .return
                  [ .inRange int24Int
                      (mulE (subE (.var "compressed") (.var "bitPos")) (.var "tickSpacing")),
                    .var "initialized" ] ] ]
          [ .letDecl "compressedPlusOne" (some int24) (addE (.var "compressed") (.intLit 1)),
            .letDecl "wordPos" (some int16) (divE (.var "compressedPlusOne") (.intLit 256)),
            .letDecl "bitPos" (some uint8) (modE (.var "compressedPlusOne") (.intLit 256)),
            .letDecl "mask" (some uint256)
              (.unary .bitNot (subE (shlE (.intLit 1) (.var "bitPos")) (.intLit 1))),
            .letDecl "masked" (some uint256)
              (bitAndE (.storage (tickBitmapRef (.var "wordPos"))) (.var "mask")),
            .letDecl "initialized" (some boolTy) (neE (.var "masked") (.intLit 0)),
            Stmt.ite (.var "initialized")
              [ .internalCall "leastSignificantBit" [.var "masked"] "lsb",
                .return
                  [ .inRange int24Int
                      (mulE
                        (addE (.var "compressedPlusOne") (subE (.var "lsb") (.var "bitPos")))
                        (.var "tickSpacing")),
                    .var "initialized" ] ]
              [ .return
                  [ .inRange int24Int
                      (mulE
                        (addE (.var "compressedPlusOne") (subE (.intLit 255) (.var "bitPos")))
                        (.var "tickSpacing")),
                    .var "initialized" ] ] ] ] }

def tickCrossFunction : FunctionDecl :=
  { name := "tickCross"
    params :=
      [ { name := "tick", ty := int24 }, { name := "feeGrowthGlobal0X128", ty := uint256 },
        { name := "feeGrowthGlobal1X128", ty := uint256 },
        { name := "secondsPerLiquidityCumulativeX128", ty := uint160 },
        { name := "tickCumulative", ty := int56 }, { name := "time", ty := uint32 } ]
    returnType := [int128]
    body :=
      [ .letStorage "info" (ticksRef (.var "tick")),
        .assign .storage { base := "info", steps := [.field "feeGrowthOutside0X128"] }
          (wordSub (.var "feeGrowthGlobal0X128")
            (.field (.var "info") "feeGrowthOutside0X128")),
        .assign .storage { base := "info", steps := [.field "feeGrowthOutside1X128"] }
          (wordSub (.var "feeGrowthGlobal1X128")
            (.field (.var "info") "feeGrowthOutside1X128")),
        .assign .storage { base := "info", steps := [.field "secondsPerLiquidityOutsideX128"] }
          (uint160Wrap
            (subE (.var "secondsPerLiquidityCumulativeX128")
              (.field (.var "info") "secondsPerLiquidityOutsideX128"))),
        .assign .storage { base := "info", steps := [.field "tickCumulativeOutside"] }
          (int56Wrap
            (subE (.var "tickCumulative") (.field (.var "info") "tickCumulativeOutside"))),
        .assign .storage { base := "info", steps := [.field "secondsOutside"] }
          (uint32Wrap (subE (.var "time") (.field (.var "info") "secondsOutside"))),
        .return [.field (.var "info") "liquidityNet"] ] }

def getNextSqrtPriceFromAmount0RoundingUpFunction : FunctionDecl :=
  { name := "getNextSqrtPriceFromAmount0RoundingUp"
    params :=
      [ { name := "sqrtPX96", ty := uint160 }, { name := "liquidity", ty := uint128 },
        { name := "amount", ty := uint256 }, { name := "add", ty := boolTy } ]
    returnType := [uint160]
    body :=
      [ Stmt.ite (eqE (.var "amount") (.intLit 0))
          [ .return [.var "sqrtPX96"] ]
          [],
        .letDecl "numerator1" (some uint256) (shlE (.var "liquidity") shift96),
        Stmt.ite (.var "add")
          ([ .letDecl "product" (some uint256) (wordMul (.var "amount") (.var "sqrtPX96")),
             Stmt.ite (eqE (divE (.var "product") (.var "amount")) (.var "sqrtPX96"))
              [ .letDecl "denominator" (some uint256)
                  (wordAdd (.var "numerator1") (.var "product")),
                Stmt.ite (geE (.var "denominator") (.var "numerator1"))
                  (mulDivRoundingUpLet "price" (.var "numerator1") (.var "sqrtPX96")
                      (.var "denominator") ++
                    [ .return [uint160Wrap (.var "price")] ])
                  [] ]
              [],
             .letDecl "denominator2Base" (some uint256)
              (divE (.var "numerator1") (.var "sqrtPX96")),
             .letDecl "denominator2" (some uint256)
              (wordAdd (.var "denominator2Base") (.var "amount")),
             .require (geE (.var "denominator2") (.var "denominator2Base")) ] ++
            divRoundingUpLet "price" (.var "numerator1") (.var "denominator2") ++
            [ .return [uint160Wrap (.var "price")] ])
          ([ .letDecl "product" (some uint256) (wordMul (.var "amount") (.var "sqrtPX96")),
             .require
              (andE (eqE (divE (.var "product") (.var "amount")) (.var "sqrtPX96"))
                (gtE (.var "numerator1") (.var "product"))),
             .letDecl "denominator" (some uint256)
              (subE (.var "numerator1") (.var "product")) ] ++
            mulDivRoundingUpLet "price" (.var "numerator1") (.var "sqrtPX96")
              (.var "denominator") ++
            [ .return [.inRange uint160Int (.var "price")] ]) ] }

def getNextSqrtPriceFromAmount1RoundingDownFunction : FunctionDecl :=
  { name := "getNextSqrtPriceFromAmount1RoundingDown"
    params :=
      [ { name := "sqrtPX96", ty := uint160 }, { name := "liquidity", ty := uint128 },
        { name := "amount", ty := uint256 }, { name := "add", ty := boolTy } ]
    returnType := [uint160]
    body :=
      [ Stmt.ite (.var "add")
          [ Stmt.ite (leE (.var "amount") uint160MaxExpr)
              [ .letDecl "quotient" (some uint256)
                  (divE (shlE (.var "amount") shift96) (.var "liquidity")) ]
              (mulDivLet "quotient" (.var "amount") (.intLit (2 ^ 96)) (.var "liquidity")),
            .letDecl "next" (some uint256) (wordAdd (.var "sqrtPX96") (.var "quotient")),
            .require (geE (.var "next") (.var "sqrtPX96")),
            .return [.inRange uint160Int (.var "next")] ]
          ([ Stmt.ite (leE (.var "amount") uint160MaxExpr)
              (divRoundingUpLet "quotient" (shlE (.var "amount") shift96) (.var "liquidity"))
              (mulDivRoundingUpLet "quotient" (.var "amount") (.intLit (2 ^ 96))
                (.var "liquidity")),
             .require (gtE (.var "sqrtPX96") (.var "quotient")),
             .return [subE (.var "sqrtPX96") (.var "quotient")] ]) ] }

def getNextSqrtPriceFromInputFunction : FunctionDecl :=
  { name := "getNextSqrtPriceFromInput"
    params :=
      [ { name := "sqrtPX96", ty := uint160 }, { name := "liquidity", ty := uint128 },
        { name := "amountIn", ty := uint256 }, { name := "zeroForOne", ty := boolTy } ]
    returnType := [uint160]
    body :=
      [ .require (gtE (.var "sqrtPX96") (.intLit 0)),
        .require (gtE (.var "liquidity") (.intLit 0)),
        Stmt.ite (.var "zeroForOne")
          [ .internalCall "getNextSqrtPriceFromAmount0RoundingUp"
              [.var "sqrtPX96", .var "liquidity", .var "amountIn", .boolLit true]
              "sqrtQX96",
            .return [.var "sqrtQX96"] ]
          [ .internalCall "getNextSqrtPriceFromAmount1RoundingDown"
              [.var "sqrtPX96", .var "liquidity", .var "amountIn", .boolLit true]
              "sqrtQX96",
            .return [.var "sqrtQX96"] ] ] }

def getNextSqrtPriceFromOutputFunction : FunctionDecl :=
  { name := "getNextSqrtPriceFromOutput"
    params :=
      [ { name := "sqrtPX96", ty := uint160 }, { name := "liquidity", ty := uint128 },
        { name := "amountOut", ty := uint256 }, { name := "zeroForOne", ty := boolTy } ]
    returnType := [uint160]
    body :=
      [ .require (gtE (.var "sqrtPX96") (.intLit 0)),
        .require (gtE (.var "liquidity") (.intLit 0)),
        Stmt.ite (.var "zeroForOne")
          [ .internalCall "getNextSqrtPriceFromAmount1RoundingDown"
              [.var "sqrtPX96", .var "liquidity", .var "amountOut", .boolLit false]
              "sqrtQX96",
            .return [.var "sqrtQX96"] ]
          [ .internalCall "getNextSqrtPriceFromAmount0RoundingUp"
              [.var "sqrtPX96", .var "liquidity", .var "amountOut", .boolLit false]
              "sqrtQX96",
            .return [.var "sqrtQX96"] ] ] }

def computeSwapStepFunction : FunctionDecl :=
  { name := "computeSwapStep"
    params :=
      [ { name := "sqrtRatioCurrentX96", ty := uint160 },
        { name := "sqrtRatioTargetX96", ty := uint160 },
        { name := "liquidity", ty := uint128 }, { name := "amountRemaining", ty := int256 },
        { name := "feePips", ty := uint24 } ]
    returnType := [uint160, uint256, uint256, uint256]
    body :=
      [ .letDecl "zeroForOne" (some boolTy)
          (geE (.var "sqrtRatioCurrentX96") (.var "sqrtRatioTargetX96")),
        .letDecl "exactIn" (some boolTy) (geE (.var "amountRemaining") (.intLit 0)),
        .letDecl "sqrtRatioNextX96" (some uint160) (.intLit 0),
        .letDecl "amountIn" (some uint256) (.intLit 0),
        .letDecl "amountOut" (some uint256) (.intLit 0),
        .letDecl "feeAmount" (some uint256) (.intLit 0),
        Stmt.ite (.var "exactIn")
          (mulDivLet "amountRemainingLessFee" (uint256Wrap (.var "amountRemaining"))
              (subE feeDenominator (.var "feePips")) feeDenominator ++
            [ Stmt.ite (.var "zeroForOne")
                [ .internalCall "getAmount0DeltaUnsigned"
                    [ .var "sqrtRatioTargetX96", .var "sqrtRatioCurrentX96",
                      .var "liquidity", .boolLit true ]
                    "amountInToTarget" ]
                [ .internalCall "getAmount1DeltaUnsigned"
                    [ .var "sqrtRatioCurrentX96", .var "sqrtRatioTargetX96",
                      .var "liquidity", .boolLit true ]
                    "amountInToTarget" ],
              .assign .localVar (varRef "amountIn") (.var "amountInToTarget"),
              Stmt.ite (geE (.var "amountRemainingLessFee") (.var "amountIn"))
                [ .assign .localVar (varRef "sqrtRatioNextX96")
                    (.var "sqrtRatioTargetX96") ]
                [ .internalCall "getNextSqrtPriceFromInput"
                    [ .var "sqrtRatioCurrentX96", .var "liquidity",
                      .var "amountRemainingLessFee", .var "zeroForOne" ]
                    "nextSqrtInput",
                  .assign .localVar (varRef "sqrtRatioNextX96") (.var "nextSqrtInput") ] ])
          [ Stmt.ite (.var "zeroForOne")
              [ .internalCall "getAmount1DeltaUnsigned"
                  [ .var "sqrtRatioTargetX96", .var "sqrtRatioCurrentX96", .var "liquidity",
                    .boolLit false ]
                  "amountOutToTarget" ]
              [ .internalCall "getAmount0DeltaUnsigned"
                  [ .var "sqrtRatioCurrentX96", .var "sqrtRatioTargetX96", .var "liquidity",
                    .boolLit false ]
                  "amountOutToTarget" ],
            .assign .localVar (varRef "amountOut") (.var "amountOutToTarget"),
            Stmt.ite (geE (uint256Wrap (subE (.intLit 0) (.var "amountRemaining")))
                (.var "amountOut"))
              [ .assign .localVar (varRef "sqrtRatioNextX96") (.var "sqrtRatioTargetX96") ]
              [ .internalCall "getNextSqrtPriceFromOutput"
                  [ .var "sqrtRatioCurrentX96", .var "liquidity",
                    uint256Wrap (subE (.intLit 0) (.var "amountRemaining")), .var "zeroForOne" ]
                  "nextSqrtOutput",
                .assign .localVar (varRef "sqrtRatioNextX96") (.var "nextSqrtOutput") ] ],
        .letDecl "max" (some boolTy) (eqE (.var "sqrtRatioTargetX96") (.var "sqrtRatioNextX96")),
        Stmt.ite (.var "zeroForOne")
          [ Stmt.ite (notE (andE (.var "max") (.var "exactIn")))
              [ .internalCall "getAmount0DeltaUnsigned"
                  [ .var "sqrtRatioNextX96", .var "sqrtRatioCurrentX96", .var "liquidity",
                    .boolLit true ]
                  "amountInRecomputed",
                .assign .localVar (varRef "amountIn") (.var "amountInRecomputed") ]
              [],
            Stmt.ite (notE (andE (.var "max") (notE (.var "exactIn"))))
              [ .internalCall "getAmount1DeltaUnsigned"
                  [ .var "sqrtRatioNextX96", .var "sqrtRatioCurrentX96", .var "liquidity",
                    .boolLit false ]
                  "amountOutRecomputed",
                .assign .localVar (varRef "amountOut") (.var "amountOutRecomputed") ]
              [] ]
          [ Stmt.ite (notE (andE (.var "max") (.var "exactIn")))
              [ .internalCall "getAmount1DeltaUnsigned"
                  [ .var "sqrtRatioCurrentX96", .var "sqrtRatioNextX96", .var "liquidity",
                    .boolLit true ]
                  "amountInRecomputed",
                .assign .localVar (varRef "amountIn") (.var "amountInRecomputed") ]
              [],
            Stmt.ite (notE (andE (.var "max") (notE (.var "exactIn"))))
              [ .internalCall "getAmount0DeltaUnsigned"
                  [ .var "sqrtRatioCurrentX96", .var "sqrtRatioNextX96", .var "liquidity",
                    .boolLit false ]
                  "amountOutRecomputed",
                .assign .localVar (varRef "amountOut") (.var "amountOutRecomputed") ]
              [] ],
        Stmt.ite (andE (notE (.var "exactIn"))
            (gtE (.var "amountOut") (uint256Wrap (subE (.intLit 0) (.var "amountRemaining")))))
          [ .assign .localVar (varRef "amountOut")
              (uint256Wrap (subE (.intLit 0) (.var "amountRemaining"))) ]
          [],
        Stmt.ite (andE (.var "exactIn")
            (neE (.var "sqrtRatioNextX96") (.var "sqrtRatioTargetX96")))
          [ .assign .localVar (varRef "feeAmount")
              (subE (uint256Wrap (.var "amountRemaining")) (.var "amountIn")) ]
          (mulDivRoundingUpLet "feeAmountComputed" (.var "amountIn") (.var "feePips")
              (subE feeDenominator (.var "feePips")) ++
            [ .assign .localVar (varRef "feeAmount") (.var "feeAmountComputed") ]),
        .return [.var "sqrtRatioNextX96", .var "amountIn", .var "amountOut", .var "feeAmount"] ] }

def functions (v : PoolImmutables) : List FunctionDecl :=
  [ getSqrtRatioAtTickFunction,
    getTickAtSqrtRatioFunction,
    oracleLteFunction,
    oracleTransformFunction,
    getSurroundingObservationsFunction,
    observeSingleFunction,
    observeBodyFunction,
    liquidityAddDeltaFunction,
    oracleWriteFunction,
    tickGetFeeGrowthInsideFunction,
    tickUpdateFunction,
    tickClearFunction,
    tickBitmapFlipFunction,
    positionUpdateFunction,
    getAmount0DeltaUnsignedFunction,
    getAmount1DeltaUnsignedFunction,
    getAmount0DeltaSignedFunction,
    getAmount1DeltaSignedFunction,
    modifyPositionFunction v,
    mostSignificantBitFunction,
    leastSignificantBitFunction,
    tickBitmapNextInitializedTickWithinOneWordFunction,
    tickCrossFunction,
    getNextSqrtPriceFromAmount0RoundingUpFunction,
    getNextSqrtPriceFromAmount1RoundingDownFunction,
    getNextSqrtPriceFromInputFunction,
    getNextSqrtPriceFromOutputFunction,
    computeSwapStepFunction ]

/-! ## Constructor -/

-- The pool constructor: `IUniswapV3PoolDeployer(msg.sender).parameters()` returns
-- `(factory, token0, token1, fee, tickSpacing)`; `original := address(this)`; and
-- `maxLiquidityPerTick := Tick.tickSpacingToMaxLiquidityPerTick(tickSpacing)`.  That formula's only
-- signed division `(-887272 / ts)` (ts > 0) equals `-(887272 / ts)`, so the whole thing reduces to
-- `(2^128-1) / (2*(887272 / ts) + 1)` over positive operands — where Solm's `/` (Euclidean) already
-- matches EVM truncating division.  Each immutable is bound to `imm_<name>` for `runtimeCodeOf`.
def constructorDecl : ConstructorDecl :=
  { params := []
    body := nonpayable ++
      [ .externalCall (.env .caller) "parameters" (.intLit 0) [] "r" (perm := false),
        .letDecl "imm_factory" none (.tupleGet (.var "r") 0),
        .letDecl "imm_token0" none (.tupleGet (.var "r") 1),
        .letDecl "imm_token1" none (.tupleGet (.var "r") 2),
        .letDecl "imm_fee" none (.tupleGet (.var "r") 3),
        .letDecl "imm_tickSpacing" none (.tupleGet (.var "r") 4),
        .letDecl "imm_original" none (.env .this),
        .letDecl "imm_maxLiquidityPerTick" none
          (.binary .div (.intLit (2 ^ 128 - 1))
            (.binary .add
              (.binary .mul (.intLit 2) (.binary .div (.intLit 887272) (.var "imm_tickSpacing")))
              (.intLit 1))) ] }

/-! ## Public ABI surface -/

def burnTransition : TransitionDecl :=
  { name := "burn"
    params :=
      [ { name := "tickLower", ty := int24 }, { name := "tickUpper", ty := int24 },
        { name := "amount", ty := uint128 } ]
    returnType := [uint256, uint256]
    body := nonpayable ++ lockPrefix ++
      [ .letDecl "liquidityDelta" (some int128)
          (subE (.intLit 0) (.inRange int128Int (.var "amount"))),
        .internalCall "modifyPosition"
          [.env .caller, .var "tickLower", .var "tickUpper", .var "liquidityDelta"]
          "modified",
        .letStorage "position" (positionsRef (tuple0 (.var "modified"))),
        .letDecl "amount0" (some uint256) (uint256Wrap (subE (.intLit 0) (tuple1 (.var "modified")))),
        .letDecl "amount1" (some uint256) (uint256Wrap (subE (.intLit 0) (tuple2 (.var "modified")))),
        Stmt.ite (orE (gtE (.var "amount0") (.intLit 0)) (gtE (.var "amount1") (.intLit 0)))
          [ .assign .storage { base := "position", steps := [.field "tokensOwed0"] }
              (addE (.field (.var "position") "tokensOwed0") (uint128Wrap (.var "amount0"))),
            .assign .storage { base := "position", steps := [.field "tokensOwed1"] }
              (addE (.field (.var "position") "tokensOwed1") (uint128Wrap (.var "amount1"))) ]
          [] ] ++
      lockSuffix ++
      [ .return [.var "amount0", .var "amount1"] ] }

def collectTransition (v : PoolImmutables) : TransitionDecl :=
  { name := "collect"
    params := [ { name := "recipient", ty := addr }, { name := "tickLower", ty := int24 }, { name := "tickUpper", ty := int24 }, { name := "amount0Requested", ty := uint128 }, { name := "amount1Requested", ty := uint128 } ]
    returnType := [uint128, uint128]
    body := nonpayable ++ lockPrefix ++
      [ .letDecl "positionKey" (some bytes32)
          (positionKey (.env .caller) (.var "tickLower") (.var "tickUpper")),
        .letDecl "amount0" (some uint128)
          (.ite (gtE (.var "amount0Requested")
              (.storage (positionsF (.var "positionKey") "tokensOwed0")))
            (.storage (positionsF (.var "positionKey") "tokensOwed0"))
            (.var "amount0Requested")),
        .letDecl "amount1" (some uint128)
          (.ite (gtE (.var "amount1Requested")
              (.storage (positionsF (.var "positionKey") "tokensOwed1")))
            (.storage (positionsF (.var "positionKey") "tokensOwed1"))
            (.var "amount1Requested")),
        Stmt.ite (gtE (.var "amount0") (.intLit 0))
          ([ .assign .storage (positionsF (.var "positionKey") "tokensOwed0")
              (subE (.storage (positionsF (.var "positionKey") "tokensOwed0")) (.var "amount0")) ] ++
            safeTransfer (addrLit v.token0) (.var "recipient") (.var "amount0") "collect0")
          [],
        Stmt.ite (gtE (.var "amount1") (.intLit 0))
          ([ .assign .storage (positionsF (.var "positionKey") "tokensOwed1")
              (subE (.storage (positionsF (.var "positionKey") "tokensOwed1")) (.var "amount1")) ] ++
            safeTransfer (addrLit v.token1) (.var "recipient") (.var "amount1") "collect1")
          [] ] ++
      lockSuffix ++
      [ .return [(.var "amount0"), (.var "amount1")] ] }

def collectprotocolTransition (v : PoolImmutables) : TransitionDecl :=
  { name := "collectProtocol"
    params := [ { name := "recipient", ty := addr }, { name := "amount0Requested", ty := uint128 }, { name := "amount1Requested", ty := uint128 } ]
    returnType := [uint128, uint128]
    body := nonpayable ++ lockPrefix ++ onlyFactoryOwner v ++
      [ .letDecl "amount0" (some uint128)
          (.ite (gtE (.var "amount0Requested") (.storage (protocolFeesF "token0")))
            (.storage (protocolFeesF "token0"))
            (.var "amount0Requested")),
        .letDecl "amount1" (some uint128)
          (.ite (gtE (.var "amount1Requested") (.storage (protocolFeesF "token1")))
            (.storage (protocolFeesF "token1"))
            (.var "amount1Requested")),
        Stmt.ite (gtE (.var "amount0") (.intLit 0))
          ([ Stmt.ite (eqE (.var "amount0") (.storage (protocolFeesF "token0")))
              [ .assign .localVar (varRef "amount0") (subE (.var "amount0") (.intLit 1)) ]
              [],
            .assign .storage (protocolFeesF "token0")
              (subE (.storage (protocolFeesF "token0")) (.var "amount0")) ] ++
            safeTransfer (addrLit v.token0) (.var "recipient") (.var "amount0") "collectProtocol0")
          [],
        Stmt.ite (gtE (.var "amount1") (.intLit 0))
          ([ Stmt.ite (eqE (.var "amount1") (.storage (protocolFeesF "token1")))
              [ .assign .localVar (varRef "amount1") (subE (.var "amount1") (.intLit 1)) ]
              [],
            .assign .storage (protocolFeesF "token1")
              (subE (.storage (protocolFeesF "token1")) (.var "amount1")) ] ++
            safeTransfer (addrLit v.token1) (.var "recipient") (.var "amount1") "collectProtocol1")
          [] ] ++
      lockSuffix ++
      [ .return [(.var "amount0"), (.var "amount1")] ] }

def factoryTransition (v : PoolImmutables) : TransitionDecl :=
  { name := "factory"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [addrLit v.factory] ] }

def feeTransition (v : PoolImmutables) : TransitionDecl :=
  { name := "fee"
    params := []
    returnType := [uint24]
    body := nonpayable ++ [ .return [.intLit v.fee] ] }

def feegrowthglobal0X128Transition : TransitionDecl :=
  { name := "feeGrowthGlobal0X128"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage feeGrowthGlobal0X128Ref] ] }

def feegrowthglobal1X128Transition : TransitionDecl :=
  { name := "feeGrowthGlobal1X128"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage feeGrowthGlobal1X128Ref] ] }

def flashTransition (v : PoolImmutables) : TransitionDecl :=
  { name := "flash"
    params := [ { name := "recipient", ty := addr }, { name := "amount0", ty := uint256 }, { name := "amount1", ty := uint256 }, { name := "data", ty := bytesTy } ]
    returnType := []
    body := nonpayable ++ lockPrefix ++ noDelegateCall v ++
      [ .letDecl "_liquidity" (some uint128) (.storage liquidityRef),
        .require (gtE (.var "_liquidity") (.intLit 0)) ] ++
      mulDivRoundingUpLet "fee0" (.var "amount0") (.intLit v.fee) feeDenominator ++
      mulDivRoundingUpLet "fee1" (.var "amount1") (.intLit v.fee) feeDenominator ++
      balanceOfInto (addrLit v.token0) "balance0Before" "flashBalance0Before" ++
      balanceOfInto (addrLit v.token1) "balance1Before" "flashBalance1Before" ++
      [ Stmt.ite (gtE (.var "amount0") (.intLit 0))
          (safeTransfer (addrLit v.token0) (.var "recipient") (.var "amount0") "flashTransfer0")
          [],
        Stmt.ite (gtE (.var "amount1") (.intLit 0))
          (safeTransfer (addrLit v.token1) (.var "recipient") (.var "amount1") "flashTransfer1")
          [],
        .externalCall (.env .caller) "uniswapV3FlashCallback" (.intLit 0)
          [.var "fee0", .var "fee1", .var "data"] "_flashCallback" ] ++
      balanceOfInto (addrLit v.token0) "balance0After" "flashBalance0After" ++
      balanceOfInto (addrLit v.token1) "balance1After" "flashBalance1After" ++
      checkedWordAddLe (.var "balance0Before") (.var "fee0") (.var "balance0After") ++
      checkedWordAddLe (.var "balance1Before") (.var "fee1") (.var "balance1After") ++
      [ .letDecl "paid0" (some uint256)
          (subE (.var "balance0After") (.var "balance0Before")),
        .letDecl "paid1" (some uint256)
          (subE (.var "balance1After") (.var "balance1Before")),
        Stmt.ite (gtE (.var "paid0") (.intLit 0))
          ([ .letDecl "feeProtocol0" (some uint8)
                (modE (.storage (slot0F "feeProtocol")) (.intLit 16)),
             .letDecl "fees0" (some uint256)
                (.ite (eqE (.var "feeProtocol0") (.intLit 0))
                  (.intLit 0)
                  (divE (.var "paid0") (.var "feeProtocol0"))),
             Stmt.ite (gtE (uint128Wrap (.var "fees0")) (.intLit 0))
                [ .assign .storage (protocolFeesF "token0")
                    (addE (.storage (protocolFeesF "token0")) (uint128Wrap (.var "fees0"))) ]
                [] ] ++
            mulDivLet "feeGrowth0Delta" (subE (.var "paid0") (.var "fees0"))
              fixedPoint128Q128 (.var "_liquidity") ++
            [ .assign .storage feeGrowthGlobal0X128Ref
                (addE (.storage feeGrowthGlobal0X128Ref) (.var "feeGrowth0Delta")) ])
          [],
        Stmt.ite (gtE (.var "paid1") (.intLit 0))
          ([ .letDecl "feeProtocol1" (some uint8)
                (shlE (.intLit 0) (.intLit 0)),
             .assign .localVar (varRef "feeProtocol1")
                (.binary .shr (.storage (slot0F "feeProtocol")) (.intLit 4)),
             .letDecl "fees1" (some uint256)
                (.ite (eqE (.var "feeProtocol1") (.intLit 0))
                  (.intLit 0)
                  (divE (.var "paid1") (.var "feeProtocol1"))),
             Stmt.ite (gtE (uint128Wrap (.var "fees1")) (.intLit 0))
                [ .assign .storage (protocolFeesF "token1")
                    (addE (.storage (protocolFeesF "token1")) (uint128Wrap (.var "fees1"))) ]
                [] ] ++
            mulDivLet "feeGrowth1Delta" (subE (.var "paid1") (.var "fees1"))
              fixedPoint128Q128 (.var "_liquidity") ++
            [ .assign .storage feeGrowthGlobal1X128Ref
                (addE (.storage feeGrowthGlobal1X128Ref) (.var "feeGrowth1Delta")) ])
          [] ] ++
      lockSuffix }

def increaseobservationcardinalitynextTransition (v : PoolImmutables) : TransitionDecl :=
  { name := "increaseObservationCardinalityNext"
    params := [ { name := "observationCardinalityNext", ty := uint16 } ]
    returnType := []
    body := nonpayable ++ lockPrefix ++ noDelegateCall v ++
      [ .letDecl "observationCardinalityNextOld" (some uint16)
          (.storage (slot0F "observationCardinalityNext")),
        .letDecl "observationCardinalityNextNew" (some uint16)
          (.var "observationCardinalityNext"),
        .require (gtE (.var "observationCardinalityNextOld") (.intLit 0)),
        Stmt.ite (leE (.var "observationCardinalityNextNew")
            (.var "observationCardinalityNextOld"))
          [ .assign .localVar (varRef "observationCardinalityNextNew")
              (.var "observationCardinalityNextOld") ]
          [ .letDecl "i" (some uint16) (.var "observationCardinalityNextOld"),
            .while (ltE (.var "i") (.var "observationCardinalityNextNew"))
              [ .assign .storage (observationsRawF (.var "i") "blockTimestamp") (.intLit 1),
                .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ] ],
        .assign .storage (slot0F "observationCardinalityNext")
          (.var "observationCardinalityNextNew") ] ++
      lockSuffix }

def initializeTransition : TransitionDecl :=
  { name := "initialize"
    params := [ { name := "sqrtPriceX96", ty := uint160 } ]
    returnType := []
    body := nonpayable ++
      [ .require (eqE (.storage (slot0F "sqrtPriceX96")) (.intLit 0)),
        .internalCall "getTickAtSqrtRatio" [.var "sqrtPriceX96"] "tick",
        .letDecl "time" (some uint32) (modE (.env .timestamp) uint32Modulus),
        .assign .storage (observationsF (.intLit 0) "blockTimestamp") (.var "time"),
        .assign .storage (observationsF (.intLit 0) "tickCumulative") (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "secondsPerLiquidityCumulativeX128") (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "initialized") (.boolLit true),
        .assign .storage (slot0F "sqrtPriceX96") (.var "sqrtPriceX96"),
        .assign .storage (slot0F "tick") (.var "tick"),
        .assign .storage (slot0F "observationIndex") (.intLit 0),
        .assign .storage (slot0F "observationCardinality") (.intLit 1),
        .assign .storage (slot0F "observationCardinalityNext") (.intLit 1),
        .assign .storage (slot0F "feeProtocol") (.intLit 0),
        .assign .storage (slot0F "unlocked") (.boolLit true) ] }

def liquidityTransition : TransitionDecl :=
  { name := "liquidity"
    params := []
    returnType := [uint128]
    body := nonpayable ++ [ .return [.storage liquidityRef] ] }

def maxliquiditypertickTransition (v : PoolImmutables) : TransitionDecl :=
  { name := "maxLiquidityPerTick"
    params := []
    returnType := [uint128]
    body := nonpayable ++ [ .return [.intLit v.maxLiquidityPerTick] ] }

def mintTransition (v : PoolImmutables) : TransitionDecl :=
  { name := "mint"
    params :=
      [ { name := "recipient", ty := addr }, { name := "tickLower", ty := int24 },
        { name := "tickUpper", ty := int24 }, { name := "amount", ty := uint128 },
        { name := "data", ty := bytesTy } ]
    returnType := [uint256, uint256]
    body := nonpayable ++ lockPrefix ++
      [ .require (gtE (.var "amount") (.intLit 0)),
        .letDecl "liquidityDelta" (some int128) (.inRange int128Int (.var "amount")),
        .internalCall "modifyPosition"
          [.var "recipient", .var "tickLower", .var "tickUpper", .var "liquidityDelta"]
          "modified",
        .letDecl "amount0" (some uint256) (uint256Wrap (tuple1 (.var "modified"))),
        .letDecl "amount1" (some uint256) (uint256Wrap (tuple2 (.var "modified"))),
        Stmt.ite (gtE (.var "amount0") (.intLit 0))
          (balanceOfInto (addrLit v.token0) "balance0Before" "mintBalance0Before")
          [],
        Stmt.ite (gtE (.var "amount1") (.intLit 0))
          (balanceOfInto (addrLit v.token1) "balance1Before" "mintBalance1Before")
          [],
        .externalCall (.env .caller) "uniswapV3MintCallback" (.intLit 0)
          [.var "amount0", .var "amount1", .var "data"] "_mintCallback",
        Stmt.ite (gtE (.var "amount0") (.intLit 0))
          (balanceOfInto (addrLit v.token0) "balance0After" "mintBalance0After" ++
            checkedWordAddLe (.var "balance0Before") (.var "amount0") (.var "balance0After"))
          [],
        Stmt.ite (gtE (.var "amount1") (.intLit 0))
          (balanceOfInto (addrLit v.token1) "balance1After" "mintBalance1After" ++
            checkedWordAddLe (.var "balance1Before") (.var "amount1") (.var "balance1After"))
          [] ] ++
      lockSuffix ++
      [ .return [.var "amount0", .var "amount1"] ] }

def observationsTransition : TransitionDecl :=
  { name := "observations"
    params := [ { name := "arg0", ty := uint256 } ]
    returnType := [uint32, int56, uint160, boolTy]
    body := nonpayable ++
      [ .require (ltE (.var "arg0") (.intLit 65535)),
        .return
          [ .storage (observationsRawF (.var "arg0") "blockTimestamp"),
            .storage (observationsRawF (.var "arg0") "tickCumulative"),
            .storage (observationsRawF (.var "arg0") "secondsPerLiquidityCumulativeX128"),
            .storage (observationsRawF (.var "arg0") "initialized") ] ] }

def observeTransition (v : PoolImmutables) : TransitionDecl :=
  { name := "observe"
    params := [ { name := "secondsAgos", ty := (.dynamicArray uint32) } ]
    returnType := [(.dynamicArray int56), (.dynamicArray uint160)]
    body := nonpayable ++ noDelegateCall v ++
      [ .internalCall "observeBody"
          [ blockTimestamp32, .var "secondsAgos", .storage (slot0F "tick"),
            .storage (slot0F "observationIndex"), .storage liquidityRef,
            .storage (slot0F "observationCardinality") ]
          "observed",
        .return [tuple0 (.var "observed"), tuple1 (.var "observed")] ] }

def positionsTransition : TransitionDecl :=
  { name := "positions"
    params := [ { name := "arg0", ty := bytes32 } ]
    returnType := [uint128, uint256, uint256, uint128, uint128]
    body := nonpayable ++ [ .return [(.storage (positionsF (.var "arg0") "liquidity")), (.storage (positionsF (.var "arg0") "feeGrowthInside0LastX128")), (.storage (positionsF (.var "arg0") "feeGrowthInside1LastX128")), (.storage (positionsF (.var "arg0") "tokensOwed0")), (.storage (positionsF (.var "arg0") "tokensOwed1"))] ] }

def protocolfeesTransition : TransitionDecl :=
  { name := "protocolFees"
    params := []
    returnType := [uint128, uint128]
    body := nonpayable ++ [ .return [(.storage (protocolFeesF "token0")), (.storage (protocolFeesF "token1"))] ] }

def setfeeprotocolTransition (v : PoolImmutables) : TransitionDecl :=
  { name := "setFeeProtocol"
    params := [ { name := "feeProtocol0", ty := uint8 }, { name := "feeProtocol1", ty := uint8 } ]
    returnType := []
    body := nonpayable ++ lockPrefix ++ onlyFactoryOwner v ++
      [ .require
          (andE (feeProtocolEnabled (.var "feeProtocol0"))
            (feeProtocolEnabled (.var "feeProtocol1"))),
        .letDecl "feeProtocolOld" (some uint8) (.storage (slot0F "feeProtocol")),
        .assign .storage (slot0F "feeProtocol")
          (addE (.var "feeProtocol0") (shlE (.var "feeProtocol1") (.intLit 4))) ] ++
      lockSuffix }

def slot0Transition : TransitionDecl :=
  { name := "slot0"
    params := []
    returnType := [uint160, int24, uint16, uint16, uint16, uint8, boolTy]
    body := nonpayable ++ [ .return [(.storage (slot0F "sqrtPriceX96")), (.storage (slot0F "tick")), (.storage (slot0F "observationIndex")), (.storage (slot0F "observationCardinality")), (.storage (slot0F "observationCardinalityNext")), (.storage (slot0F "feeProtocol")), (.storage (slot0F "unlocked"))] ] }

def snapshotcumulativesinsideTransition (v : PoolImmutables) : TransitionDecl :=
  { name := "snapshotCumulativesInside"
    params := [ { name := "tickLower", ty := int24 }, { name := "tickUpper", ty := int24 } ]
    returnType := [int56, uint160, uint32]
    body := nonpayable ++ noDelegateCall v ++
      checkTicksBody (.var "tickLower") (.var "tickUpper") ++
      [ .letStorage "lower" (ticksRef (.var "tickLower")),
        .letStorage "upper" (ticksRef (.var "tickUpper")),
        .require (.field (.var "lower") "initialized"),
        .require (.field (.var "upper") "initialized"),
        Stmt.ite (ltE (.storage (slot0F "tick")) (.var "tickLower"))
          [ .return
              [ int56Wrap
                  (subE (.field (.var "lower") "tickCumulativeOutside")
                    (.field (.var "upper") "tickCumulativeOutside")),
                uint160Wrap
                  (subE (.field (.var "lower") "secondsPerLiquidityOutsideX128")
                    (.field (.var "upper") "secondsPerLiquidityOutsideX128")),
                uint32Wrap
                  (subE (.field (.var "lower") "secondsOutside")
                    (.field (.var "upper") "secondsOutside")) ] ]
          [],
        Stmt.ite (ltE (.storage (slot0F "tick")) (.var "tickUpper"))
          [ .letDecl "time" (some uint32) blockTimestamp32,
            .internalCall "observeSingle"
              [ .var "time", .intLit 0, .storage (slot0F "tick"),
                .storage (slot0F "observationIndex"), .storage liquidityRef,
                .storage (slot0F "observationCardinality") ]
              "currentObservation",
            .return
              [ int56Wrap
                  (subE (subE (tuple0 (.var "currentObservation"))
                      (.field (.var "lower") "tickCumulativeOutside"))
                    (.field (.var "upper") "tickCumulativeOutside")),
                uint160Wrap
                  (subE (subE (tuple1 (.var "currentObservation"))
                      (.field (.var "lower") "secondsPerLiquidityOutsideX128"))
                    (.field (.var "upper") "secondsPerLiquidityOutsideX128")),
                uint32Wrap
                  (subE (subE (.var "time") (.field (.var "lower") "secondsOutside"))
                    (.field (.var "upper") "secondsOutside")) ] ]
          [ .return
              [ int56Wrap
                  (subE (.field (.var "upper") "tickCumulativeOutside")
                    (.field (.var "lower") "tickCumulativeOutside")),
                uint160Wrap
                  (subE (.field (.var "upper") "secondsPerLiquidityOutsideX128")
                    (.field (.var "lower") "secondsPerLiquidityOutsideX128")),
                uint32Wrap
                  (subE (.field (.var "upper") "secondsOutside")
                    (.field (.var "lower") "secondsOutside")) ] ] ] }

def swapTransition (v : PoolImmutables) : TransitionDecl :=
  { name := "swap"
    params :=
      [ { name := "recipient", ty := addr }, { name := "zeroForOne", ty := boolTy },
        { name := "amountSpecified", ty := int256 },
        { name := "sqrtPriceLimitX96", ty := uint160 }, { name := "data", ty := bytesTy } ]
    returnType := [int256, int256]
    body := nonpayable ++ noDelegateCall v ++
      [ .require (neE (.var "amountSpecified") (.intLit 0)),
        .letDecl "slot0StartSqrtPriceX96" (some uint160) (.storage (slot0F "sqrtPriceX96")),
        .letDecl "slot0StartTick" (some int24) (.storage (slot0F "tick")),
        .letDecl "slot0StartObservationIndex" (some uint16)
          (.storage (slot0F "observationIndex")),
        .letDecl "slot0StartObservationCardinality" (some uint16)
          (.storage (slot0F "observationCardinality")),
        .letDecl "slot0StartObservationCardinalityNext" (some uint16)
          (.storage (slot0F "observationCardinalityNext")),
        .letDecl "slot0StartFeeProtocol" (some uint8) (.storage (slot0F "feeProtocol")),
        .letDecl "slot0StartUnlocked" (some boolTy) (.storage (slot0F "unlocked")),
        .require (.var "slot0StartUnlocked"),
        .require
          (.ite (.var "zeroForOne")
            (andE (ltE (.var "sqrtPriceLimitX96") (.var "slot0StartSqrtPriceX96"))
              (gtE (.var "sqrtPriceLimitX96") minSqrtRatio))
            (andE (gtE (.var "sqrtPriceLimitX96") (.var "slot0StartSqrtPriceX96"))
              (ltE (.var "sqrtPriceLimitX96") maxSqrtRatio))),
        .assign .storage (slot0F "unlocked") (.boolLit false),
        .letDecl "cacheLiquidityStart" (some uint128) (.storage liquidityRef),
        .letDecl "cacheBlockTimestamp" (some uint32) blockTimestamp32,
        .letDecl "cacheFeeProtocol" (some uint8)
          (.ite (.var "zeroForOne")
            (modE (.var "slot0StartFeeProtocol") (.intLit 16))
            (shrE (.var "slot0StartFeeProtocol") (.intLit 4))),
        .letDecl "cacheSecondsPerLiquidityCumulativeX128" (some uint160) (.intLit 0),
        .letDecl "cacheTickCumulative" (some int56) (.intLit 0),
        .letDecl "cacheComputedLatestObservation" (some boolTy) (.boolLit false),
        .letDecl "exactInput" (some boolTy) (gtE (.var "amountSpecified") (.intLit 0)),
        .letDecl "stateAmountSpecifiedRemaining" (some int256) (.var "amountSpecified"),
        .letDecl "stateAmountCalculated" (some int256) (.intLit 0),
        .letDecl "stateSqrtPriceX96" (some uint160) (.var "slot0StartSqrtPriceX96"),
        .letDecl "stateTick" (some int24) (.var "slot0StartTick"),
        .letDecl "stateFeeGrowthGlobalX128" (some uint256)
          (.ite (.var "zeroForOne") (.storage feeGrowthGlobal0X128Ref)
            (.storage feeGrowthGlobal1X128Ref)),
        .letDecl "stateProtocolFee" (some uint128) (.intLit 0),
        .letDecl "stateLiquidity" (some uint128) (.var "cacheLiquidityStart"),
        .while
          (andE (neE (.var "stateAmountSpecifiedRemaining") (.intLit 0))
            (neE (.var "stateSqrtPriceX96") (.var "sqrtPriceLimitX96")))
          [ .letDecl "stepSqrtPriceStartX96" (some uint160) (.var "stateSqrtPriceX96"),
            .internalCall "tickBitmapNextInitializedTickWithinOneWord"
              [.var "stateTick", .intLit v.tickSpacing, .var "zeroForOne"]
              "nextTick",
            .letDecl "stepTickNext" (some int24) (tuple0 (.var "nextTick")),
            .letDecl "stepInitialized" (some boolTy) (tuple1 (.var "nextTick")),
            Stmt.ite (ltE (.var "stepTickNext") minTick)
              [ .assign .localVar (varRef "stepTickNext") minTick ]
              [ Stmt.ite (gtE (.var "stepTickNext") maxTick)
                  [ .assign .localVar (varRef "stepTickNext") maxTick ]
                  [] ],
            .internalCall "getSqrtRatioAtTick" [.var "stepTickNext"]
              "stepSqrtPriceNextX96",
            .letDecl "stepTargetSqrtPriceX96" (some uint160)
              (.ite
                (.ite (.var "zeroForOne")
                  (ltE (.var "stepSqrtPriceNextX96") (.var "sqrtPriceLimitX96"))
                  (gtE (.var "stepSqrtPriceNextX96") (.var "sqrtPriceLimitX96")))
                (.var "sqrtPriceLimitX96")
                (.var "stepSqrtPriceNextX96")),
            .internalCall "computeSwapStep"
              [ .var "stateSqrtPriceX96", .var "stepTargetSqrtPriceX96",
                .var "stateLiquidity", .var "stateAmountSpecifiedRemaining",
                .intLit v.fee ]
              "stepResult",
            .assign .localVar (varRef "stateSqrtPriceX96") (tuple0 (.var "stepResult")),
            .letDecl "stepAmountIn" (some uint256) (tuple1 (.var "stepResult")),
            .letDecl "stepAmountOut" (some uint256) (tuple2 (.var "stepResult")),
            .letDecl "stepFeeAmount" (some uint256) (tuple3 (.var "stepResult")),
            Stmt.ite (.var "exactInput")
              [ .assign .localVar (varRef "stateAmountSpecifiedRemaining")
                  (.inRange int256Int
                    (subE (.var "stateAmountSpecifiedRemaining")
                      (.inRange int256Int (addE (.var "stepAmountIn") (.var "stepFeeAmount"))))),
                .assign .localVar (varRef "stateAmountCalculated")
                  (.inRange int256Int
                    (subE (.var "stateAmountCalculated")
                      (.inRange int256Int (.var "stepAmountOut")))) ]
              [ .assign .localVar (varRef "stateAmountSpecifiedRemaining")
                  (.inRange int256Int
                    (addE (.var "stateAmountSpecifiedRemaining")
                      (.inRange int256Int (.var "stepAmountOut")))),
                .assign .localVar (varRef "stateAmountCalculated")
                  (.inRange int256Int
                    (addE (.var "stateAmountCalculated")
                      (.inRange int256Int (addE (.var "stepAmountIn") (.var "stepFeeAmount"))))) ],
            Stmt.ite (gtE (.var "cacheFeeProtocol") (.intLit 0))
              [ .letDecl "protocolDelta" (some uint256)
                  (divE (.var "stepFeeAmount") (.var "cacheFeeProtocol")),
                .assign .localVar (varRef "stepFeeAmount")
                  (subE (.var "stepFeeAmount") (.var "protocolDelta")),
                .assign .localVar (varRef "stateProtocolFee")
                  (uint128Wrap
                    (addE (.var "stateProtocolFee") (uint128Wrap (.var "protocolDelta")))) ]
              [],
            Stmt.ite (gtE (.var "stateLiquidity") (.intLit 0))
              (mulDivLet "feeGrowthGlobalDelta" (.var "stepFeeAmount") fixedPoint128Q128
                  (.var "stateLiquidity") ++
                [ .assign .localVar (varRef "stateFeeGrowthGlobalX128")
                    (wordAdd (.var "stateFeeGrowthGlobalX128") (.var "feeGrowthGlobalDelta")) ])
              [],
            Stmt.ite (eqE (.var "stateSqrtPriceX96") (.var "stepSqrtPriceNextX96"))
              [ Stmt.ite (.var "stepInitialized")
                  [ Stmt.ite (notE (.var "cacheComputedLatestObservation"))
                      [ .internalCall "observeSingle"
                          [ .var "cacheBlockTimestamp", .intLit 0, .var "slot0StartTick",
                            .var "slot0StartObservationIndex", .var "cacheLiquidityStart",
                            .var "slot0StartObservationCardinality" ]
                          "latestObservation",
                        .assign .localVar (varRef "cacheTickCumulative")
                          (tuple0 (.var "latestObservation")),
                        .assign .localVar (varRef "cacheSecondsPerLiquidityCumulativeX128")
                          (tuple1 (.var "latestObservation")),
                        .assign .localVar (varRef "cacheComputedLatestObservation")
                          (.boolLit true) ]
                      [],
                    .internalCall "tickCross"
                      [ .var "stepTickNext",
                        .ite (.var "zeroForOne") (.var "stateFeeGrowthGlobalX128")
                          (.storage feeGrowthGlobal0X128Ref),
                        .ite (.var "zeroForOne") (.storage feeGrowthGlobal1X128Ref)
                          (.var "stateFeeGrowthGlobalX128"),
                        .var "cacheSecondsPerLiquidityCumulativeX128",
                        .var "cacheTickCumulative", .var "cacheBlockTimestamp" ]
                      "liquidityNetCross",
                    .letDecl "liquidityNet" (some int128) (.var "liquidityNetCross"),
                    Stmt.ite (.var "zeroForOne")
                      [ .assign .localVar (varRef "liquidityNet")
                          (.inRange int128Int (subE (.intLit 0) (.var "liquidityNet"))) ]
                      [],
                    .internalCall "liquidityAddDelta"
                      [.var "stateLiquidity", .var "liquidityNet"]
                      "stateLiquidityAfterCross",
                    .assign .localVar (varRef "stateLiquidity")
                      (.var "stateLiquidityAfterCross") ]
                  [],
                .assign .localVar (varRef "stateTick")
                  (.ite (.var "zeroForOne") (subE (.var "stepTickNext") (.intLit 1))
                    (.var "stepTickNext")) ]
              [ Stmt.ite (neE (.var "stateSqrtPriceX96") (.var "stepSqrtPriceStartX96"))
                  [ .internalCall "getTickAtSqrtRatio" [.var "stateSqrtPriceX96"]
                      "stateTickUpdated",
                    .assign .localVar (varRef "stateTick") (.var "stateTickUpdated") ]
                  [] ] ],
        Stmt.ite (neE (.var "stateTick") (.var "slot0StartTick"))
          [ .internalCall "oracleWrite"
              [ .var "slot0StartObservationIndex", .var "cacheBlockTimestamp",
                .var "slot0StartTick", .var "cacheLiquidityStart",
                .var "slot0StartObservationCardinality",
                .var "slot0StartObservationCardinalityNext" ]
              "oracleUpdatedAfterSwap",
            .assign .storage (slot0F "sqrtPriceX96") (.var "stateSqrtPriceX96"),
            .assign .storage (slot0F "tick") (.var "stateTick"),
            .assign .storage (slot0F "observationIndex") (tuple0 (.var "oracleUpdatedAfterSwap")),
            .assign .storage (slot0F "observationCardinality")
              (tuple1 (.var "oracleUpdatedAfterSwap")) ]
          [ .assign .storage (slot0F "sqrtPriceX96") (.var "stateSqrtPriceX96") ],
        Stmt.ite (neE (.var "cacheLiquidityStart") (.var "stateLiquidity"))
          [ .assign .storage liquidityRef (.var "stateLiquidity") ]
          [],
        Stmt.ite (.var "zeroForOne")
          [ .assign .storage feeGrowthGlobal0X128Ref (.var "stateFeeGrowthGlobalX128"),
            Stmt.ite (gtE (.var "stateProtocolFee") (.intLit 0))
              [ .assign .storage (protocolFeesF "token0")
                  (addE (.storage (protocolFeesF "token0")) (.var "stateProtocolFee")) ]
              [] ]
          [ .assign .storage feeGrowthGlobal1X128Ref (.var "stateFeeGrowthGlobalX128"),
            Stmt.ite (gtE (.var "stateProtocolFee") (.intLit 0))
              [ .assign .storage (protocolFeesF "token1")
                  (addE (.storage (protocolFeesF "token1")) (.var "stateProtocolFee")) ]
              [] ],
        .letDecl "amount0" (some int256) (.intLit 0),
        .letDecl "amount1" (some int256) (.intLit 0),
        Stmt.ite (eqE (.var "zeroForOne") (.var "exactInput"))
          [ .assign .localVar (varRef "amount0")
              (.inRange int256Int
                (subE (.var "amountSpecified") (.var "stateAmountSpecifiedRemaining"))),
            .assign .localVar (varRef "amount1") (.var "stateAmountCalculated") ]
          [ .assign .localVar (varRef "amount0") (.var "stateAmountCalculated"),
            .assign .localVar (varRef "amount1")
              (.inRange int256Int
                (subE (.var "amountSpecified") (.var "stateAmountSpecifiedRemaining"))) ],
        Stmt.ite (.var "zeroForOne")
          ([ Stmt.ite (ltE (.var "amount1") (.intLit 0))
              (safeTransfer (addrLit v.token1) (.var "recipient")
                (uint256Wrap (subE (.intLit 0) (.var "amount1"))) "swapTransfer1")
              [] ] ++
            balanceOfInto (addrLit v.token0) "balance0Before" "swapBalance0Before" ++
            [ .externalCall (.env .caller) "uniswapV3SwapCallback" (.intLit 0)
                [.var "amount0", .var "amount1", .var "data"] "_swapCallback" ] ++
            balanceOfInto (addrLit v.token0) "balance0After" "swapBalance0After" ++
            checkedWordAddLe (.var "balance0Before") (uint256Wrap (.var "amount0"))
              (.var "balance0After"))
          ([ Stmt.ite (ltE (.var "amount0") (.intLit 0))
              (safeTransfer (addrLit v.token0) (.var "recipient")
                (uint256Wrap (subE (.intLit 0) (.var "amount0"))) "swapTransfer0")
              [] ] ++
            balanceOfInto (addrLit v.token1) "balance1Before" "swapBalance1Before" ++
            [ .externalCall (.env .caller) "uniswapV3SwapCallback" (.intLit 0)
                [.var "amount0", .var "amount1", .var "data"] "_swapCallback" ] ++
            balanceOfInto (addrLit v.token1) "balance1After" "swapBalance1After" ++
            checkedWordAddLe (.var "balance1Before") (uint256Wrap (.var "amount1"))
              (.var "balance1After")) ] ++
      lockSuffix ++
      [ .return [.var "amount0", .var "amount1"] ] }

def tickbitmapTransition : TransitionDecl :=
  { name := "tickBitmap"
    params := [ { name := "arg0", ty := int16 } ]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (tickBitmapRef (.var "arg0"))] ] }

def tickspacingTransition (v : PoolImmutables) : TransitionDecl :=
  { name := "tickSpacing"
    params := []
    returnType := [int24]
    body := nonpayable ++ [ .return [.intLit v.tickSpacing] ] }

def ticksTransition : TransitionDecl :=
  { name := "ticks"
    params := [ { name := "arg0", ty := int24 } ]
    returnType := [uint128, int128, uint256, uint256, int56, uint160, uint32, boolTy]
    body := nonpayable ++ [ .return [(.storage (ticksF (.var "arg0") "liquidityGross")), (.storage (ticksF (.var "arg0") "liquidityNet")), (.storage (ticksF (.var "arg0") "feeGrowthOutside0X128")), (.storage (ticksF (.var "arg0") "feeGrowthOutside1X128")), (.storage (ticksF (.var "arg0") "tickCumulativeOutside")), (.storage (ticksF (.var "arg0") "secondsPerLiquidityOutsideX128")), (.storage (ticksF (.var "arg0") "secondsOutside")), (.storage (ticksF (.var "arg0") "initialized"))] ] }

def token0Transition (v : PoolImmutables) : TransitionDecl :=
  { name := "token0"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [addrLit v.token0] ] }

def token1Transition (v : PoolImmutables) : TransitionDecl :=
  { name := "token1"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [addrLit v.token1] ] }

def transitions (v : PoolImmutables) : List TransitionDecl :=
  [
        burnTransition,
        collectTransition v,
        collectprotocolTransition v,
        factoryTransition v,
        feeTransition v,
        feegrowthglobal0X128Transition,
        feegrowthglobal1X128Transition,
        flashTransition v,
        increaseobservationcardinalitynextTransition v,
        initializeTransition,
        liquidityTransition,
        maxliquiditypertickTransition v,
        mintTransition v,
        observationsTransition,
        observeTransition v,
        positionsTransition,
        protocolfeesTransition,
        setfeeprotocolTransition v,
        slot0Transition,
        snapshotcumulativesinsideTransition v,
        swapTransition v,
        tickbitmapTransition,
        tickspacingTransition v,
        ticksTransition,
        token0Transition v,
        token1Transition v ]

def contract (v : PoolImmutables) : ContractDecl :=
  { name := "UniswapV3Pool"
    storage := storageDecls
    ctor := constructorDecl
    structs := structs
    functions := functions v
    transitions := transitions v }

def config (v : PoolImmutables) : Config :=
  { storage := storageLayout
    externalABI := poolExternalABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment (contract v).ctor.params }

end Benchmarks.UniswapV3Pool
