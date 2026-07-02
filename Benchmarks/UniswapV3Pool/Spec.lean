import Solm.Semantics
import Solm.SolidityLayout

/-!
# UniswapV3Pool benchmark spec

Solm benchmark scaffold for upstream `Uniswap/v3-core` `Benchmarks/UniswapV3Pool/contracts/UniswapV3Pool.sol`.
The storage declarations and raw storage layout are transcribed from solc's storage-layout output.
Events and fallback/receive dispatch are omitted; the selector-dispatched ABI surface is explicit.

The transition bodies are ABI-shaped proof scaffolds: they enforce nonpayable call-value checks,
return storage-backed values for compiler-visible public state where practical, and otherwise use
zero/default return values until the full source semantics are proved.
-/

open Solm ABI

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

/-! ## Storage references -/

def slot0F (field : Ident) : StorageRef := { base := "slot0", steps := [.field field] }
def protocolFeesF (field : Ident) : StorageRef := { base := "protocolFees", steps := [.field field] }
def ticksF (tick : Expr) (field : Ident) : StorageRef :=
  { base := "ticks", steps := [.mindex tick, .field field] }
def tickBitmapRef (wordPosition : Expr) : StorageRef :=
  { base := "tickBitmap", steps := [.mindex wordPosition] }
def positionsF (key : Expr) (field : Ident) : StorageRef :=
  { base := "positions", steps := [.mindex key, .field field] }
def observationsF (index : Expr) (field : Ident) : StorageRef :=
  { base := "observations", steps := [.aindex index, .field field] }
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
    { name := "observations", ty := .array observationStructTy 65535 } ]

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
  | _, _ => none

def storageLayout : StorageLayout :=
  solidityStorageLayout storageLayoutRaw

/-! ## Shared source patterns -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := []
    body := nonpayable }

/-! ## Public ABI surface -/

def burnTransition : TransitionDecl :=
  { name := "burn"
    params := [ { name := "tickLower", ty := int24 }, { name := "tickUpper", ty := int24 }, { name := "amount", ty := uint128 } ]
    returnType := (some (.tuple [uint256, uint256]))
    body := nonpayable ++ [ .return (.tupleLit [(.intLit 0), (.intLit 0)]) ] }

def collectTransition : TransitionDecl :=
  { name := "collect"
    params := [ { name := "recipient", ty := addr }, { name := "tickLower", ty := int24 }, { name := "tickUpper", ty := int24 }, { name := "amount0Requested", ty := uint128 }, { name := "amount1Requested", ty := uint128 } ]
    returnType := (some (.tuple [uint128, uint128]))
    body := nonpayable ++ [ .return (.tupleLit [(.intLit 0), (.intLit 0)]) ] }

def collectprotocolTransition : TransitionDecl :=
  { name := "collectProtocol"
    params := [ { name := "recipient", ty := addr }, { name := "amount0Requested", ty := uint128 }, { name := "amount1Requested", ty := uint128 } ]
    returnType := (some (.tuple [uint128, uint128]))
    body := nonpayable ++ [ .return (.tupleLit [(.intLit 0), (.intLit 0)]) ] }

def factoryTransition : TransitionDecl :=
  { name := "factory"
    params := []
    returnType := (some addr)
    body := nonpayable ++ [ .return zeroAddr ] }

def feeTransition : TransitionDecl :=
  { name := "fee"
    params := []
    returnType := (some uint24)
    body := nonpayable ++ [ .return (.intLit 0) ] }

def feegrowthglobal0X128Transition : TransitionDecl :=
  { name := "feeGrowthGlobal0X128"
    params := []
    returnType := (some uint256)
    body := nonpayable ++ [ .return (.storage feeGrowthGlobal0X128Ref) ] }

def feegrowthglobal1X128Transition : TransitionDecl :=
  { name := "feeGrowthGlobal1X128"
    params := []
    returnType := (some uint256)
    body := nonpayable ++ [ .return (.storage feeGrowthGlobal1X128Ref) ] }

def flashTransition : TransitionDecl :=
  { name := "flash"
    params := [ { name := "recipient", ty := addr }, { name := "amount0", ty := uint256 }, { name := "amount1", ty := uint256 }, { name := "data", ty := bytesTy } ]
    returnType := none
    body := nonpayable }

def increaseobservationcardinalitynextTransition : TransitionDecl :=
  { name := "increaseObservationCardinalityNext"
    params := [ { name := "observationCardinalityNext", ty := uint16 } ]
    returnType := none
    body := nonpayable }

def initializeTransition : TransitionDecl :=
  { name := "initialize"
    params := [ { name := "sqrtPriceX96", ty := uint160 } ]
    returnType := none
    body := nonpayable }

def liquidityTransition : TransitionDecl :=
  { name := "liquidity"
    params := []
    returnType := (some uint128)
    body := nonpayable ++ [ .return (.storage liquidityRef) ] }

def maxliquiditypertickTransition : TransitionDecl :=
  { name := "maxLiquidityPerTick"
    params := []
    returnType := (some uint128)
    body := nonpayable ++ [ .return (.intLit 0) ] }

def mintTransition : TransitionDecl :=
  { name := "mint"
    params := [ { name := "recipient", ty := addr }, { name := "tickLower", ty := int24 }, { name := "tickUpper", ty := int24 }, { name := "amount", ty := uint128 }, { name := "data", ty := bytesTy } ]
    returnType := (some (.tuple [uint256, uint256]))
    body := nonpayable ++ [ .return (.tupleLit [(.intLit 0), (.intLit 0)]) ] }

def observationsTransition : TransitionDecl :=
  { name := "observations"
    params := [ { name := "arg0", ty := uint256 } ]
    returnType := (some (.tuple [uint32, int56, uint160, boolTy]))
    body := nonpayable ++ [ .return (.tupleLit [(.storage (observationsF (.var "arg0") "blockTimestamp")), (.storage (observationsF (.var "arg0") "tickCumulative")), (.storage (observationsF (.var "arg0") "secondsPerLiquidityCumulativeX128")), (.storage (observationsF (.var "arg0") "initialized"))]) ] }

def observeTransition : TransitionDecl :=
  { name := "observe"
    params := [ { name := "secondsAgos", ty := (.dynamicArray uint32) } ]
    returnType := (some (.tuple [(.dynamicArray int56), (.dynamicArray uint160)]))
    body := nonpayable ++ [ .return (.tupleLit [(.arrayLit []), (.arrayLit [])]) ] }

def positionsTransition : TransitionDecl :=
  { name := "positions"
    params := [ { name := "arg0", ty := bytes32 } ]
    returnType := (some (.tuple [uint128, uint256, uint256, uint128, uint128]))
    body := nonpayable ++ [ .return (.tupleLit [(.storage (positionsF (.var "arg0") "liquidity")), (.storage (positionsF (.var "arg0") "feeGrowthInside0LastX128")), (.storage (positionsF (.var "arg0") "feeGrowthInside1LastX128")), (.storage (positionsF (.var "arg0") "tokensOwed0")), (.storage (positionsF (.var "arg0") "tokensOwed1"))]) ] }

def protocolfeesTransition : TransitionDecl :=
  { name := "protocolFees"
    params := []
    returnType := (some (.tuple [uint128, uint128]))
    body := nonpayable ++ [ .return (.tupleLit [(.storage (protocolFeesF "token0")), (.storage (protocolFeesF "token1"))]) ] }

def setfeeprotocolTransition : TransitionDecl :=
  { name := "setFeeProtocol"
    params := [ { name := "feeProtocol0", ty := uint8 }, { name := "feeProtocol1", ty := uint8 } ]
    returnType := none
    body := nonpayable }

def slot0Transition : TransitionDecl :=
  { name := "slot0"
    params := []
    returnType := (some (.tuple [uint160, int24, uint16, uint16, uint16, uint8, boolTy]))
    body := nonpayable ++ [ .return (.tupleLit [(.storage (slot0F "sqrtPriceX96")), (.storage (slot0F "tick")), (.storage (slot0F "observationIndex")), (.storage (slot0F "observationCardinality")), (.storage (slot0F "observationCardinalityNext")), (.storage (slot0F "feeProtocol")), (.storage (slot0F "unlocked"))]) ] }

def snapshotcumulativesinsideTransition : TransitionDecl :=
  { name := "snapshotCumulativesInside"
    params := [ { name := "tickLower", ty := int24 }, { name := "tickUpper", ty := int24 } ]
    returnType := (some (.tuple [int56, uint160, uint32]))
    body := nonpayable ++ [ .return (.tupleLit [(.intLit 0), (.intLit 0), (.intLit 0)]) ] }

def swapTransition : TransitionDecl :=
  { name := "swap"
    params := [ { name := "recipient", ty := addr }, { name := "zeroForOne", ty := boolTy }, { name := "amountSpecified", ty := int256 }, { name := "sqrtPriceLimitX96", ty := uint160 }, { name := "data", ty := bytesTy } ]
    returnType := (some (.tuple [int256, int256]))
    body := nonpayable ++ [ .return (.tupleLit [(.intLit 0), (.intLit 0)]) ] }

def tickbitmapTransition : TransitionDecl :=
  { name := "tickBitmap"
    params := [ { name := "arg0", ty := int16 } ]
    returnType := (some uint256)
    body := nonpayable ++ [ .return (.storage (tickBitmapRef (.var "arg0"))) ] }

def tickspacingTransition : TransitionDecl :=
  { name := "tickSpacing"
    params := []
    returnType := (some int24)
    body := nonpayable ++ [ .return (.intLit 0) ] }

def ticksTransition : TransitionDecl :=
  { name := "ticks"
    params := [ { name := "arg0", ty := int24 } ]
    returnType := (some (.tuple [uint128, int128, uint256, uint256, int56, uint160, uint32, boolTy]))
    body := nonpayable ++ [ .return (.tupleLit [(.storage (ticksF (.var "arg0") "liquidityGross")), (.storage (ticksF (.var "arg0") "liquidityNet")), (.storage (ticksF (.var "arg0") "feeGrowthOutside0X128")), (.storage (ticksF (.var "arg0") "feeGrowthOutside1X128")), (.storage (ticksF (.var "arg0") "tickCumulativeOutside")), (.storage (ticksF (.var "arg0") "secondsPerLiquidityOutsideX128")), (.storage (ticksF (.var "arg0") "secondsOutside")), (.storage (ticksF (.var "arg0") "initialized"))]) ] }

def token0Transition : TransitionDecl :=
  { name := "token0"
    params := []
    returnType := (some addr)
    body := nonpayable ++ [ .return zeroAddr ] }

def token1Transition : TransitionDecl :=
  { name := "token1"
    params := []
    returnType := (some addr)
    body := nonpayable ++ [ .return zeroAddr ] }

def transitions : List TransitionDecl :=
  [
        burnTransition,
        collectTransition,
        collectprotocolTransition,
        factoryTransition,
        feeTransition,
        feegrowthglobal0X128Transition,
        feegrowthglobal1X128Transition,
        flashTransition,
        increaseobservationcardinalitynextTransition,
        initializeTransition,
        liquidityTransition,
        maxliquiditypertickTransition,
        mintTransition,
        observationsTransition,
        observeTransition,
        positionsTransition,
        protocolfeesTransition,
        setfeeprotocolTransition,
        slot0Transition,
        snapshotcumulativesinsideTransition,
        swapTransition,
        tickbitmapTransition,
        tickspacingTransition,
        ticksTransition,
        token0Transition,
        token1Transition ]

def contract : ContractDecl :=
  { name := "UniswapV3Pool"
    storage := storageDecls
    ctor := constructorDecl
    structs := structs
    functions := []
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.UniswapV3Pool
