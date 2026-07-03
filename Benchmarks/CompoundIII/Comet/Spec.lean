import Benchmarks.CompoundIII.Comet.Immutables
import Solm.Semantics
import Solm.SolidityLayout

/-!
# Compound III CometWithExtendedAssetList benchmark spec

Solm benchmark scaffold for Compound III `CometWithExtendedAssetList` from the upstream
`compound-finance/comet` main branch.

The current runtime target is solc's unpatched runtime template.  Immutable reads are therefore
centralized through `Comet.Immutables`, whose values match that template bytecode.
-/

open Solm ABI

namespace Benchmarks.CompoundIII.Comet

/-! ## Types -/

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint16Int : IntType := .uint ⟨16, by decide⟩
def uint32Int : IntType := .uint ⟨32, by decide⟩
def uint40Int : IntType := .uint ⟨40, by decide⟩
def uint64Int : IntType := .uint ⟨64, by decide⟩
def uint104Int : IntType := .uint ⟨104, by decide⟩
def uint128Int : IntType := .uint ⟨128, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩
def int104Int : IntType := .sint ⟨104, by decide⟩
def int256Int : IntType := .sint ⟨256, by decide⟩

def uint8 : ABIType := .elem (.int uint8Int)
def uint16 : ABIType := .elem (.int uint16Int)
def uint32 : ABIType := .elem (.int uint32Int)
def uint40 : ABIType := .elem (.int uint40Int)
def uint64 : ABIType := .elem (.int uint64Int)
def uint104 : ABIType := .elem (.int uint104Int)
def uint128 : ABIType := .elem (.int uint128Int)
def uint256 : ABIType := .elem (.int uint256Int)
def int104 : ABIType := .elem (.int int104Int)
def int256 : ABIType := .elem (.int int256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytesTy : ABIType := .bytes
def stringTy : ABIType := .string

def uint8St : StorageType := .elem (.int uint8Int)
def uint16St : StorageType := .elem (.int uint16Int)
def uint32St : StorageType := .elem (.int uint32Int)
def uint40St : StorageType := .elem (.int uint40Int)
def uint64St : StorageType := .elem (.int uint64Int)
def uint104St : StorageType := .elem (.int uint104Int)
def uint128St : StorageType := .elem (.int uint128Int)
def uint256St : StorageType := .elem (.int uint256Int)
def int104St : StorageType := .elem (.int int104Int)
def int256St : StorageType := .elem (.int int256Int)
def addrSt : StorageType := .elem .address
def boolSt : StorageType := .elem .bool

def zeroAddr : Expr := .cast (.intLit 0) addrSt
def sender : Expr := .env .caller

def maxUint40 : Int := (2 : Int) ^ 40 - 1
def maxUint64 : Int := (2 : Int) ^ 64 - 1
def maxUint104 : Int := (2 : Int) ^ 104 - 1
def maxUint128 : Int := (2 : Int) ^ 128 - 1
def maxInt104 : Int := (2 : Int) ^ 103 - 1
def minInt104 : Int := -((2 : Int) ^ 103)
def baseIndexScale : Int := 1000000000000000
def factorScale : Int := 1000000000000000000

def u8 (e : Expr) : Expr := .inRange uint8Int e
def u40 (e : Expr) : Expr := .inRange uint40Int e
def u64 (e : Expr) : Expr := .inRange uint64Int e
def u104 (e : Expr) : Expr := .inRange uint104Int e
def u128 (e : Expr) : Expr := .inRange uint128Int e
def i104 (e : Expr) : Expr := .inRange int104Int e
def u256 (e : Expr) : Expr := .inRange uint256Int e

def boolToUint8 (e : Expr) : Expr :=
  .ite e (.intLit 1) (.intLit 0)

def shiftedFlag (e : Expr) (offset : Int) : Expr :=
  .binary .shl (boolToUint8 e) (.intLit offset)

def pauseFlagsValue
    (supplyPaused transferPaused withdrawPaused absorbPaused buyPaused : Expr) : Expr :=
  u8 (.binary .bitOr
    (shiftedFlag supplyPaused 0)
    (.binary .bitOr
      (shiftedFlag transferPaused 1)
      (.binary .bitOr
        (shiftedFlag withdrawPaused 2)
        (.binary .bitOr
          (shiftedFlag absorbPaused 3)
          (shiftedFlag buyPaused 4)))))

def pauseFlag (offset : Int) : Expr :=
  .binary .ne
    (.binary .bitAnd (.storage { base := "pauseFlags" }) (.binary .shl (.intLit 1) (.intLit offset)))
    (.intLit 0)

def presentValueSupplyExpr (index principal : Expr) : Expr :=
  u256 (.binary .div (u256 (.binary .mul principal index)) (.intLit baseIndexScale))

def presentValueBorrowExpr (index principal : Expr) : Expr :=
  presentValueSupplyExpr index principal

def mulFactorExpr (n factor : Expr) : Expr :=
  .binary .div (u256 (.binary .mul n factor)) (.intLit factorScale)

def borrowRateExpr (utilization : Expr) : Expr :=
  .ite (.binary .le utilization Immutables.borrowKink)
    (u256 (.binary .add Immutables.borrowPerSecondInterestRateBase
      (mulFactorExpr Immutables.borrowPerSecondInterestRateSlopeLow utilization)))
    (u256 (.binary .add
      (u256 (.binary .add Immutables.borrowPerSecondInterestRateBase
        (mulFactorExpr Immutables.borrowPerSecondInterestRateSlopeLow Immutables.borrowKink)))
      (mulFactorExpr Immutables.borrowPerSecondInterestRateSlopeHigh
        (u256 (.binary .sub utilization Immutables.borrowKink)))))

def supplyRateExpr (utilization : Expr) : Expr :=
  .ite (.binary .le utilization Immutables.supplyKink)
    (u256 (.binary .add Immutables.supplyPerSecondInterestRateBase
      (mulFactorExpr Immutables.supplyPerSecondInterestRateSlopeLow utilization)))
    (u256 (.binary .add
      (u256 (.binary .add Immutables.supplyPerSecondInterestRateBase
        (mulFactorExpr Immutables.supplyPerSecondInterestRateSlopeLow Immutables.supplyKink)))
      (mulFactorExpr Immutables.supplyPerSecondInterestRateSlopeHigh
        (u256 (.binary .sub utilization Immutables.supplyKink)))))

/-! ## Storage references -/

def baseSupplyIndexRef : StorageRef := { base := "baseSupplyIndex" }
def baseBorrowIndexRef : StorageRef := { base := "baseBorrowIndex" }
def trackingSupplyIndexRef : StorageRef := { base := "trackingSupplyIndex" }
def trackingBorrowIndexRef : StorageRef := { base := "trackingBorrowIndex" }
def totalSupplyBaseRef : StorageRef := { base := "totalSupplyBase" }
def totalBorrowBaseRef : StorageRef := { base := "totalBorrowBase" }
def lastAccrualTimeRef : StorageRef := { base := "lastAccrualTime" }
def pauseFlagsRef : StorageRef := { base := "pauseFlags" }
def totalsCollateralF (asset : Expr) (field : Ident) : StorageRef :=
  { base := "totalsCollateral", steps := [.mindex asset, .field field] }

def isAllowedRef (owner manager : Expr) : StorageRef :=
  { base := "isAllowed", steps := [.mindex owner, .mindex manager] }

def userNonceRef (account : Expr) : StorageRef :=
  { base := "userNonce", steps := [.mindex account] }

def userBasicF (account : Expr) (field : Ident) : StorageRef :=
  { base := "userBasic", steps := [.mindex account, .field field] }

def userCollateralF (account asset : Expr) (field : Ident) : StorageRef :=
  { base := "userCollateral", steps := [.mindex account, .mindex asset, .field field] }

def liquidatorPointsF (account : Expr) (field : Ident) : StorageRef :=
  { base := "liquidatorPoints", steps := [.mindex account, .field field] }

/-! ## Storage declarations and layout -/

def LiquidatorPointsStructTy : StorageType :=
  .struct "LiquidatorPoints" [("numAbsorbs", (.elem (.int uint32Int))), ("numAbsorbed", (.elem (.int uint64Int))), ("approxSpend", (.elem (.int uint128Int))), ("_reserved", (.elem (.int uint32Int)))]

def TotalsCollateralStructTy : StorageType :=
  .struct "TotalsCollateral" [("totalSupplyAsset", (.elem (.int uint128Int))), ("_reserved", (.elem (.int uint128Int)))]

def UserBasicStructTy : StorageType :=
  .struct "UserBasic" [("principal", (.elem (.int int104Int))), ("baseTrackingIndex", (.elem (.int uint64Int))), ("baseTrackingAccrued", (.elem (.int uint64Int))), ("assetsIn", (.elem (.int uint16Int))), ("_reserved", (.elem (.int uint8Int)))]

def UserCollateralStructTy : StorageType :=
  .struct "UserCollateral" [("balance", (.elem (.int uint128Int))), ("_reserved", (.elem (.int uint128Int)))]

def LiquidatorPointsStructDecl : StructDecl :=
  { name := "LiquidatorPoints"
    fields := [{ name := "numAbsorbs", ty := (.elem (.int uint32Int)) }, { name := "numAbsorbed", ty := (.elem (.int uint64Int)) }, { name := "approxSpend", ty := (.elem (.int uint128Int)) }, { name := "_reserved", ty := (.elem (.int uint32Int)) }] }

def TotalsCollateralStructDecl : StructDecl :=
  { name := "TotalsCollateral"
    fields := [{ name := "totalSupplyAsset", ty := (.elem (.int uint128Int)) }, { name := "_reserved", ty := (.elem (.int uint128Int)) }] }

def UserBasicStructDecl : StructDecl :=
  { name := "UserBasic"
    fields := [{ name := "principal", ty := (.elem (.int int104Int)) }, { name := "baseTrackingIndex", ty := (.elem (.int uint64Int)) }, { name := "baseTrackingAccrued", ty := (.elem (.int uint64Int)) }, { name := "assetsIn", ty := (.elem (.int uint16Int)) }, { name := "_reserved", ty := (.elem (.int uint8Int)) }] }

def UserCollateralStructDecl : StructDecl :=
  { name := "UserCollateral"
    fields := [{ name := "balance", ty := (.elem (.int uint128Int)) }, { name := "_reserved", ty := (.elem (.int uint128Int)) }] }

def storageDecls : List StorageDecl :=
  [
    { name := "baseSupplyIndex", ty := (.elem (.int uint64Int)) },
    { name := "baseBorrowIndex", ty := (.elem (.int uint64Int)) },
    { name := "trackingSupplyIndex", ty := (.elem (.int uint64Int)) },
    { name := "trackingBorrowIndex", ty := (.elem (.int uint64Int)) },
    { name := "totalSupplyBase", ty := (.elem (.int uint104Int)) },
    { name := "totalBorrowBase", ty := (.elem (.int uint104Int)) },
    { name := "lastAccrualTime", ty := (.elem (.int uint40Int)) },
    { name := "pauseFlags", ty := (.elem (.int uint8Int)) },
    { name := "totalsCollateral", ty := (.mapping .address TotalsCollateralStructTy) },
    { name := "isAllowed", ty := (.mapping .address (.mapping .address (.elem .bool))) },
    { name := "userNonce", ty := (.mapping .address (.elem (.int uint256Int))) },
    { name := "userBasic", ty := (.mapping .address UserBasicStructTy) },
    { name := "userCollateral", ty := (.mapping .address (.mapping .address UserCollateralStructTy)) },
    { name := "liquidatorPoints", ty := (.mapping .address LiquidatorPointsStructTy) }
  ]

def structs : List StructDecl := [LiquidatorPointsStructDecl, TotalsCollateralStructDecl, UserBasicStructDecl, UserCollateralStructDecl]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def slotAdd (slot : Ethereum.UInt256) (n : Nat) : Ethereum.UInt256 :=
  slot + Ethereum.UInt256.ofNat n

def loc (slot : Ethereum.UInt256) (offset : Fin 32) (size : Fin 33)
    (hbound : offset.val + size.val - 1 < 32) (ty : ElemType) : StorageLoc :=
  { slot := slot, offset := offset, size := size, hbound := hbound, type := ty }

def fieldLoc (slot : Ethereum.UInt256) (offset : Fin 32) (size : Fin 33)
    (hbound : offset.val + size.val - 1 < 32) (ty : ElemType) : StorageLoc :=
  loc slot offset size hbound ty

def totalsCollateralSlot (asset : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord asset) ⟨2⟩

def isAllowedOwnerSlot (owner : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord owner) ⟨3⟩

def isAllowedSlot (owner manager : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord manager) (isAllowedOwnerSlot owner)

def userNonceSlot (account : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord account) ⟨4⟩

def userBasicSlot (account : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord account) ⟨5⟩

def userCollateralAccountSlot (account : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord account) ⟨6⟩

def userCollateralSlot (account asset : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord asset) (userCollateralAccountSlot account)

def liquidatorPointsSlot (account : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord account) ⟨7⟩

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "baseSupplyIndex", steps := [] }, _ =>
      some (fieldLoc ⟨0⟩ 0 8 (by decide) (.int uint64Int))
  | { base := "baseBorrowIndex", steps := [] }, _ =>
      some (fieldLoc ⟨0⟩ 8 8 (by decide) (.int uint64Int))
  | { base := "trackingSupplyIndex", steps := [] }, _ =>
      some (fieldLoc ⟨0⟩ 16 8 (by decide) (.int uint64Int))
  | { base := "trackingBorrowIndex", steps := [] }, _ =>
      some (fieldLoc ⟨0⟩ 24 8 (by decide) (.int uint64Int))
  | { base := "totalSupplyBase", steps := [] }, _ =>
      some (fieldLoc ⟨1⟩ 0 13 (by decide) (.int uint104Int))
  | { base := "totalBorrowBase", steps := [] }, _ =>
      some (fieldLoc ⟨1⟩ 13 13 (by decide) (.int uint104Int))
  | { base := "lastAccrualTime", steps := [] }, _ =>
      some (fieldLoc ⟨1⟩ 26 5 (by decide) (.int uint40Int))
  | { base := "pauseFlags", steps := [] }, _ =>
      some (fieldLoc ⟨1⟩ 31 1 (by decide) (.int uint8Int))
  | { base := "totalsCollateral", steps := [.mindex asset, .field "totalSupplyAsset"] }, _ =>
      some (fieldLoc (slotAdd (totalsCollateralSlot asset) 0) 0 16 (by decide) (.int uint128Int))
  | { base := "totalsCollateral", steps := [.mindex asset, .field "_reserved"] }, _ =>
      some (fieldLoc (slotAdd (totalsCollateralSlot asset) 0) 16 16 (by decide) (.int uint128Int))
  | { base := "userBasic", steps := [.mindex account, .field "principal"] }, _ =>
      some (fieldLoc (slotAdd (userBasicSlot account) 0) 0 13 (by decide) (.int int104Int))
  | { base := "userBasic", steps := [.mindex account, .field "baseTrackingIndex"] }, _ =>
      some (fieldLoc (slotAdd (userBasicSlot account) 0) 13 8 (by decide) (.int uint64Int))
  | { base := "userBasic", steps := [.mindex account, .field "baseTrackingAccrued"] }, _ =>
      some (fieldLoc (slotAdd (userBasicSlot account) 0) 21 8 (by decide) (.int uint64Int))
  | { base := "userBasic", steps := [.mindex account, .field "assetsIn"] }, _ =>
      some (fieldLoc (slotAdd (userBasicSlot account) 0) 29 2 (by decide) (.int uint16Int))
  | { base := "userBasic", steps := [.mindex account, .field "_reserved"] }, _ =>
      some (fieldLoc (slotAdd (userBasicSlot account) 0) 31 1 (by decide) (.int uint8Int))
  | { base := "userCollateral", steps := [.mindex account, .mindex asset, .field "balance"] }, _ =>
      some (fieldLoc (slotAdd (userCollateralSlot account asset) 0) 0 16 (by decide) (.int uint128Int))
  | { base := "userCollateral", steps := [.mindex account, .mindex asset, .field "_reserved"] }, _ =>
      some (fieldLoc (slotAdd (userCollateralSlot account asset) 0) 16 16 (by decide) (.int uint128Int))
  | { base := "liquidatorPoints", steps := [.mindex account, .field "numAbsorbs"] }, _ =>
      some (fieldLoc (slotAdd (liquidatorPointsSlot account) 0) 0 4 (by decide) (.int uint32Int))
  | { base := "liquidatorPoints", steps := [.mindex account, .field "numAbsorbed"] }, _ =>
      some (fieldLoc (slotAdd (liquidatorPointsSlot account) 0) 4 8 (by decide) (.int uint64Int))
  | { base := "liquidatorPoints", steps := [.mindex account, .field "approxSpend"] }, _ =>
      some (fieldLoc (slotAdd (liquidatorPointsSlot account) 0) 12 16 (by decide) (.int uint128Int))
  | { base := "liquidatorPoints", steps := [.mindex account, .field "_reserved"] }, _ =>
      some (fieldLoc (slotAdd (liquidatorPointsSlot account) 0) 28 4 (by decide) (.int uint32Int))
  | { base := "isAllowed", steps := [.mindex owner, .mindex manager] }, _ =>
      some (fieldLoc (isAllowedSlot owner manager) 0 1 (by decide) .bool)
  | { base := "userNonce", steps := [.mindex account] }, _ =>
      some (fieldLoc (userNonceSlot account) 0 32 (by decide) (.int uint256Int))
  | _, _ => none

def storageLayout : StorageLayout :=
  solidityStorageLayout storageLayoutRaw

/-! ## Shared source patterns -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "config", ty := (.tuple [addr, addr, addr, addr, addr, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint104, uint104, uint104, (.dynamicArray (.tuple [addr, addr, uint8, uint64, uint64, uint64, uint128]))]) }]
    body := nonpayable }

/-! ## Public ABI surface -/

def absorbTransition : TransitionDecl :=
  { name := "absorb"
    params := [{ name := "absorber", ty := addr }, { name := "accounts", ty := (.dynamicArray addr) }]
    returnType := []
    body := nonpayable }

def accrueAccountTransition : TransitionDecl :=
  { name := "accrueAccount"
    params := [{ name := "account", ty := addr }]
    returnType := []
    body := nonpayable }

def approveThisTransition : TransitionDecl :=
  { name := "approveThis"
    params := [{ name := "manager", ty := addr }, { name := "asset", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := []
    body := nonpayable }

def assetListTransition : TransitionDecl :=
  { name := "assetList"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [Immutables.assetList] ] }

def balanceOfTransition : TransitionDecl :=
  { name := "balanceOf"
    params := [{ name := "account", ty := addr }]
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .letDecl "principal" (some int104)
          (.storage (userBasicF (.var "account") "principal")),
        .return
          [ .ite (.binary .gt (.var "principal") (.intLit 0))
              (presentValueSupplyExpr (.storage baseSupplyIndexRef) (.var "principal"))
              (.intLit 0) ] ] }

def baseBorrowMinTransition : TransitionDecl :=
  { name := "baseBorrowMin"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.baseBorrowMin] ] }

def baseMinForRewardsTransition : TransitionDecl :=
  { name := "baseMinForRewards"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.baseMinForRewards] ] }

def baseScaleTransition : TransitionDecl :=
  { name := "baseScale"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.baseScale] ] }

def baseTokenTransition : TransitionDecl :=
  { name := "baseToken"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [Immutables.baseToken] ] }

def baseTokenPriceFeedTransition : TransitionDecl :=
  { name := "baseTokenPriceFeed"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [Immutables.baseTokenPriceFeed] ] }

def baseTrackingBorrowSpeedTransition : TransitionDecl :=
  { name := "baseTrackingBorrowSpeed"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.baseTrackingBorrowSpeed] ] }

def baseTrackingSupplySpeedTransition : TransitionDecl :=
  { name := "baseTrackingSupplySpeed"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.baseTrackingSupplySpeed] ] }

def borrowBalanceOfTransition : TransitionDecl :=
  { name := "borrowBalanceOf"
    params := [{ name := "account", ty := addr }]
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .letDecl "principal" (some int104)
          (.storage (userBasicF (.var "account") "principal")),
        .return
          [ .ite (.binary .lt (.var "principal") (.intLit 0))
              (presentValueBorrowExpr (.storage baseBorrowIndexRef)
                (u104 (.unary .neg (.var "principal"))))
              (.intLit 0) ] ] }

def borrowKinkTransition : TransitionDecl :=
  { name := "borrowKink"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.borrowKink] ] }

def borrowPerSecondInterestRateBaseTransition : TransitionDecl :=
  { name := "borrowPerSecondInterestRateBase"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.borrowPerSecondInterestRateBase] ] }

def borrowPerSecondInterestRateSlopeHighTransition : TransitionDecl :=
  { name := "borrowPerSecondInterestRateSlopeHigh"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.borrowPerSecondInterestRateSlopeHigh] ] }

def borrowPerSecondInterestRateSlopeLowTransition : TransitionDecl :=
  { name := "borrowPerSecondInterestRateSlopeLow"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.borrowPerSecondInterestRateSlopeLow] ] }

def buyCollateralTransition : TransitionDecl :=
  { name := "buyCollateral"
    params := [{ name := "asset", ty := addr }, { name := "minAmount", ty := uint256 }, { name := "baseAmount", ty := uint256 }, { name := "recipient", ty := addr }]
    returnType := []
    body := nonpayable }

def decimalsTransition : TransitionDecl :=
  { name := "decimals"
    params := []
    returnType := [uint8]
    body := nonpayable ++ [ .return [Immutables.decimals] ] }

def extensionDelegateTransition : TransitionDecl :=
  { name := "extensionDelegate"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [Immutables.extensionDelegate] ] }

def getAssetInfoTransition : TransitionDecl :=
  { name := "getAssetInfo"
    params := [{ name := "i", ty := uint8 }]
    returnType := [(.tuple [uint8, addr, addr, uint64, uint64, uint64, uint64, uint128])]
    body := nonpayable ++ [ .return [(.tupleLit [(.intLit 0), zeroAddr, zeroAddr, (.intLit 0), (.intLit 0), (.intLit 0), (.intLit 0), (.intLit 0)])] ] }

def getAssetInfoByAddressTransition : TransitionDecl :=
  { name := "getAssetInfoByAddress"
    params := [{ name := "asset", ty := addr }]
    returnType := [(.tuple [uint8, addr, addr, uint64, uint64, uint64, uint64, uint128])]
    body := nonpayable ++ [ .return [(.tupleLit [(.intLit 0), zeroAddr, zeroAddr, (.intLit 0), (.intLit 0), (.intLit 0), (.intLit 0), (.intLit 0)])] ] }

def getBorrowRateTransition : TransitionDecl :=
  { name := "getBorrowRate"
    params := [{ name := "utilization", ty := uint256 }]
    returnType := [uint64]
    body := nonpayable ++ [ .return [u64 (borrowRateExpr (.var "utilization"))] ] }

def getCollateralReservesTransition : TransitionDecl :=
  { name := "getCollateralReserves"
    params := [{ name := "asset", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [(.intLit 0)] ] }

def getPriceTransition : TransitionDecl :=
  { name := "getPrice"
    params := [{ name := "priceFeed", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [(.intLit 0)] ] }

def getReservesTransition : TransitionDecl :=
  { name := "getReserves"
    params := []
    returnType := [int256]
    body := nonpayable ++ [ .return [(.intLit 0)] ] }

def getSupplyRateTransition : TransitionDecl :=
  { name := "getSupplyRate"
    params := [{ name := "utilization", ty := uint256 }]
    returnType := [uint64]
    body := nonpayable ++ [ .return [u64 (supplyRateExpr (.var "utilization"))] ] }

def getUtilizationTransition : TransitionDecl :=
  { name := "getUtilization"
    params := []
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .letDecl "totalSupply_" (some uint256)
          (presentValueSupplyExpr (.storage baseSupplyIndexRef) (.storage totalSupplyBaseRef)),
        .letDecl "totalBorrow_" (some uint256)
          (presentValueBorrowExpr (.storage baseBorrowIndexRef) (.storage totalBorrowBaseRef)),
        .return
          [ .ite (.binary .eq (.var "totalSupply_") (.intLit 0))
              (.intLit 0)
              (.binary .div
                (u256 (.binary .mul (.var "totalBorrow_") (.intLit factorScale)))
                (.var "totalSupply_")) ] ] }

def governorTransition : TransitionDecl :=
  { name := "governor"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [Immutables.governor] ] }

def hasPermissionTransition : TransitionDecl :=
  { name := "hasPermission"
    params := [{ name := "owner", ty := addr }, { name := "manager", ty := addr }]
    returnType := [boolTy]
    body :=
      nonpayable ++
      [ .return
          [ .binary .or
              (.binary .eq (.var "owner") (.var "manager"))
              (.storage (isAllowedRef (.var "owner") (.var "manager"))) ] ] }

def initializeStorageTransition : TransitionDecl :=
  { name := "initializeStorage"
    params := []
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .eq (.storage lastAccrualTimeRef) (.intLit 0)),
        .require (.binary .le (.env .timestamp) (.intLit maxUint40)),
        .assign .storage lastAccrualTimeRef (u40 (.env .timestamp)),
        .assign .storage baseSupplyIndexRef (.intLit baseIndexScale),
        .assign .storage baseBorrowIndexRef (.intLit baseIndexScale) ] }

def isAbsorbPausedTransition : TransitionDecl :=
  { name := "isAbsorbPaused"
    params := []
    returnType := [boolTy]
    body := nonpayable ++ [ .return [pauseFlag 3] ] }

def isAllowedTransition : TransitionDecl :=
  { name := "isAllowed"
    params := [{ name := "arg0", ty := addr }, { name := "arg1", ty := addr }]
    returnType := [boolTy]
    body := nonpayable ++ [ .return [.storage (isAllowedRef (.var "arg0") (.var "arg1"))] ] }

def isBorrowCollateralizedTransition : TransitionDecl :=
  { name := "isBorrowCollateralized"
    params := [{ name := "account", ty := addr }]
    returnType := [boolTy]
    body := nonpayable ++ [ .return [(.boolLit false)] ] }

def isBuyPausedTransition : TransitionDecl :=
  { name := "isBuyPaused"
    params := []
    returnType := [boolTy]
    body := nonpayable ++ [ .return [pauseFlag 4] ] }

def isLiquidatableTransition : TransitionDecl :=
  { name := "isLiquidatable"
    params := [{ name := "account", ty := addr }]
    returnType := [boolTy]
    body := nonpayable ++ [ .return [(.boolLit false)] ] }

def isSupplyPausedTransition : TransitionDecl :=
  { name := "isSupplyPaused"
    params := []
    returnType := [boolTy]
    body := nonpayable ++ [ .return [pauseFlag 0] ] }

def isTransferPausedTransition : TransitionDecl :=
  { name := "isTransferPaused"
    params := []
    returnType := [boolTy]
    body := nonpayable ++ [ .return [pauseFlag 1] ] }

def isWithdrawPausedTransition : TransitionDecl :=
  { name := "isWithdrawPaused"
    params := []
    returnType := [boolTy]
    body := nonpayable ++ [ .return [pauseFlag 2] ] }

def liquidatorPointsTransition : TransitionDecl :=
  { name := "liquidatorPoints"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint32, uint64, uint128, uint32]
    body := nonpayable ++ [ .return [.storage (liquidatorPointsF (.var "arg0") "numAbsorbs"), .storage (liquidatorPointsF (.var "arg0") "numAbsorbed"), .storage (liquidatorPointsF (.var "arg0") "approxSpend"), .storage (liquidatorPointsF (.var "arg0") "_reserved")] ] }

def numAssetsTransition : TransitionDecl :=
  { name := "numAssets"
    params := []
    returnType := [uint8]
    body := nonpayable ++ [ .return [Immutables.numAssets] ] }

def pauseTransition : TransitionDecl :=
  { name := "pause"
    params := [{ name := "supplyPaused", ty := boolTy }, { name := "transferPaused", ty := boolTy }, { name := "withdrawPaused", ty := boolTy }, { name := "absorbPaused", ty := boolTy }, { name := "buyPaused", ty := boolTy }]
    returnType := []
    body :=
      nonpayable ++
      [ .require
          (.binary .or
            (.binary .eq sender Immutables.governor)
            (.binary .eq sender Immutables.pauseGuardian)),
        .assign .storage pauseFlagsRef
          (pauseFlagsValue (.var "supplyPaused") (.var "transferPaused")
            (.var "withdrawPaused") (.var "absorbPaused") (.var "buyPaused")) ] }

def pauseGuardianTransition : TransitionDecl :=
  { name := "pauseGuardian"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [Immutables.pauseGuardian] ] }

def quoteCollateralTransition : TransitionDecl :=
  { name := "quoteCollateral"
    params := [{ name := "asset", ty := addr }, { name := "baseAmount", ty := uint256 }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [(.intLit 0)] ] }

def storeFrontPriceFactorTransition : TransitionDecl :=
  { name := "storeFrontPriceFactor"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.storeFrontPriceFactor] ] }

def supplyTransition : TransitionDecl :=
  { name := "supply"
    params := [{ name := "asset", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := []
    body := nonpayable }

def supplyFromTransition : TransitionDecl :=
  { name := "supplyFrom"
    params := [{ name := "from", ty := addr }, { name := "dst", ty := addr }, { name := "asset", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := []
    body := nonpayable }

def supplyKinkTransition : TransitionDecl :=
  { name := "supplyKink"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.supplyKink] ] }

def supplyPerSecondInterestRateBaseTransition : TransitionDecl :=
  { name := "supplyPerSecondInterestRateBase"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.supplyPerSecondInterestRateBase] ] }

def supplyPerSecondInterestRateSlopeHighTransition : TransitionDecl :=
  { name := "supplyPerSecondInterestRateSlopeHigh"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.supplyPerSecondInterestRateSlopeHigh] ] }

def supplyPerSecondInterestRateSlopeLowTransition : TransitionDecl :=
  { name := "supplyPerSecondInterestRateSlopeLow"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.supplyPerSecondInterestRateSlopeLow] ] }

def supplyToTransition : TransitionDecl :=
  { name := "supplyTo"
    params := [{ name := "dst", ty := addr }, { name := "asset", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := []
    body := nonpayable }

def targetReservesTransition : TransitionDecl :=
  { name := "targetReserves"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.targetReserves] ] }

def totalBorrowTransition : TransitionDecl :=
  { name := "totalBorrow"
    params := []
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .return
          [ presentValueBorrowExpr (.storage baseBorrowIndexRef) (.storage totalBorrowBaseRef) ] ] }

def totalSupplyTransition : TransitionDecl :=
  { name := "totalSupply"
    params := []
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .return
          [ presentValueSupplyExpr (.storage baseSupplyIndexRef) (.storage totalSupplyBaseRef) ] ] }

def totalsCollateralTransition : TransitionDecl :=
  { name := "totalsCollateral"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint128, uint128]
    body := nonpayable ++ [ .return [.storage (totalsCollateralF (.var "arg0") "totalSupplyAsset"), .storage (totalsCollateralF (.var "arg0") "_reserved")] ] }

def trackingIndexScaleTransition : TransitionDecl :=
  { name := "trackingIndexScale"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [Immutables.trackingIndexScale] ] }

def transferTransition : TransitionDecl :=
  { name := "transfer"
    params := [{ name := "dst", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := [boolTy]
    body := nonpayable ++ [ .return [(.boolLit false)] ] }

def transferAssetTransition : TransitionDecl :=
  { name := "transferAsset"
    params := [{ name := "dst", ty := addr }, { name := "asset", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := []
    body := nonpayable }

def transferAssetFromTransition : TransitionDecl :=
  { name := "transferAssetFrom"
    params := [{ name := "src", ty := addr }, { name := "dst", ty := addr }, { name := "asset", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := []
    body := nonpayable }

def transferFromTransition : TransitionDecl :=
  { name := "transferFrom"
    params := [{ name := "src", ty := addr }, { name := "dst", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := [boolTy]
    body := nonpayable ++ [ .return [(.boolLit false)] ] }

def userBasicTransition : TransitionDecl :=
  { name := "userBasic"
    params := [{ name := "arg0", ty := addr }]
    returnType := [int104, uint64, uint64, uint16, uint8]
    body := nonpayable ++ [ .return [.storage (userBasicF (.var "arg0") "principal"), .storage (userBasicF (.var "arg0") "baseTrackingIndex"), .storage (userBasicF (.var "arg0") "baseTrackingAccrued"), .storage (userBasicF (.var "arg0") "assetsIn"), .storage (userBasicF (.var "arg0") "_reserved")] ] }

def userCollateralTransition : TransitionDecl :=
  { name := "userCollateral"
    params := [{ name := "arg0", ty := addr }, { name := "arg1", ty := addr }]
    returnType := [uint128, uint128]
    body := nonpayable ++ [ .return [.storage (userCollateralF (.var "arg0") (.var "arg1") "balance"), .storage (userCollateralF (.var "arg0") (.var "arg1") "_reserved")] ] }

def userNonceTransition : TransitionDecl :=
  { name := "userNonce"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (userNonceRef (.var "arg0"))] ] }

def withdrawTransition : TransitionDecl :=
  { name := "withdraw"
    params := [{ name := "asset", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := []
    body := nonpayable }

def withdrawFromTransition : TransitionDecl :=
  { name := "withdrawFrom"
    params := [{ name := "src", ty := addr }, { name := "to", ty := addr }, { name := "asset", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := []
    body := nonpayable }

def withdrawReservesTransition : TransitionDecl :=
  { name := "withdrawReserves"
    params := [{ name := "to", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := []
    body := nonpayable }

def withdrawToTransition : TransitionDecl :=
  { name := "withdrawTo"
    params := [{ name := "to", ty := addr }, { name := "asset", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := []
    body := nonpayable }

def fallbackTransition : TransitionDecl :=
  { name := "fallback"
    params := [{ name := "calldata", ty := bytesTy }]
    returnType := [bytesTy]
    body :=
      [ .delegateCall Immutables.extensionDelegate (.var "calldata") "ok" "returndata",
        .require (.var "ok"),
        .return [.var "returndata"] ] }

def transitions : List TransitionDecl :=
  [ absorbTransition,
    accrueAccountTransition,
    approveThisTransition,
    assetListTransition,
    balanceOfTransition,
    baseBorrowMinTransition,
    baseMinForRewardsTransition,
    baseScaleTransition,
    baseTokenTransition,
    baseTokenPriceFeedTransition,
    baseTrackingBorrowSpeedTransition,
    baseTrackingSupplySpeedTransition,
    borrowBalanceOfTransition,
    borrowKinkTransition,
    borrowPerSecondInterestRateBaseTransition,
    borrowPerSecondInterestRateSlopeHighTransition,
    borrowPerSecondInterestRateSlopeLowTransition,
    buyCollateralTransition,
    decimalsTransition,
    extensionDelegateTransition,
    getAssetInfoTransition,
    getAssetInfoByAddressTransition,
    getBorrowRateTransition,
    getCollateralReservesTransition,
    getPriceTransition,
    getReservesTransition,
    getSupplyRateTransition,
    getUtilizationTransition,
    governorTransition,
    hasPermissionTransition,
    initializeStorageTransition,
    isAbsorbPausedTransition,
    isAllowedTransition,
    isBorrowCollateralizedTransition,
    isBuyPausedTransition,
    isLiquidatableTransition,
    isSupplyPausedTransition,
    isTransferPausedTransition,
    isWithdrawPausedTransition,
    liquidatorPointsTransition,
    numAssetsTransition,
    pauseTransition,
    pauseGuardianTransition,
    quoteCollateralTransition,
    storeFrontPriceFactorTransition,
    supplyTransition,
    supplyFromTransition,
    supplyKinkTransition,
    supplyPerSecondInterestRateBaseTransition,
    supplyPerSecondInterestRateSlopeHighTransition,
    supplyPerSecondInterestRateSlopeLowTransition,
    supplyToTransition,
    targetReservesTransition,
    totalBorrowTransition,
    totalSupplyTransition,
    totalsCollateralTransition,
    trackingIndexScaleTransition,
    transferTransition,
    transferAssetTransition,
    transferAssetFromTransition,
    transferFromTransition,
    userBasicTransition,
    userCollateralTransition,
    userNonceTransition,
    withdrawTransition,
    withdrawFromTransition,
    withdrawReservesTransition,
    withdrawToTransition ]

def contract : ContractDecl :=
  { name := "CometWithExtendedAssetList"
    storage := storageDecls
    ctor := constructorDecl
    structs := structs
    functions := []
    transitions := transitions
    fallback := some fallbackTransition }

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.CompoundIII.Comet
