import Solm.Semantics

/-!
# Compound III Comet immutable values

`Benchmarks/CompoundIII/Comet/runtime.hex` is solc's `--bin-runtime` output: the runtime template
before the constructor patches immutable references.  In that template every immutable reference is
encoded as zero bytes.  These constants make that choice explicit in the Solm spec instead of
silently returning ad-hoc zero literals from each getter.

This is faithful to the stored runtime template bytecode.  It is not the runtime returned by a
successful arbitrary Comet constructor deployment; the constructor patches these values from
constructor arguments and external constructor calls.
-/

open Solm ABI

namespace Benchmarks.CompoundIII.Comet.Immutables

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

def addressZero : Expr := .cast (.intLit 0) (.elem .address)
def uint8Zero : Expr := .inRange uint8Int (.intLit 0)
def uint256Zero : Expr := .inRange uint256Int (.intLit 0)

def governor : Expr := addressZero
def pauseGuardian : Expr := addressZero
def baseToken : Expr := addressZero
def baseTokenPriceFeed : Expr := addressZero
def extensionDelegate : Expr := addressZero
def assetList : Expr := addressZero

def supplyKink : Expr := uint256Zero
def supplyPerSecondInterestRateSlopeLow : Expr := uint256Zero
def supplyPerSecondInterestRateSlopeHigh : Expr := uint256Zero
def supplyPerSecondInterestRateBase : Expr := uint256Zero
def borrowKink : Expr := uint256Zero
def borrowPerSecondInterestRateSlopeLow : Expr := uint256Zero
def borrowPerSecondInterestRateSlopeHigh : Expr := uint256Zero
def borrowPerSecondInterestRateBase : Expr := uint256Zero
def storeFrontPriceFactor : Expr := uint256Zero
def baseScale : Expr := uint256Zero
def trackingIndexScale : Expr := uint256Zero
def baseTrackingSupplySpeed : Expr := uint256Zero
def baseTrackingBorrowSpeed : Expr := uint256Zero
def baseMinForRewards : Expr := uint256Zero
def baseBorrowMin : Expr := uint256Zero
def targetReserves : Expr := uint256Zero
def decimals : Expr := uint8Zero
def numAssets : Expr := uint8Zero
def accrualDescaleFactor : Expr := uint256Zero

structure Entry where
  name : Ident
  value : Expr
deriving Repr, Inhabited

def runtimeTemplate : List Entry :=
  [ { name := "governor", value := governor },
    { name := "pauseGuardian", value := pauseGuardian },
    { name := "baseToken", value := baseToken },
    { name := "baseTokenPriceFeed", value := baseTokenPriceFeed },
    { name := "extensionDelegate", value := extensionDelegate },
    { name := "supplyKink", value := supplyKink },
    { name := "supplyPerSecondInterestRateSlopeLow", value := supplyPerSecondInterestRateSlopeLow },
    { name := "supplyPerSecondInterestRateSlopeHigh", value := supplyPerSecondInterestRateSlopeHigh },
    { name := "supplyPerSecondInterestRateBase", value := supplyPerSecondInterestRateBase },
    { name := "borrowKink", value := borrowKink },
    { name := "borrowPerSecondInterestRateSlopeLow", value := borrowPerSecondInterestRateSlopeLow },
    { name := "borrowPerSecondInterestRateSlopeHigh", value := borrowPerSecondInterestRateSlopeHigh },
    { name := "borrowPerSecondInterestRateBase", value := borrowPerSecondInterestRateBase },
    { name := "storeFrontPriceFactor", value := storeFrontPriceFactor },
    { name := "baseScale", value := baseScale },
    { name := "trackingIndexScale", value := trackingIndexScale },
    { name := "baseTrackingSupplySpeed", value := baseTrackingSupplySpeed },
    { name := "baseTrackingBorrowSpeed", value := baseTrackingBorrowSpeed },
    { name := "baseMinForRewards", value := baseMinForRewards },
    { name := "baseBorrowMin", value := baseBorrowMin },
    { name := "targetReserves", value := targetReserves },
    { name := "decimals", value := decimals },
    { name := "numAssets", value := numAssets },
    { name := "accrualDescaleFactor", value := accrualDescaleFactor },
    { name := "assetList", value := assetList } ]

end Benchmarks.CompoundIII.Comet.Immutables
