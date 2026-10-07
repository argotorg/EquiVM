import Reasoning.SolmBody
import Reasoning.BytecodePatching
import Solm
import Reasoning.Immutables

/-!
# Compound III Comet immutable values, offset table, and `runtimeCodeOf`

`runtime.hex` is solc's `--via-ir --optimize --optimize-runs 1 --metadata-hash none` runtime
*template* (immutables zeroed).  Offsets re-derived and verified this session (solc 0.8.15):
the emitted template equals `runtime.hex` byte-for-byte and the 25 `immutableReferences` map to
the immutable declarations below (astId→name via the AST).  Convention: the constructor binds
each immutable as `imm_<name>`; `runtimeCodeOf` reads those locals, `valueToWord`s and splices.
-/

open Solm ABI

namespace Benchmarks.CompoundIII.Comet.Immutables

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

/-- Comet's 25 constructor-set immutables. -/
structure CometImmutables where
  governor : EVM.Address
  pauseGuardian : EVM.Address
  baseToken : EVM.Address
  baseTokenPriceFeed : EVM.Address
  extensionDelegate : EVM.Address
  supplyKink : Int
  supplyPerSecondInterestRateSlopeLow : Int
  supplyPerSecondInterestRateSlopeHigh : Int
  supplyPerSecondInterestRateBase : Int
  borrowKink : Int
  borrowPerSecondInterestRateSlopeLow : Int
  borrowPerSecondInterestRateSlopeHigh : Int
  borrowPerSecondInterestRateBase : Int
  storeFrontPriceFactor : Int
  baseScale : Int
  trackingIndexScale : Int
  baseTrackingSupplySpeed : Int
  baseTrackingBorrowSpeed : Int
  baseMinForRewards : Int
  baseBorrowMin : Int
  targetReserves : Int
  decimals : Int
  numAssets : Int
  accrualDescaleFactor : Int
  assetList : EVM.Address


variable (v : CometImmutables)

-- Each immutable as an `Expr` returning its value (getters + internal rate computations).
def governor : Expr := Reasoning.Theory.addressLiteral v.governor
def pauseGuardian : Expr := Reasoning.Theory.addressLiteral v.pauseGuardian
def baseToken : Expr := Reasoning.Theory.addressLiteral v.baseToken
def baseTokenPriceFeed : Expr := Reasoning.Theory.addressLiteral v.baseTokenPriceFeed
def extensionDelegate : Expr := Reasoning.Theory.addressLiteral v.extensionDelegate
def supplyKink : Expr := .intLit v.supplyKink
def supplyPerSecondInterestRateSlopeLow : Expr := .intLit v.supplyPerSecondInterestRateSlopeLow
def supplyPerSecondInterestRateSlopeHigh : Expr := .intLit v.supplyPerSecondInterestRateSlopeHigh
def supplyPerSecondInterestRateBase : Expr := .intLit v.supplyPerSecondInterestRateBase
def borrowKink : Expr := .intLit v.borrowKink
def borrowPerSecondInterestRateSlopeLow : Expr := .intLit v.borrowPerSecondInterestRateSlopeLow
def borrowPerSecondInterestRateSlopeHigh : Expr := .intLit v.borrowPerSecondInterestRateSlopeHigh
def borrowPerSecondInterestRateBase : Expr := .intLit v.borrowPerSecondInterestRateBase
def storeFrontPriceFactor : Expr := .intLit v.storeFrontPriceFactor
def baseScale : Expr := .intLit v.baseScale
def trackingIndexScale : Expr := .intLit v.trackingIndexScale
def baseTrackingSupplySpeed : Expr := .intLit v.baseTrackingSupplySpeed
def baseTrackingBorrowSpeed : Expr := .intLit v.baseTrackingBorrowSpeed
def baseMinForRewards : Expr := .intLit v.baseMinForRewards
def baseBorrowMin : Expr := .intLit v.baseBorrowMin
def targetReserves : Expr := .intLit v.targetReserves
def decimals : Expr := .intLit v.decimals
def numAssets : Expr := .intLit v.numAssets
def accrualDescaleFactor : Expr := .intLit v.accrualDescaleFactor
def assetList : Expr := Reasoning.Theory.addressLiteral v.assetList

/-- solc `immutableReferences` offsets, keyed by `imm_<name>` (verified against the AST). -/
def offsets : List (Ident × List Nat) :=
  [ ("imm_governor", [1592, 3441, 5137, 6161]),
    ("imm_pauseGuardian", [2168, 3703]),
    ("imm_baseToken", [2078, 5008, 5625, 6266, 6450, 9907, 12117, 12429, 14552, 15644, 15869]),
    ("imm_baseTokenPriceFeed", [6768, 10264, 17068, 18119]),
    ("imm_extensionDelegate", [3767, 18431]),
    ("imm_supplyKink", [4926, 8616]),
    ("imm_supplyPerSecondInterestRateSlopeLow", [3925, 8676, 8782]),
    ("imm_supplyPerSecondInterestRateSlopeHigh", [4196, 8830]),
    ("imm_supplyPerSecondInterestRateBase", [4550, 8715]),
    ("imm_borrowKink", [4430, 8888]),
    ("imm_borrowPerSecondInterestRateSlopeLow", [2599, 8948, 9054]),
    ("imm_borrowPerSecondInterestRateSlopeHigh", [2353, 9102]),
    ("imm_borrowPerSecondInterestRateBase", [4064, 8987]),
    ("imm_storeFrontPriceFactor", [1966, 18059]),
    ("imm_baseScale", [3313, 10302, 11157, 17180, 18175]),
    ("imm_trackingIndexScale", [5072, 11824]),
    ("imm_baseTrackingSupplySpeed", [1772, 8308]),
    ("imm_baseTrackingBorrowSpeed", [4610, 8188]),
    ("imm_baseMinForRewards", [4490, 8046]),
    ("imm_baseBorrowMin", [2721, 15134, 16028]),
    ("imm_targetReserves", [2844, 6688]),
    ("imm_decimals", [2783]),
    ("imm_numAssets", [4865, 7501, 10357, 10878, 17114]),
    ("imm_accrualDescaleFactor", [11863]),
    ("imm_assetList", [6070, 7222]) ]

/-- The constructor's immutable offsets as a layout for generated runtime summaries. -/
def immutableLayout : Reasoning.Immutables.Layout :=
  ⟨offsets.flatMap fun (key, sites) => sites.map fun off => (off, 32, key)⟩

/-- The immutable values as `Value`s under their `imm_<name>` keys. -/
def immValues (v : CometImmutables) : List (Ident × Value) :=
  [ ("imm_governor", .address v.governor),
    ("imm_pauseGuardian", .address v.pauseGuardian),
    ("imm_baseToken", .address v.baseToken),
    ("imm_baseTokenPriceFeed", .address v.baseTokenPriceFeed),
    ("imm_extensionDelegate", .address v.extensionDelegate),
    ("imm_supplyKink", .int v.supplyKink),
    ("imm_supplyPerSecondInterestRateSlopeLow", .int v.supplyPerSecondInterestRateSlopeLow),
    ("imm_supplyPerSecondInterestRateSlopeHigh", .int v.supplyPerSecondInterestRateSlopeHigh),
    ("imm_supplyPerSecondInterestRateBase", .int v.supplyPerSecondInterestRateBase),
    ("imm_borrowKink", .int v.borrowKink),
    ("imm_borrowPerSecondInterestRateSlopeLow", .int v.borrowPerSecondInterestRateSlopeLow),
    ("imm_borrowPerSecondInterestRateSlopeHigh", .int v.borrowPerSecondInterestRateSlopeHigh),
    ("imm_borrowPerSecondInterestRateBase", .int v.borrowPerSecondInterestRateBase),
    ("imm_storeFrontPriceFactor", .int v.storeFrontPriceFactor),
    ("imm_baseScale", .int v.baseScale),
    ("imm_trackingIndexScale", .int v.trackingIndexScale),
    ("imm_baseTrackingSupplySpeed", .int v.baseTrackingSupplySpeed),
    ("imm_baseTrackingBorrowSpeed", .int v.baseTrackingBorrowSpeed),
    ("imm_baseMinForRewards", .int v.baseMinForRewards),
    ("imm_baseBorrowMin", .int v.baseBorrowMin),
    ("imm_targetReserves", .int v.targetReserves),
    ("imm_decimals", .int v.decimals),
    ("imm_numAssets", .int v.numAssets),
    ("imm_accrualDescaleFactor", .int v.accrualDescaleFactor),
    ("imm_assetList", .address v.assetList) ]


def patchesFrom (get : Ident → Option Value) : Option (List (Nat × ByteArray)) :=
  offsets.foldrM (fun p acc => do
    let x ← get p.1
    let bytes ← Reasoning.Theory.wordBytes? x
    pure (p.2.map (fun o => (o, bytes)) ++ acc)) []

def patches (v : CometImmutables) : List (Nat × ByteArray) :=
  (patchesFrom (fun n => (immValues v).lookup n)).getD []

/-- `runtimeCodeOf` for the parameterized constructor relation. -/
def runtimeCodeOf (template : ByteArray) (locals : Store) : Option ByteArray := do
  let ps ← patchesFrom (fun n => locals.get? n)
  patchRuntime template ps

end Benchmarks.CompoundIII.Comet.Immutables
