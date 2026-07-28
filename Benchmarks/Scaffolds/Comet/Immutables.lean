import Solm

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

/-- An address value as an `Expr` literal. -/
def addrLit (a : EVM.Address) : Expr := .cast (.intLit (Int.ofNat a.toNat)) (.elem .address)

variable (v : CometImmutables)

-- Each immutable as an `Expr` returning its value (getters + internal rate computations).
def governor : Expr := addrLit v.governor
def pauseGuardian : Expr := addrLit v.pauseGuardian
def baseToken : Expr := addrLit v.baseToken
def baseTokenPriceFeed : Expr := addrLit v.baseTokenPriceFeed
def extensionDelegate : Expr := addrLit v.extensionDelegate
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
def assetList : Expr := addrLit v.assetList

/-- solc `immutableReferences` offsets, keyed by `imm_<name>` (verified against the AST). -/
def offsets : List (Ident × List Nat) :=
  [ ("imm_governor", [1592, 3562, 5300, 6314]),
    ("imm_pauseGuardian", [2139, 3872]),
    ("imm_baseToken", [2049, 5173, 5780, 6419, 6603, 10047, 12073, 12352, 14120, 15216, 15439]),
    ("imm_baseTokenPriceFeed", [6921, 10363, 16597, 17562]),
    ("imm_extensionDelegate", [3936, 17874]),
    ("imm_supplyKink", [5091, 8793]),
    ("imm_supplyPerSecondInterestRateSlopeLow", [4094, 8853, 8959]),
    ("imm_supplyPerSecondInterestRateSlopeHigh", [4365, 9007]),
    ("imm_supplyPerSecondInterestRateBase", [4717, 8892]),
    ("imm_borrowKink", [4597, 9065]),
    ("imm_borrowPerSecondInterestRateSlopeLow", [2672, 9125, 9231]),
    ("imm_borrowPerSecondInterestRateSlopeHigh", [2324, 9279]),
    ("imm_borrowPerSecondInterestRateBase", [4233, 9164]),
    ("imm_storeFrontPriceFactor", [1940, 17502]),
    ("imm_baseScale", [3382, 10401, 11062, 16709, 17618]),
    ("imm_trackingIndexScale", [5237, 11787]),
    ("imm_baseTrackingSupplySpeed", [1772, 8517]),
    ("imm_baseTrackingBorrowSpeed", [4777, 8392]),
    ("imm_baseMinForRewards", [4657, 8286]),
    ("imm_baseBorrowMin", [2794, 14711, 15598]),
    ("imm_targetReserves", [2917, 6841]),
    ("imm_decimals", [2856]),
    ("imm_numAssets", [5030, 7705, 10456, 10797, 16643]),
    ("imm_accrualDescaleFactor", [11826]),
    ("imm_assetList", [6223, 7424]) ]

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

def wordBytes? (x : Value) : Option ByteArray :=
  (valueToWord x).map (fun w => ByteArray.mk (EVM.Word.toBytesBE w).toArray)

def patchesFrom (get : Ident → Option Value) : Option (List (Nat × ByteArray)) :=
  offsets.foldrM (fun p acc => do
    let x ← get p.1
    let bytes ← wordBytes? x
    pure (p.2.map (fun o => (o, bytes)) ++ acc)) []

def patches (v : CometImmutables) : List (Nat × ByteArray) :=
  (patchesFrom (fun n => (immValues v).lookup n)).getD []

/-- `runtimeCodeOf` for the parameterized constructor relation. -/
def runtimeCodeOf (template : ByteArray) (locals : Store) : Option ByteArray := do
  let ps ← patchesFrom (fun n => locals.get? n)
  patchRuntime template ps

end Benchmarks.CompoundIII.Comet.Immutables
