import Reasoning.SolmBody
import Reasoning.BytecodePatching
import Solm
import Reasoning.PatchRuntime
import Reasoning.Immutables

/-!
# Compound III Comet immutable values and offset table

`runtime.hex` is solc's `--via-ir --optimize --optimize-runs 1 --metadata-hash none` runtime
*template* (immutables zeroed).  Offsets re-derived and verified this session (solc 0.8.15):
the emitted template equals `runtime.hex` byte-for-byte and the 25 `immutableReferences` map to
the immutable declarations below (astId→name via the AST).
-/

open Solm ABI

namespace Benchmarks.CompoundIII.Comet.Immutables

-- Each immutable as an `Expr` returning its value (getters + internal rate computations).
def governor : Expr := .immutable "governor"
def pauseGuardian : Expr := .immutable "pauseGuardian"
def baseToken : Expr := .immutable "baseToken"
def baseTokenPriceFeed : Expr := .immutable "baseTokenPriceFeed"
def extensionDelegate : Expr := .immutable "extensionDelegate"
def supplyKink : Expr := .immutable "supplyKink"
def supplyPerSecondInterestRateSlopeLow : Expr := .immutable "supplyPerSecondInterestRateSlopeLow"
def supplyPerSecondInterestRateSlopeHigh : Expr := .immutable "supplyPerSecondInterestRateSlopeHigh"
def supplyPerSecondInterestRateBase : Expr := .immutable "supplyPerSecondInterestRateBase"
def borrowKink : Expr := .immutable "borrowKink"
def borrowPerSecondInterestRateSlopeLow : Expr := .immutable "borrowPerSecondInterestRateSlopeLow"
def borrowPerSecondInterestRateSlopeHigh : Expr := .immutable "borrowPerSecondInterestRateSlopeHigh"
def borrowPerSecondInterestRateBase : Expr := .immutable "borrowPerSecondInterestRateBase"
def storeFrontPriceFactor : Expr := .immutable "storeFrontPriceFactor"
def baseScale : Expr := .immutable "baseScale"
def trackingIndexScale : Expr := .immutable "trackingIndexScale"
def baseTrackingSupplySpeed : Expr := .immutable "baseTrackingSupplySpeed"
def baseTrackingBorrowSpeed : Expr := .immutable "baseTrackingBorrowSpeed"
def baseMinForRewards : Expr := .immutable "baseMinForRewards"
def baseBorrowMin : Expr := .immutable "baseBorrowMin"
def targetReserves : Expr := .immutable "targetReserves"
def decimals : Expr := .immutable "decimals"
def numAssets : Expr := .immutable "numAssets"
def accrualDescaleFactor : Expr := .immutable "accrualDescaleFactor"
def assetList : Expr := .immutable "assetList"

/-- solc `immutableReferences` offsets, keyed by immutable name (verified against the AST). -/
def offsets : List (Ident × List Nat) :=
  [ ("governor", [1592, 3562, 5300, 6314]),
    ("pauseGuardian", [2139, 3872]),
    ("baseToken", [2049, 5173, 5780, 6419, 6603, 10047, 12073, 12352, 14120, 15216, 15439]),
    ("baseTokenPriceFeed", [6921, 10363, 16597, 17562]),
    ("extensionDelegate", [3936, 17874]),
    ("supplyKink", [5091, 8793]),
    ("supplyPerSecondInterestRateSlopeLow", [4094, 8853, 8959]),
    ("supplyPerSecondInterestRateSlopeHigh", [4365, 9007]),
    ("supplyPerSecondInterestRateBase", [4717, 8892]),
    ("borrowKink", [4597, 9065]),
    ("borrowPerSecondInterestRateSlopeLow", [2672, 9125, 9231]),
    ("borrowPerSecondInterestRateSlopeHigh", [2324, 9279]),
    ("borrowPerSecondInterestRateBase", [4233, 9164]),
    ("storeFrontPriceFactor", [1940, 17502]),
    ("baseScale", [3382, 10401, 11062, 16709, 17618]),
    ("trackingIndexScale", [5237, 11787]),
    ("baseTrackingSupplySpeed", [1772, 8517]),
    ("baseTrackingBorrowSpeed", [4777, 8392]),
    ("baseMinForRewards", [4657, 8286]),
    ("baseBorrowMin", [2794, 14711, 15598]),
    ("targetReserves", [2917, 6841]),
    ("decimals", [2856]),
    ("numAssets", [5030, 7705, 10456, 10797, 16643]),
    ("accrualDescaleFactor", [11826]),
    ("assetList", [6223, 7424]) ]

/-- The constructor's immutable offsets as a layout for generated runtime summaries. -/
def immutableLayout : Reasoning.Immutables.Layout :=
  ⟨offsets.flatMap fun (key, sites) => sites.map fun off => (off, 32, key)⟩

def wordBytes? (x : Value) : Option ByteArray :=
  (valueToWord x).map (fun w => ByteArray.mk (EVM.Word.toBytesBE w).toArray)

def patchesFrom (get : Ident → Option Value) : Option (List (Nat × ByteArray)) :=
  offsets.foldrM (fun p acc => do
    let x ← get p.1
    let bytes ← Reasoning.Theory.wordBytes? x
    pure (p.2.map (fun o => (o, bytes)) ++ acc)) []

/-- The runtime code deployed for an immutables store: the template patched with the stored
    values at their `immutableReferences` offsets (the template itself if a value is missing or
    a patch does not fit). -/
def deployedRuntime (template : ByteArray) (imms : Store) : ByteArray :=
  ((patchesFrom (fun n => imms.get? n)).bind (patchRuntime template)).getD template

end Benchmarks.CompoundIII.Comet.Immutables
