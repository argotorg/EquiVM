import Benchmarks.Morpho.MetaMorphoV1_1.SupplyAssetsSource

/-! The allocated accrued-assets helper's initialization and withdrawal-queue loop. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option maxRecDepth 2000

def accruedAssetsCondition : Expr :=
  .binary .lt (.var "i") (.arrayLength .storage ⟨"withdrawQueue", []⟩)

def accruedAssetsPost : List Stmt :=
  [.assign .localVar ⟨"i", []⟩
    (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "i") (.intLit 1)))]

def accruedAssetsIteration : List Stmt :=
  cursorCall allocatedMarketParamsFunction.name
    [.storage ⟨"withdrawQueue", [.aindex (.var "i")]⟩] "__c0" ++
  cursorCall allocatedSupplyAssetsFunction.name
    [.immutable "MORPHO", .var "__c0", .env .this] "__c1" ++
  [.assign .localVar ⟨"realTotalAssets", []⟩
    (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "realTotalAssets") (.var "__c1")))]

theorem allocatedAccruedFeeAssetsFunction_prefix :
    allocatedAccruedFeeAssetsFunction.body =
      [.letDecl "feeShares" (some abiUInt256) (.intLit 0),
       .letDecl "newTotalAssets" (some abiUInt256) (.intLit 0),
       .letDecl "newLostAssets" (some abiUInt256) (.intLit 0),
       .letDecl "realTotalAssets" (some abiUInt256) (.intLit 0),
       .for [.letDecl "i" (some abiUInt256) (.intLit 0)] accruedAssetsCondition
         accruedAssetsPost accruedAssetsIteration] ++
      allocatedAccruedFeeAssetsFunction.body.drop 5 := by decide +kernel

set_option maxRecDepth 2000 in
theorem allocatedAccruedFeeAssetsFunction_lookup :
    lookupCallable? contract allocatedAccruedFeeAssetsFunction.name =
      some allocatedAccruedFeeAssetsFunction.toCallable := by rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
