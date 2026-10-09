import Benchmarks.CompoundIII.Comet.CollateralValueSource
import Benchmarks.CompoundIII.Comet.IsInAssetSource
import Benchmarks.CompoundIII.Comet.SignedWord
import Benchmarks.CompoundIII.Comet.AssetSearch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def CollateralValueBound (borrow : Bool) (result : Option (EVM.State × CollateralValueData)) :
    Prop :=
  match result with
  | none => True
  | some (_, d) => (d.value borrow).toNat < 2^255

theorem CollateralAfterAsset.value_bound {borrow out amount evm result}
    (ht : CollateralAfterAsset borrow out amount evm result) :
    CollateralValueBound borrow result := by
  cases ht with
  | priceFailed => trivial
  | @result evm' priceOut hc hh hv =>
      apply Classical.byCases (p := CollateralMathValid borrow amount (calldataWord priceOut 32) out)
      · intro hm
        rw [if_pos hm]
        exact hm.2.2
      · intro hm
        rw [if_neg hm]
        trivial

theorem CollateralValueTrace.value_lt {v borrow account i evm evm' d}
    (ht : CollateralValueTrace v borrow account i evm (some (evm', d))) :
    (d.value borrow).toNat < 2^255 := by
  cases ht with
  | assetOk hc hh hv ht => exact ht.value_bound

def collateralResultBool (borrow : Bool) (liquidity : UInt256) : Bool :=
  if borrow then decide (0 ≤ signedWord liquidity) else decide (signedWord liquidity < 0)

def collateralSolventExpr : Expr := .binary .ge (.var "liquidity") (.intLit 0)

def collateralResultExpr (borrow : Bool) : Expr :=
  if borrow then collateralSolventExpr else .binary .lt (.var "liquidity") (.intLit 0)

def collateralAddStmt : Stmt :=
  .assign .localVar ⟨"liquidity", []⟩ (.inRange (.sint ⟨256, by decide⟩)
    (.binary .add (.var "liquidity") (.var "__c8")))

def collateralSelectedBlock (borrow : Bool) : List Stmt :=
  .ite collateralSolventExpr [.return [.boolLit borrow]] [] ::
    (collateralValueBlock borrow ++ [collateralAddStmt])

def collateralLoopBody (borrow : Bool) : List Stmt :=
  [.internalCall "isInAsset" [.var "assetsIn", .var "i", .var "_reserved"] "__c3",
    .ite (.var "__c3") (collateralSelectedBlock borrow) [], assetSearchIncrement]

def collateralLoopTail (borrow : Bool) : List Stmt :=
  [.while assetSearchCond (collateralLoopBody borrow), .return [collateralResultExpr borrow]]

/-- Both collateral checks traverse the same assets, with different factors and final tests. -/
inductive CollateralLoopTrace (v : CometWithExtendedAssetListImmutables) (borrow : Bool)
    (account : AccountAddress) (assets reserved : UInt256) :
    Nat → UInt256 → EVM.State → Option (EVM.State × Bool) → Prop where
  | exhausted {i liquidity evm} (hi : v.numAssets.toNat ≤ i) :
      CollateralLoopTrace v borrow account assets reserved i liquidity evm
        (some (evm, collateralResultBool borrow liquidity))
  | skipped {i liquidity evm result} (hi : i < v.numAssets.toNat)
      (hm : isInAssetBool assets (UInt256.ofNat i) reserved = false)
      (ht : CollateralLoopTrace v borrow account assets reserved (i + 1) liquidity evm result) :
      CollateralLoopTrace v borrow account assets reserved i liquidity evm result
  | solvent {i liquidity evm} (hi : i < v.numAssets.toNat)
      (hm : isInAssetBool assets (UInt256.ofNat i) reserved = true)
      (hl : 0 ≤ signedWord liquidity) :
      CollateralLoopTrace v borrow account assets reserved i liquidity evm (some (evm, borrow))
  | failed {i liquidity evm} (hi : i < v.numAssets.toNat)
      (hm : isInAssetBool assets (UInt256.ofNat i) reserved = true)
      (hl : signedWord liquidity < 0)
      (ht : CollateralValueTrace v borrow account (UInt256.ofNat i) evm none) :
      CollateralLoopTrace v borrow account assets reserved i liquidity evm none
  | next {i liquidity evm evm' d result} (hi : i < v.numAssets.toNat)
      (hm : isInAssetBool assets (UInt256.ofNat i) reserved = true)
      (hl : signedWord liquidity < 0)
      (hv : CollateralValueTrace v borrow account (UInt256.ofNat i) evm (some (evm', d)))
      (ht : CollateralLoopTrace v borrow account assets reserved (i + 1)
        (liquidity + d.value borrow) evm' result) :
      CollateralLoopTrace v borrow account assets reserved i liquidity evm result

end Benchmarks.CompoundIII.Comet
