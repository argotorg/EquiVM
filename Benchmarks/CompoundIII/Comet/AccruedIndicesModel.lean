import Benchmarks.CompoundIII.Comet.IndexAccrual
import Benchmarks.CompoundIII.Comet.RateSource
import Benchmarks.CompoundIII.Comet.UtilizationSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def accruedRate (v : CometWithExtendedAssetListImmutables) (w0 w1 : UInt256)
    (borrow : Bool) : UInt256 := rateWord (rateParams v borrow) (utilizationWord w0 w1)

def accruedIndex (v : CometWithExtendedAssetListImmutables) (w0 w1 elapsed : UInt256)
    (borrow : Bool) : UInt256 :=
  if elapsed = ⟨0⟩ then totalsIndexWord w0 borrow
  else accruedIndexWord (totalsIndexWord w0 borrow) (accruedRate v w0 w1 borrow) elapsed

abbrev AccruedWorkValid (v : CometWithExtendedAssetListImmutables)
    (w0 w1 elapsed : UInt256) : Prop :=
    RateValid (rateParams v false) (utilizationWord w0 w1) ∧
    RateValid (rateParams v true) (utilizationWord w0 w1) ∧
    IndexAccrualValid (totalsIndexWord w0 false) (accruedRate v w0 w1 false) elapsed ∧
    IndexAccrualValid (totalsIndexWord w0 true) (accruedRate v w0 w1 true) elapsed

abbrev AccruedIndicesValid (v : CometWithExtendedAssetListImmutables)
    (w0 w1 elapsed : UInt256) : Prop :=
  if elapsed = ⟨0⟩ then True else AccruedWorkValid v w0 w1 elapsed

theorem accruedIndex_lt {v : CometWithExtendedAssetListImmutables} {w0 w1 elapsed : UInt256}
    (h : AccruedIndicesValid v w0 w1 elapsed) (borrow : Bool) :
    (accruedIndex v w0 w1 elapsed borrow).toNat < 2^64 := by
  by_cases hz : elapsed = ⟨0⟩
  · simpa only [accruedIndex, if_pos hz] using totalsIndexWord_lt w0 borrow
  · rw [AccruedIndicesValid, if_neg hz] at h
    rw [accruedIndex, if_neg hz]
    cases borrow
    · exact accruedIndexWord_lt h.2.2.1
    · exact accruedIndexWord_lt h.2.2.2

def accruedIndicesThen : List Stmt :=
  [.internalCall "getUtilization_body" [] "utilization",
    .internalCall "getSupplyRate_body" [.var "utilization"] "supplyRate",
    .internalCall "getBorrowRate_body" [.var "utilization"] "borrowRate"] ++
      indexAccrualBlock false ++ indexAccrualBlock true

def accruedIndicesCallable : CallableDecl :=
  { params := [⟨"timeElapsed", .elem (.int (.uint ⟨256, by decide⟩))⟩]
    returnType := [.elem (.int (.uint ⟨64, by decide⟩)),
      .elem (.int (.uint ⟨64, by decide⟩))]
    body := [
      .letDecl "baseSupplyIndex_" (some (.elem (.int (.uint ⟨64, by decide⟩))))
        (.storage ⟨"baseSupplyIndex", []⟩),
      .letDecl "baseBorrowIndex_" (some (.elem (.int (.uint ⟨64, by decide⟩))))
        (.storage ⟨"baseBorrowIndex", []⟩),
      .ite (.binary .gt (.var "timeElapsed") (.intLit 0)) accruedIndicesThen [],
      .return [.var "baseSupplyIndex_", .var "baseBorrowIndex_"]] }

theorem accruedIndicesCallable_lookup :
    lookupCallable? contract "accruedInterestIndices" = some accruedIndicesCallable := rfl

def accruedIndicesEntry (v : CometWithExtendedAssetListImmutables) (elapsed : UInt256) : Frame :=
  { contract := contract, locals := (∅ : Store).insert "timeElapsed" (.int elapsed.toNat),
    immutables := immStore v }

def accruedIndicesInitialFrame (v : CometWithExtendedAssetListImmutables)
    (w0 elapsed : UInt256) : Frame :=
  let f := accruedIndicesEntry v elapsed
  { f with
    locals := (f.locals.insert "baseSupplyIndex_" (.int (totalsIndexWord w0 false).toNat)).insert
      "baseBorrowIndex_" (.int (totalsIndexWord w0 true).toNat) }

def accruedIndicesRatesFrame (v : CometWithExtendedAssetListImmutables)
    (w0 w1 elapsed : UInt256) : Frame :=
  let f := accruedIndicesInitialFrame v w0 elapsed
  { f with
    locals := ((f.locals.insert "utilization" (.int (utilizationWord w0 w1).toNat)).insert
      "supplyRate" (.int (accruedRate v w0 w1 false).toNat)).insert
        "borrowRate" (.int (accruedRate v w0 w1 true).toNat) }

def accruedIndicesUpdatedFrame (v : CometWithExtendedAssetListImmutables)
    (w0 w1 elapsed : UInt256) : Frame :=
    let f := accruedIndicesRatesFrame v w0 w1 elapsed
    let f' := indexAccrualFrame f false (totalsIndexWord w0 false) (accruedRate v w0 w1 false) elapsed
    indexAccrualFrame f' true (totalsIndexWord w0 true) (accruedRate v w0 w1 true) elapsed

def accruedIndicesFinalFrame (v : CometWithExtendedAssetListImmutables)
    (w0 w1 elapsed : UInt256) : Frame :=
  if elapsed = ⟨0⟩ then accruedIndicesInitialFrame v w0 elapsed
  else accruedIndicesUpdatedFrame v w0 w1 elapsed

end Benchmarks.CompoundIII.Comet
