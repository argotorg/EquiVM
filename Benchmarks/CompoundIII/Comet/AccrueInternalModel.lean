import Benchmarks.CompoundIII.Comet.InternalOutcome
import Benchmarks.CompoundIII.Comet.TrackingAccrualModel
import Benchmarks.CompoundIII.Comet.CurrentIndicesSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def accrueElapsed (evm : EVM.State) : UInt256 :=
  currentElapsed (timestampWord evm.executionEnv)
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)

abbrev AccrueTimeValid (evm : EVM.State) : Prop :=
  (timestampWord evm.executionEnv).toNat < 2^40 ∧
    (lastAccrualWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)).toNat ≤
      (timestampWord evm.executionEnv).toNat

abbrev AccrueIndicesValid (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (elapsed : UInt256) : Prop :=
  AccruedIndicesValid v (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) elapsed

def accrueIndicesState (evm : EVM.State) (v : CometWithExtendedAssetListImmutables)
    (elapsed : UInt256) : EVM.State :=
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
  storeTotalsIndex (storeTotalsIndex evm true (accruedIndex v w0 w1 elapsed true)) false
    (accruedIndex v w0 w1 elapsed false)

abbrev AccrueRewardsValid (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (elapsed : UInt256) : Prop :=
  TrackingBranchValid v false evm elapsed ∧
    TrackingBranchValid v true (trackingBranchState evm v false elapsed) elapsed

def accrueRewardsState (evm : EVM.State) (v : CometWithExtendedAssetListImmutables)
    (elapsed time : UInt256) : EVM.State :=
  storeLastAccrual
    (trackingBranchState (trackingBranchState evm v false elapsed) v true elapsed) time

def accrueThenOutcome (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (elapsed time : UInt256) : InternalOutcome :=
  if AccrueIndicesValid v evm elapsed then
    if evm.executionEnv.perm then
      if AccrueRewardsValid v (accrueIndicesState evm v elapsed) elapsed then
        .ok (accrueRewardsState (accrueIndicesState evm v elapsed) v elapsed time)
      else .reverted
    else .staticViolation
  else .reverted

def accrueOutcome (v : CometWithExtendedAssetListImmutables) (evm : EVM.State) : InternalOutcome :=
  let elapsed := accrueElapsed evm
  if AccrueTimeValid evm then
    if elapsed = ⟨0⟩ then .ok evm
    else accrueThenOutcome v evm elapsed (timestampWord evm.executionEnv)
  else .reverted

def accrueRewardsBlock : List Stmt :=
  [trackingBranch false, trackingBranch true,
    .assign .storage ⟨"lastAccrualTime", []⟩ (.var "now_")]

def accrueThenBlock : List Stmt :=
  [.internalCall "accruedInterestIndices" [.var "timeElapsed"] "__c1",
    .assign .storage ⟨"baseBorrowIndex", []⟩ (.tupleGet (.var "__c1") 1),
    .assign .storage ⟨"baseSupplyIndex", []⟩ (.tupleGet (.var "__c1") 0)] ++ accrueRewardsBlock

def accrueCallable : CallableDecl :=
  { params := [], returnType := [], body :=
    [.internalCall "getNowInternal" [] "now_",
      .letDecl "timeElapsed" (some (.elem (.int (.uint ⟨256, by decide⟩))))
        (.cast (.inRange (.uint ⟨40, by decide⟩)
          (.binary .sub (.var "now_") (.storage ⟨"lastAccrualTime", []⟩)))
          (.elem (.int (.uint ⟨256, by decide⟩)))),
      .ite (.binary .gt (.var "timeElapsed") (.intLit 0)) accrueThenBlock []] }

theorem accrueCallable_lookup :
    lookupCallable? contract "accrueInternal" = some accrueCallable := rfl

def accrueEntry (v : CometWithExtendedAssetListImmutables) : Frame :=
  { contract := contract, locals := ∅, immutables := immStore v }

def accrueTimeFrame (v : CometWithExtendedAssetListImmutables) (elapsed time : UInt256) : Frame :=
  { contract := contract, immutables := immStore v,
    locals := ((∅ : Store).insert "now_" (.int time.toNat)).insert
      "timeElapsed" (.int elapsed.toNat) }

def accrueIndicesFrame (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (elapsed time : UInt256) : Frame :=
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
  let f := accrueTimeFrame v elapsed time
  { f with locals := f.locals.insert "__c1" (.tuple
      [.int (accruedIndex v w0 w1 elapsed false).toNat,
        .int (accruedIndex v w0 w1 elapsed true).toNat]) }

end Benchmarks.CompoundIII.Comet
