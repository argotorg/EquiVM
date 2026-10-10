import Benchmarks.CompoundIII.Comet.BaseReward
import Benchmarks.CompoundIII.Comet.AccrualWrites
import Benchmarks.CompoundIII.Comet.UserBasicLocal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def accountRewardName (borrow : Bool) : Ident := if borrow then "__c1" else "__c0"

def accountMagnitude (principal : UInt256) (borrow : Bool) : UInt256 :=
  if borrow then negativePrincipal principal else positivePrincipal principal

def accountMagnitudeExpr (borrow : Bool) : Expr :=
  .cast (if borrow then .inRange (.sint ⟨104, by decide⟩)
    (.binary .sub (.intLit 0) (.var "principal")) else .var "principal")
    (.elem (.int (.uint ⟨104, by decide⟩)))

def accountRewardIndex (evm : EVM.State) (borrow : Bool) : UInt256 :=
  trackingIndexWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) borrow

def accountRewardDelta (evm : EVM.State) (basic : UserBasicData) (borrow : Bool) : UInt256 :=
  UInt256.sub (accountRewardIndex evm borrow) basic.index

def accountReward (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (basic : UserBasicData) (principal : UInt256) (borrow : Bool) : UInt256 :=
  baseRewardWord v (accountMagnitude principal borrow) (accountRewardDelta evm basic borrow)

abbrev AccountRewardValid (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (basic : UserBasicData) (principal : UInt256) (borrow : Bool) : Prop :=
  basic.index.toNat ≤ (accountRewardIndex evm borrow).toNat ∧
    -(2^103 : Int) < signed104 principal ∧
    BaseRewardValid v (accountMagnitude principal borrow) (accountRewardDelta evm basic borrow) ∧
    basic.accrued.toNat + (accountReward v evm basic principal borrow).toNat < 2^64

def accountRewardBlock (borrow : Bool) : List Stmt :=
  [.letDecl "indexDelta" (some (.elem (.int (.uint ⟨256, by decide⟩))))
    (.cast (.inRange (.uint ⟨64, by decide⟩)
      (.binary .sub (.storage ⟨trackingIndexName borrow, []⟩)
        (.field (.var "basic") "baseTrackingIndex"))) (.elem (.int (.uint ⟨256, by decide⟩)))),
    .internalCall "safe64" [baseRewardExpr (accountMagnitudeExpr borrow) (.var "indexDelta")]
      (accountRewardName borrow),
    .assign .localVar ⟨"basic", [.field "baseTrackingAccrued"]⟩
      (.inRange (.uint ⟨64, by decide⟩)
        (.binary .add (.field (.var "basic") "baseTrackingAccrued")
          (.var (accountRewardName borrow))))]

def accountRewardFrame (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (basic : UserBasicData) (principal : UInt256) (borrow : Bool) : Frame :=
  let reward := accountReward v evm basic principal borrow
  { frame with
    locals := ((frame.locals.insert "indexDelta"
      (.int (accountRewardDelta evm basic borrow).toNat)).insert
      (accountRewardName borrow) (.int reward.toNat)).insert "basic"
      (userBasicValue (userBasicWithAccrued basic (basic.accrued + reward))) }

theorem accountRewardIndex_lt (evm : EVM.State) (borrow : Bool) :
    (accountRewardIndex evm borrow).toNat < 2^64 := trackingIndexWord_lt _ _

theorem accountRewardDelta_lt {evm basic borrow}
    (hle : basic.index.toNat ≤ (accountRewardIndex evm borrow).toNat) :
    (accountRewardDelta evm basic borrow).toNat < 2^64 := by
  unfold accountRewardDelta
  rw [usub_toNat hle]
  have hb := accountRewardIndex_lt evm borrow
  omega

end Benchmarks.CompoundIII.Comet
