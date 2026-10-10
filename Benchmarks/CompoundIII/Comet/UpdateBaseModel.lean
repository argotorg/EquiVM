import Benchmarks.CompoundIII.Comet.AccountRewardModel
import Benchmarks.CompoundIII.Comet.InternalOutcome
import Benchmarks.CompoundIII.Comet.UserBasicWrite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def principalBorrow (principal : UInt256) : Bool := decide (signed104 principal < 0)

def basicSetIndex (evm : EVM.State) (basic : UserBasicData) (principal : UInt256) : UserBasicData :=
  { basic with index := accountRewardIndex evm (principalBorrow principal),
               index_lt := accountRewardIndex_lt evm (principalBorrow principal) }

def updatedBaseBasic (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (basic : UserBasicData) (newPrincipal : UInt256) : UserBasicData :=
  basicSetIndex evm
    (userBasicWithAccrued { basic with principal := newPrincipal }
      (basic.accrued + accountReward v evm basic basic.principal (principalBorrow basic.principal)))
    newPrincipal

def updateBaseOutcome (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (addr : AccountAddress) (basic : UserBasicData) (newPrincipal : UInt256) : InternalOutcome :=
  if AccountRewardValid v evm basic basic.principal (principalBorrow basic.principal) then
    if evm.executionEnv.perm then
      .ok (storeUserBasic evm addr (updatedBaseBasic v evm basic newPrincipal))
    else .staticViolation
  else .reverted

def basicSetIndexStmt (borrow : Bool) : Stmt :=
  .assign .localVar ⟨"basic", [.field "baseTrackingIndex"]⟩
    (.storage ⟨trackingIndexName borrow, []⟩)

def updateBaseFinishBlock : List Stmt :=
  [.ite (.binary .ge (.var "principalNew") (.intLit 0))
    [basicSetIndexStmt false] [basicSetIndexStmt true],
    .assign .storage ⟨"userBasic", [.mindex (.var "account")]⟩ (.var "basic")]

def updateBaseCallable : CallableDecl :=
  { params := [⟨"account", .elem .address⟩, ⟨"basic", .tuple
      [.elem (.int (.sint ⟨104, by decide⟩)), .elem (.int (.uint ⟨64, by decide⟩)),
        .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨16, by decide⟩)),
        .elem (.int (.uint ⟨8, by decide⟩))]⟩,
      ⟨"principalNew", .elem (.int (.sint ⟨104, by decide⟩))⟩]
    returnType := []
    body := [.letDecl "principal" (some (.elem (.int (.sint ⟨104, by decide⟩))))
        (.field (.var "basic") "principal"),
      .assign .localVar ⟨"basic", [.field "principal"]⟩ (.var "principalNew"),
      .ite (.binary .ge (.var "principal") (.intLit 0))
        (accountRewardBlock false) (accountRewardBlock true)] ++ updateBaseFinishBlock }

theorem updateBaseCallable_lookup :
    lookupCallable? contract "updateBasePrincipal" = some updateBaseCallable := rfl

def updateBaseEntry (v : CometWithExtendedAssetListImmutables) (addr : AccountAddress)
    (basic : UserBasicData) (newPrincipal : UInt256) : Frame :=
  { contract := contract, immutables := immStore v,
    locals := (((∅ : Store).insert "principalNew" (.int (signed104 newPrincipal))).insert
      "basic" (userBasicValue basic)).insert "account" (.address addr) }

def updateBaseRewardEntry (v : CometWithExtendedAssetListImmutables) (addr : AccountAddress)
    (basic : UserBasicData) (newPrincipal : UInt256) : Frame :=
  let frame := updateBaseEntry v addr basic newPrincipal
  { frame with
    locals := (frame.locals.insert "principal" (.int (signed104 basic.principal))).insert "basic"
      (userBasicValue { basic with principal := newPrincipal }) }

end Benchmarks.CompoundIII.Comet
