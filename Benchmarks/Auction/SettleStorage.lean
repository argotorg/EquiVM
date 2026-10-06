import Reasoning.PackedStorage
import Reasoning.ExternalCall
import Benchmarks.Auction.InitializerStorage
import Benchmarks.Auction.CallState
import Benchmarks.Auction.SettleSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction


def settledState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨211⟩
    (setBoolTrueOffset20Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩))

def settledAccounts (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨211⟩ (setBoolTrueOffset20Word (solcSlotWord σ I ⟨211⟩))

theorem settleStoreSource {evm locals} (ha : locals.get? "auction" = none) :
    ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
      (.assign .storage (aField "settled") (.boolLit true))
      (.ok { contract := auctionContract, locals := locals } (settledState evm)) := by
  apply ExecStmt.assign (value := .bool true) (by simp only [evalExpr?, pure])
  apply assignStorageRef_storage_scalar_value
    (er := { base := "auction", steps := [.field "settled"] })
    (ty := .elem .bool) (loc := auctionBoolLocAt ⟨211⟩ 20) ha
  · simp [aField, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      pure, bind, EvalResult.bind]
  · change storageTypeAt? auctionContract.storage
      { base := "auction", steps := [.field "settled"] } = some (.elem .bool)
    native_decide
  · rfl
  · trivial
  · exact storageLocStore_bool_true_offset20 evm ⟨211⟩


theorem SourceState.settled {s0 I σ evm} (hs : SourceState s0 I σ evm) :
    SourceState s0 I (settledAccounts σ I) (settledState evm) := by
  have hw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ =
      solcSlotWord σ I ⟨211⟩ := by
    exact hs.storageRead _
  unfold settledState settledAccounts
  rw [hw, hs.env]
  exact hs.storageWrite _ _

end Auction
