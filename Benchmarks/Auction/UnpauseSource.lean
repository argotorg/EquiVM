import Benchmarks.Auction.PausableSource
import Benchmarks.Auction.SettleStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def unpauseWord (word : UInt256) : UInt256 := UInt256.land word (UInt256.lnot ⟨255⟩)

def unpauseState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨51⟩
    (unpauseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩))

theorem SourceState.unpause {s0 I cA σ evm} (hs : SourceState s0 I cA σ evm) :
    SourceState s0 I cA
      (sstoreAccountMap I.codeOwner σ ⟨51⟩ (unpauseWord (storedWord σ I ⟨51⟩)))
      (unpauseState evm) := by
  have hw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩ =
      storedWord σ I ⟨51⟩ := by
    exact hs.storageRead _
  unfold unpauseState
  rw [hw, hs.env]
  exact hs.storageWrite _ _

theorem unpauseStoreSource {evm : EVM.State} {locals : Store}
    (hb : locals.get? "_paused" = none) :
    ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
      (.assign .storage pausedRef (.boolLit false))
      (.ok { contract := auctionContract, locals := locals } (unpauseState evm)) := by
  apply ExecStmt.assign (value := .bool false) (by simp only [evalExpr?, pure])
  exact scalarWrite evm _ locals "_paused" (.elem .bool) (auctionBoolLoc ⟨51⟩) (.bool false)
    hb (by native_decide) rfl (by trivial) (storageLocStore_bool_false_offset0 evm ⟨51⟩)

end Auction
