import Benchmarks.Auction.PausableSource
import Benchmarks.Auction.SettleStorage

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def unpauseWord (word : UInt256) : UInt256 := UInt256.land word (UInt256.lnot ⟨255⟩)

def unpauseState (evm : EVM.State) : EVM.State :=
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨51⟩
    (unpauseWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩))

theorem SourceState.unpause {s0 I σ evm} (hs : SourceState s0 I σ evm) :
    SourceState s0 I
      (sstoreAccountMap I.codeOwner σ ⟨51⟩ (unpauseWord (solcSlotWord σ I ⟨51⟩)))
      (unpauseState evm) := by
  have hw : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩ =
      solcSlotWord σ I ⟨51⟩ := by
    exact hs.storageRead _
  unfold unpauseState
  rw [hw, hs.env]
  exact hs.storageWrite _ _

theorem unpauseStoreSourceSplit {evm : EVM.State} {locals : Store}
    (hb : locals.get? "_paused" = none) :
    (evm.executionEnv.perm = true → ExecStmt fork auctionConfig { contract := auctionContract, locals := locals } evm
      (.assign .storage pausedRef (.boolLit false))
      (.ok { contract := auctionContract, locals := locals } (unpauseState evm))) ∧
      (evm.executionEnv.perm = false →
        ExecStmt fork auctionConfig { contract := auctionContract, locals := locals } evm
        (.assign .storage pausedRef (.boolLit false)) .staticViolation) := by
  have hvalue : evalExpr? auctionConfig { contract := auctionContract, locals := locals }
      evm (.boolLit false) = .ok (.bool false) := by simp only [evalExpr?, pure]
  have hassign := scalarWrite evm _ locals "_paused" (.elem .bool)
    (auctionBoolLoc ⟨51⟩) (.bool false) hb (by native_decide) rfl (by exact Or.inl ⟨_, rfl⟩)
    (storageLocStore_bool_false_offset0 evm ⟨51⟩)
  exact ⟨fun hperm ↦ ExecStmt.assign (hperm := Or.inr hperm) hvalue hassign,
    fun hperm ↦ ExecStmt.assignStatic hvalue hassign hperm⟩

theorem unpauseStoreSource {evm : EVM.State} {locals : Store}
    (hb : locals.get? "_paused" = none)
    (hperm : evm.executionEnv.perm = true) :
    ExecStmt fork auctionConfig { contract := auctionContract, locals := locals } evm
      (.assign .storage pausedRef (.boolLit false))
      (.ok { contract := auctionContract, locals := locals } (unpauseState evm)) :=
  (unpauseStoreSourceSplit hb).1 hperm

end Auction
