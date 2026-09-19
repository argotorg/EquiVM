import Solm.Benchmarks.Auction.SnapshotSource
import Solm.Benchmarks.Auction.PaymentArithmetic
import Solm.Benchmarks.Auction.InitializerSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

structure SettleValues (locals : Store) (s : Snapshot) (ptr : UInt256) : Prop where
  snapshot : locals.get? "_auction" = some s.value
  ptr : locals.get? "_freePtr" = some (.int (Int.ofNat ptr.toNat))
  auction : locals.get? "auction" = none
  nouns : locals.get? "nouns" = none
  owner : locals.get? "_owner" = none

theorem SettleValues.insertOther {locals s ptr} (h : SettleValues locals s ptr)
    (value : Value) {name : Ident} (hs : (name == "_auction") = false)
    (hp : (name == "_freePtr") = false) (ha : (name == "auction") = false)
    (hn : (name == "nouns") = false) (ho : (name == "_owner") = false) :
    SettleValues (locals.insert name value) s ptr := by
  exact ⟨(store_get_ne _ _ hs).trans h.snapshot, (store_get_ne _ _ hp).trans h.ptr,
    (store_get_ne _ _ ha).trans h.auction, (store_get_ne _ _ hn).trans h.nouns,
    (store_get_ne _ _ ho).trans h.owner⟩

theorem SettleValues.setFree {locals s ptr} (h : SettleValues locals s ptr) (next : UInt256) :
    SettleValues (locals.insert "_freePtr" (.int (Int.ofNat next.toNat))) s next := by
  exact ⟨(store_get_ne _ _ (by decide)).trans h.snapshot, store_get_self _ _ _,
    (store_get_ne _ _ (by decide)).trans h.auction,
    (store_get_ne _ _ (by decide)).trans h.nouns,
    (store_get_ne _ _ (by decide)).trans h.owner⟩

def settleSnapshotStmts : List Stmt :=
  [.letDecl "_auction" none (.storage auctionRef), advanceFreePtr (.intLit 192)]

def settleGuardStmts : List Stmt :=
  [.require (.binary .ne (auctionMemField "startTime") (.intLit 0)),
    .require (.unary .not (auctionMemField "settled")),
    .require (.binary .ge now (auctionMemField "endTime"))]

theorem settleSnapshotSource {evm locals ptr}
    (hp : locals.get? "_freePtr" = some (.int (Int.ofNat ptr.toNat)))
    (ha : locals.get? "auction" = none) (hn : locals.get? "nouns" = none)
    (ho : locals.get? "_owner" = none) (hb : ptr.toNat + 192 < UInt256.size) :
    ∃ locals',
      ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
        settleSnapshotStmts (.ok { contract := auctionContract, locals := locals' } evm) ∧
      SettleValues locals' (snapshotOfState evm) (ptr + ⟨192⟩) := by
  have hv : SettleValues (locals.insert "_auction" (snapshotOfState evm).value)
      (snapshotOfState evm) ptr := by
    exact ⟨store_get_self _ _ _, (store_get_ne _ _ (by decide)).trans hp,
      (store_get_ne _ _ (by decide)).trans ha, (store_get_ne _ _ (by decide)).trans hn,
      (store_get_ne _ _ (by decide)).trans ho⟩
  refine ⟨_, ?_, hv.setFree (ptr + ⟨192⟩)⟩
  apply ExecBlock.consNormal (ExecStmt.letDecl (snapshotSourceRead evm locals ha))
  exact ExecBlock.consNormal
    (advanceFreePtrSource (delta := ⟨192⟩) hv.ptr
      (by simp only [evalExpr?, pure]; rfl) hb) ExecBlock.nil

theorem settleStartGuardSource {evm locals s}
    (hs : locals.get? "_auction" = some (Snapshot.value s)) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .ne (auctionMemField "startTime") (.intLit 0)) =
      .ok (.bool (decide (s.startTime ≠ ⟨0⟩))) := by
  simp only [evalExpr?, snapshotStartSource hs, pure, bind, EvalResult.bind, evalBinaryOp?]
  congr 2
  by_cases hz : s.startTime = ⟨0⟩
  · rw [hz]; rfl
  · have hn : s.startTime.toNat ≠ 0 := by
      intro he
      exact hz (u256_inj he)
    simp [hz, hn]

theorem settleUnsettledGuardSource {evm locals s}
    (hs : locals.get? "_auction" = some (Snapshot.value s)) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.unary .not (auctionMemField "settled")) =
      .ok (.bool (decide (s.settledByte = ⟨0⟩))) := by
  simp only [evalExpr?, snapshotSettledSource hs, wordToElemBool, bind, EvalResult.bind,
    evalUnaryOp?, EvalResult.ofOption, Bool.not_not]

theorem settleEndGuardSource {evm locals s}
    (hs : locals.get? "_auction" = some (Snapshot.value s)) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .ge now (auctionMemField "endTime")) =
      .ok (.bool (decide (s.endTime.toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat))) := by
  simp only [now, evalExpr?, snapshotEndSource hs, envValue, pure, bind, EvalResult.bind,
    evalBinaryOp?, Int.ofNat_eq_natCast, Int.ofNat_le]

end Auction
