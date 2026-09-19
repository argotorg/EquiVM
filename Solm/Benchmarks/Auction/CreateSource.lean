import Solm.Benchmarks.Auction.CreateState
import Solm.Benchmarks.Auction.RangeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def createStoreStmts : List Stmt :=
  [.assign .storage (aField "nounId") (.var "nounId"),
    .assign .storage (aField "amount") (.intLit 0),
    .assign .storage (aField "startTime") (.var "startTime"),
    .assign .storage (aField "endTime") (.var "endTime"),
    .assign .storage (aField "bidder") zeroAddr,
    .assign .storage (aField "settled") (.boolLit false)]

def createSuccessStmts : List Stmt :=
  [.letDecl "startTime" (some uint256) now,
    .letDecl "endTime" (some uint256)
      (u256 (.binary .add (.var "startTime") (.storage durationRef)))] ++ createStoreStmts

theorem createStoresSource {evm locals noun start finish}
    (ha : locals.get? "auction" = none)
    (hn : locals.get? "nounId" = some (.int (Int.ofNat (UInt256.toNat noun))))
    (ht : locals.get? "startTime" = some (.int (Int.ofNat (UInt256.toNat start))))
    (he : locals.get? "endTime" = some (.int (Int.ofNat (UInt256.toNat finish)))) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm createStoreStmts
      (.ok { contract := auctionContract, locals := locals }
        (createdAuctionState evm noun start finish)) := by
  apply ExecBlock.consNormal (ExecStmt.assign (value := .int (Int.ofNat noun.toNat))
    (by simp only [evalExpr?, hn, EvalResult.ofOption])
    (auctionFieldWrite evm _ locals "nounId" (.elem (.int uint256Int)) (auctionUint256Loc ⟨207⟩)
      _ ha (by native_decide) rfl (by trivial) (storageLocStore_uint256 evm ⟨207⟩ noun)))
  apply ExecBlock.consNormal (ExecStmt.assign (value := .int 0)
    (by simp only [evalExpr?, pure])
    (auctionFieldWrite _ _ locals "amount" (.elem (.int uint256Int)) (auctionUint256Loc ⟨208⟩)
      _ ha (by native_decide) rfl (by trivial) (storageLocStore_uint256 _ ⟨208⟩ ⟨0⟩)))
  apply ExecBlock.consNormal (ExecStmt.assign (value := .int (Int.ofNat start.toNat))
    (by simp only [evalExpr?, ht, EvalResult.ofOption])
    (auctionFieldWrite _ _ locals "startTime" (.elem (.int uint256Int)) (auctionUint256Loc ⟨209⟩)
      _ ha (by native_decide) rfl (by trivial) (storageLocStore_uint256 _ ⟨209⟩ start)))
  apply ExecBlock.consNormal (ExecStmt.assign (value := .int (Int.ofNat finish.toNat))
    (by simp only [evalExpr?, he, EvalResult.ofOption])
    (auctionFieldWrite _ _ locals "endTime" (.elem (.int uint256Int)) (auctionUint256Loc ⟨210⟩)
      _ ha (by native_decide) rfl (by trivial) (storageLocStore_uint256 _ ⟨210⟩ finish)))
  simp only [storageStore_executionEnv]
  change ExecBlock auctionConfig _ (createdScalarState evm noun start finish) _ _
  apply ExecBlock.consNormal (ExecStmt.assign (value := .address (.ofNat 0))
    (by simp only [zeroAddr, evalExpr?, pure, bind, EvalResult.bind, castValue?, addrSt,
        EvalResult.ofOption]; rfl)
    (auctionFieldWrite _ _ locals "bidder" (.elem .address) (auctionAddrLoc ⟨211⟩)
      _ ha (by native_decide) rfl (by trivial)
      (storageLocStore_address_offset0 _ ⟨211⟩ ⟨0⟩ (by decide))))
  apply ExecBlock.consNormal (ExecStmt.assign (value := .bool false)
    (by simp only [evalExpr?, pure])
    (auctionFieldWrite _ _ locals "settled" (.elem .bool) (auctionBoolLocAt ⟨211⟩ 20)
      _ ha (by native_decide) rfl (by trivial) (storageLocStore_settledFalse _ ⟨211⟩)))
  exact ExecBlock.nil

theorem durationSourceRead {s0 I cA σ evm locals}
    (hs : SourceState s0 I cA σ evm) (hd : locals.get? "duration" = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.storage durationRef) = .ok (.int (Int.ofNat (storedWord σ I ⟨206⟩).toNat)) := by
  rw [durationRef, scalarRead evm locals "duration" (.int uint256Int) (auctionUint256Loc ⟨206⟩)
    hd (by native_decide) rfl, loadUint256, storedWord_equiv hs.accounts, ← hs.env]
  rfl

def createdLocals (locals : Store) (start finish : UInt256) : Store :=
  (locals.insert "startTime" (.int (Int.ofNat start.toNat))).insert "endTime"
    (.int (Int.ofNat finish.toNat))

theorem createSuccessSource {s0 I cA σ evm locals noun}
    (hs : SourceState s0 I cA σ evm) (ha : locals.get? "auction" = none)
    (hd : locals.get? "duration" = none)
    (hn : locals.get? "nounId" = some (.int (Int.ofNat (UInt256.toNat noun))))
    (hno : (UInt256.ofNat I.header.timestamp).toNat + (storedWord σ I ⟨206⟩).toNat < UInt256.size) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm createSuccessStmts
      (.ok
        { contract := auctionContract
          locals := createdLocals locals (UInt256.ofNat I.header.timestamp)
            (UInt256.ofNat I.header.timestamp + storedWord σ I ⟨206⟩) }
        (createdAuctionState evm noun (UInt256.ofNat I.header.timestamp)
          (UInt256.ofNat I.header.timestamp + storedWord σ I ⟨206⟩))) := by
  apply ExecBlock.consNormal (ExecStmt.letDecl
    (value := .int (Int.ofNat (UInt256.ofNat I.header.timestamp).toNat)) (by
    simp only [now, evalExpr?, envValue, hs.env, pure]))
  apply ExecBlock.consNormal (ExecStmt.letDecl (checkedAddSourceOk
    (by simp only [evalExpr?, store_get_self, EvalResult.ofOption])
    (durationSourceRead hs ((store_get_ne _ _ (by decide)).trans hd)) hno))
  exact createStoresSource
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans ha))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hn))
    ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)) (store_get_self _ _ _)

theorem createSuccessSourceOverflow {s0 I cA σ evm locals}
    (hs : SourceState s0 I cA σ evm) (hd : locals.get? "duration" = none)
    (hover : UInt256.size ≤ (UInt256.ofNat I.header.timestamp).toNat +
      (storedWord σ I ⟨206⟩).toNat) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm createSuccessStmts
      .reverted := by
  apply ExecBlock.consNormal (ExecStmt.letDecl
    (value := .int (Int.ofNat (UInt256.ofNat I.header.timestamp).toNat)) (by
    simp only [now, evalExpr?, envValue, hs.env, pure]))
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert (checkedAddSourceOverflow
    (by simp only [evalExpr?, store_get_self, EvalResult.ofOption])
    (durationSourceRead hs ((store_get_ne _ _ (by decide)).trans hd)) hover))

end Auction
