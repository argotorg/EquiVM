import Benchmarks.Auction.Snapshot
import Benchmarks.Auction.CallState

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def Snapshot.value (s : Snapshot) : Value :=
  .struct "Auction"
    [("nounId", .int (Int.ofNat s.nounId.toNat)), ("amount", .int (Int.ofNat s.amount.toNat)),
      ("startTime", .int (Int.ofNat s.startTime.toNat)), ("endTime", .int (Int.ofNat
        s.endTime.toNat)),
      ("bidder", .address (AccountAddress.ofNat s.bidderWord.toNat)),
      ("settled", wordToElem .bool s.settledByte)]

theorem snapshotSourceRead (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "auction" = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.storage auctionRef) = .ok (snapshotOfState evm).value := by
  have hr : resolveStorageRef? auctionConfig { contract := auctionContract, locals := locals }
      evm auctionRef = .ok ({ base := "auction" }, auctionStructTy) := by
    apply resolveStorageRef?_ok hbase
    · simp [auctionRef, evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
    · change storageTypeAt? auctionContract.storage { base := "auction" } = some auctionStructTy
      native_decide
  have h0 := readStorage?_elem (cfg := auctionConfig) (evm := evm)
    (er := { base := "auction", steps := [.field "nounId"] })
    (t := .int uint256Int) (loc := auctionUint256Loc ⟨207⟩) rfl
  have h1 := readStorage?_elem (cfg := auctionConfig) (evm := evm)
    (er := { base := "auction", steps := [.field "amount"] })
    (t := .int uint256Int) (loc := auctionUint256Loc ⟨208⟩) rfl
  have h2 := readStorage?_elem (cfg := auctionConfig) (evm := evm)
    (er := { base := "auction", steps := [.field "startTime"] })
    (t := .int uint256Int) (loc := auctionUint256Loc ⟨209⟩) rfl
  have h3 := readStorage?_elem (cfg := auctionConfig) (evm := evm)
    (er := { base := "auction", steps := [.field "endTime"] })
    (t := .int uint256Int) (loc := auctionUint256Loc ⟨210⟩) rfl
  have h4 := readStorage?_elem (cfg := auctionConfig) (evm := evm)
    (er := { base := "auction", steps := [.field "bidder"] })
    (t := .address) (loc := auctionAddrLoc ⟨211⟩) rfl
  have h5 := readStorage?_elem (cfg := auctionConfig) (evm := evm)
    (er := { base := "auction", steps := [.field "settled"] })
    (t := .bool) (loc := auctionBoolLocAt ⟨211⟩ 20) rfl
  rw [loadUint256] at h0 h1 h2 h3
  rw [loadAddress] at h4
  rw [loadBoolAt] at h5
  have hpow : UInt256.ofNat (256 ^ (20 : Fin 32).val) = (⟨2 ^ 160⟩ : UInt256) := by native_decide
  rw [hpow] at h5
  rw [evalExpr?, hr]
  simp only [bind, EvalResult.bind]
  unfold auctionStructTy
  rw [readStorage?]
  simp only [readFields?, List.nil_append, h0, h1, h2, h3, h4, h5,
    uint256St, addrSt, boolSt, bind, EvalResult.bind, pure]
  rfl

theorem snapshotSourceState {s0 I cA σ evm} (hs : SourceState s0 I cA σ evm) :
    snapshotOfState evm = snapshotOf σ I := by
  rw [snapshotOf_equiv hs.accounts, ← hs.env]
  rfl

theorem snapshotFieldSource {evm locals s name value}
    (hs : locals.get? "_auction" = some (Snapshot.value s))
    (hf : lookupField? s.value name = some value) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (auctionMemField name) = .ok value := by
  simp only [auctionMemField, evalExpr?, hs, EvalResult.ofOption, bind, EvalResult.bind, hf]
  rfl

theorem snapshotNounSource {evm locals s}
    (hs : locals.get? "_auction" = some (Snapshot.value s)) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (auctionMemField "nounId") = .ok (.int (Int.ofNat s.nounId.toNat)) := by
  exact snapshotFieldSource hs (by simp [Snapshot.value, lookupField?, lookupAssoc])

theorem snapshotAmountSource {evm locals s}
    (hs : locals.get? "_auction" = some (Snapshot.value s)) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (auctionMemField "amount") = .ok (.int (Int.ofNat s.amount.toNat)) := by
  exact snapshotFieldSource hs (by simp [Snapshot.value, lookupField?, lookupAssoc])

theorem snapshotStartSource {evm locals s}
    (hs : locals.get? "_auction" = some (Snapshot.value s)) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (auctionMemField "startTime") = .ok (.int (Int.ofNat s.startTime.toNat)) := by
  exact snapshotFieldSource hs (by simp [Snapshot.value, lookupField?, lookupAssoc])

theorem snapshotEndSource {evm locals s}
    (hs : locals.get? "_auction" = some (Snapshot.value s)) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (auctionMemField "endTime") = .ok (.int (Int.ofNat s.endTime.toNat)) := by
  exact snapshotFieldSource hs (by simp [Snapshot.value, lookupField?, lookupAssoc])

theorem snapshotBidderSource {evm locals s}
    (hs : locals.get? "_auction" = some (Snapshot.value s)) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (auctionMemField "bidder") = .ok (.address (AccountAddress.ofNat s.bidderWord.toNat)) := by
  exact snapshotFieldSource hs (by simp [Snapshot.value, lookupField?, lookupAssoc])

theorem snapshotSettledSource {evm locals s}
    (hs : locals.get? "_auction" = some (Snapshot.value s)) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (auctionMemField "settled") = .ok (wordToElem .bool s.settledByte) := by
  exact snapshotFieldSource hs (by simp [Snapshot.value, lookupField?, lookupAssoc])

end Auction
