import Benchmarks.Auction.SnapshotSource
import Benchmarks.Auction.WordSourceArithmetic
import Benchmarks.Auction.ReentrancySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def bidStorageNames : List Ident :=
  ["auction", "timeBuffer", "reservePrice", "minBidIncrementPercentage", "_status"]

structure BidValues (locals : Store) (s : Snapshot) (noun : UInt256) : Prop where
  snapshot : locals.get? "_auction" = some s.value
  noun : locals.get? "nounId" = some (.int (Int.ofNat noun.toNat))
  storage : ∀ name ∈ bidStorageNames, locals.get? name = none

theorem BidValues.insertOther {locals s noun} (hv : BidValues locals s noun) (value : Value)
    {name : Ident} (hs : (name == "_auction") = false) (hn : (name == "nounId") = false)
    (hother : name ∉ bidStorageNames) : BidValues (locals.insert name value) s noun := by
  refine ⟨(store_get_ne _ _ hs).trans hv.snapshot, (store_get_ne _ _ hn).trans hv.noun, ?_⟩
  intro key hk
  have hne : (name == key) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    exact hother (he ▸ hk)
  exact (store_get_ne _ _ hne).trans (hv.storage key hk)

def bidInitialGuardStmts : List Stmt :=
  [.require (.binary .eq (auctionMemField "nounId") (.var "nounId")),
    .require (.binary .lt now (auctionMemField "endTime")),
    .require (.binary .ge (.env .callvalue) (.storage reservePriceRef))]

def bidProductExpr : Expr :=
  u256 (.binary .mul (auctionMemField "amount") (.storage minBidIncRef))

def bidMinimumExpr : Expr :=
  u256 (.binary .add (auctionMemField "amount") (.binary .div bidProductExpr (.intLit 100)))

def bidMinimumGuard : Expr := .binary .ge (.env .callvalue) bidMinimumExpr

def bidPercentage (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (storedWord σ I ⟨205⟩) ⟨255⟩

def bidIncrement (amount percentage : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul amount percentage) ⟨100⟩

theorem bidNounGuardSource {evm locals s noun} (hv : BidValues locals s noun) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .eq (auctionMemField "nounId") (.var "nounId")) =
      .ok (.bool (decide (s.nounId = noun))) := by
  simp only [evalExpr?, snapshotNounSource hv.snapshot, hv.noun, EvalResult.ofOption,
    bind, EvalResult.bind, evalBinaryOp?]
  congr 2
  rw [beq_eq_decide]
  congr 1
  apply propext
  constructor
  · intro he
    have hn := Value.int.inj he
    apply u256_inj
    simp only [Int.ofNat_eq_natCast] at hn
    exact_mod_cast hn
  · intro he
    rw [he]

theorem bidTimeGuardSource {s0 I cA σ evm locals s noun}
    (hs : SourceState s0 I cA σ evm) (hv : BidValues locals s noun) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .lt now (auctionMemField "endTime")) =
      .ok (.bool (decide ((UInt256.ofNat I.header.timestamp).toNat < s.endTime.toNat))) := by
  simp only [now, evalExpr?, snapshotEndSource hv.snapshot, envValue, hs.env, pure,
    bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast, Int.ofNat_lt]

theorem bidReserveGuardSource {s0 I cA σ evm locals s noun}
    (hs : SourceState s0 I cA σ evm) (hv : BidValues locals s noun) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .ge (.env .callvalue) (.storage reservePriceRef)) =
      .ok (.bool (decide ((storedWord σ I ⟨204⟩).toNat ≤ I.weiValue.toNat))) := by
  have hr := scalarRead evm locals "reservePrice" (.int uint256Int) (auctionUint256Loc ⟨204⟩)
    (hv.storage _ (by decide)) (by native_decide) rfl
  rw [loadUint256] at hr
  have hw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨204⟩ =
      storedWord σ I ⟨204⟩ := by
    exact hs.storageRead _
  rw [hw] at hr
  simp only [reservePriceRef, evalExpr?, hr, envValue, hs.env, pure,
    bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast, Int.ofNat_le]
  rfl

theorem bidPercentageSource {s0 I cA σ evm locals s noun}
    (hs : SourceState s0 I cA σ evm) (hv : BidValues locals s noun) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.storage minBidIncRef) = .ok (.int (Int.ofNat (bidPercentage σ I).toNat)) := by
  rw [minBidIncRef, scalarRead evm locals "minBidIncrementPercentage"
    (.int uint8Int) (auctionUint8LocAt ⟨205⟩ 0) (hv.storage _ (by decide))
      (by native_decide) rfl, loadUint8]
  rw [bidPercentage, storedWord_equiv hs.accounts, ← hs.env]
  rfl

theorem bidMinimumSource {s0 I cA σ evm locals s noun}
    (hs : SourceState s0 I cA σ evm) (hv : BidValues locals s noun)
    (hmul : s.amount.toNat * (bidPercentage σ I).toNat < UInt256.size)
    (hadd : s.amount.toNat + (bidIncrement s.amount (bidPercentage σ I)).toNat < UInt256.size) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      bidMinimumGuard = .ok (.bool
        (decide ((s.amount + bidIncrement s.amount (bidPercentage σ I)).toNat ≤
          I.weiValue.toNat))) := by
  have hp := checkedMulSourceOk (snapshotAmountSource (evm := evm) hv.snapshot)
    (bidPercentageSource hs hv) hmul
  have hd := divSourceOk hp (b := ⟨100⟩) (rhs := .intLit 100)
    (by simp only [evalExpr?, pure]; rfl) (by decide)
  have ha := checkedAddSourceOk (snapshotAmountSource (evm := evm) hv.snapshot) hd hadd
  change evalExpr? _ _ _ bidMinimumExpr = _ at ha
  change evalExpr? _ _ _ (.binary .ge (.env .callvalue) _) = _
  simp only [evalExpr?, ha, envValue, hs.env, pure, bind, EvalResult.bind, evalBinaryOp?,
    Int.ofNat_eq_natCast, Int.ofNat_le]
  rfl

theorem bidMinimumMulOverflow {s0 I cA σ evm locals s noun}
    (hs : SourceState s0 I cA σ evm) (hv : BidValues locals s noun)
    (hmul : UInt256.size ≤ s.amount.toNat * (bidPercentage σ I).toNat) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      bidMinimumGuard = .revert := by
  have hp := checkedMulSourceOverflow (snapshotAmountSource (evm := evm) hv.snapshot)
    (bidPercentageSource hs hv) hmul
  change evalExpr? _ _ _ bidProductExpr = .revert at hp
  simp only [bidMinimumGuard, bidMinimumExpr, u256, evalExpr?, hp,
    envValue, snapshotAmountSource hv.snapshot, pure, bind, EvalResult.bind]

theorem bidMinimumAddOverflow {s0 I cA σ evm locals s noun}
    (hs : SourceState s0 I cA σ evm) (hv : BidValues locals s noun)
    (hmul : s.amount.toNat * (bidPercentage σ I).toNat < UInt256.size)
    (hadd : UInt256.size ≤ s.amount.toNat + (bidIncrement s.amount (bidPercentage σ I)).toNat) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      bidMinimumGuard = .revert := by
  have hp := checkedMulSourceOk (snapshotAmountSource (evm := evm) hv.snapshot)
    (bidPercentageSource hs hv) hmul
  have hd := divSourceOk hp (b := ⟨100⟩) (rhs := .intLit 100)
    (by simp only [evalExpr?, pure]; rfl) (by decide)
  have ha := checkedAddSourceOverflow (snapshotAmountSource (evm := evm) hv.snapshot) hd hadd
  change evalExpr? _ _ _ bidMinimumExpr = .revert at ha
  change evalExpr? _ _ _ (.binary .ge (.env .callvalue) _) = _
  simp only [evalExpr?, ha, envValue, pure, bind, EvalResult.bind]

end Auction
