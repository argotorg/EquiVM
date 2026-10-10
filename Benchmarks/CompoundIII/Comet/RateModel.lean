import Benchmarks.CompoundIII.Comet.ArithmeticSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

structure RateParams where
  kink : UInt256
  low : UInt256
  high : UInt256
  base : UInt256

def rateParams (v : CometWithExtendedAssetListImmutables) (borrow : Bool) : RateParams :=
  if borrow then
    ⟨v.borrowKink, v.borrowPerSecondInterestRateSlopeLow,
      v.borrowPerSecondInterestRateSlopeHigh, v.borrowPerSecondInterestRateBase⟩
  else
    ⟨v.supplyKink, v.supplyPerSecondInterestRateSlopeLow,
      v.supplyPerSecondInterestRateSlopeHigh, v.supplyPerSecondInterestRateBase⟩

def rateKinkName (borrow : Bool) : Ident := if borrow then "borrowKink" else "supplyKink"
def rateLowName (borrow : Bool) : Ident :=
  if borrow then "borrowPerSecondInterestRateSlopeLow" else "supplyPerSecondInterestRateSlopeLow"
def rateHighName (borrow : Bool) : Ident :=
  if borrow then "borrowPerSecondInterestRateSlopeHigh" else "supplyPerSecondInterestRateSlopeHigh"
def rateBaseName (borrow : Bool) : Ident :=
  if borrow then "borrowPerSecondInterestRateBase" else "supplyPerSecondInterestRateBase"
def rateCallableName (borrow : Bool) : Ident :=
  if borrow then "getBorrowRate_body" else "getSupplyRate_body"

theorem rateKink_get (v : CometWithExtendedAssetListImmutables) (b : Bool) :
    (immStore v).get? (rateKinkName b) = some (.int (rateParams v b).kink.toNat) := by
  cases b
  · exact immStore_get_supplyKink v
  · exact immStore_get_borrowKink v

theorem rateLow_get (v : CometWithExtendedAssetListImmutables) (b : Bool) :
    (immStore v).get? (rateLowName b) = some (.int (rateParams v b).low.toNat) := by
  cases b
  · exact immStore_get_supplyPerSecondInterestRateSlopeLow v
  · exact immStore_get_borrowPerSecondInterestRateSlopeLow v

theorem rateHigh_get (v : CometWithExtendedAssetListImmutables) (b : Bool) :
    (immStore v).get? (rateHighName b) = some (.int (rateParams v b).high.toNat) := by
  cases b
  · exact immStore_get_supplyPerSecondInterestRateSlopeHigh v
  · exact immStore_get_borrowPerSecondInterestRateSlopeHigh v

theorem rateBase_get (v : CometWithExtendedAssetListImmutables) (b : Bool) :
    (immStore v).get? (rateBaseName b) = some (.int (rateParams v b).base.toNat) := by
  cases b
  · exact immStore_get_supplyPerSecondInterestRateBase v
  · exact immStore_get_borrowPerSecondInterestRateBase v

def rateWord (p : RateParams) (u : UInt256) : UInt256 :=
  if u.toNat ≤ p.kink.toNat then p.base + mulFactorWord p.low u
  else (p.base + mulFactorWord p.low p.kink) + mulFactorWord p.high (UInt256.sub u p.kink)

abbrev RateValid (p : RateParams) (u : UInt256) : Prop :=
  if u.toNat ≤ p.kink.toNat then
    p.low.toNat * u.toNat < UInt256.size ∧
    p.base.toNat + (mulFactorWord p.low u).toNat < UInt256.size ∧
    (p.base + mulFactorWord p.low u).toNat < 2^64
  else
    p.low.toNat * p.kink.toNat < UInt256.size ∧
    p.high.toNat * (UInt256.sub u p.kink).toNat < UInt256.size ∧
    p.base.toNat + (mulFactorWord p.low p.kink).toNat < UInt256.size ∧
    (p.base + mulFactorWord p.low p.kink).toNat +
      (mulFactorWord p.high (UInt256.sub u p.kink)).toNat < UInt256.size ∧
    ((p.base + mulFactorWord p.low p.kink) +
      mulFactorWord p.high (UInt256.sub u p.kink)).toNat < 2^64

theorem rateWord_lt {p : RateParams} {u : UInt256} (h : RateValid p u) :
    (rateWord p u).toNat < 2^64 := by
  unfold RateValid at h
  unfold rateWord
  split_ifs at * <;> tauto

def rateCallable (borrow : Bool) : CallableDecl :=
  { params := [⟨"utilization", .elem (.int (.uint ⟨256, by decide⟩))⟩]
    returnType := [.elem (.int (.uint ⟨64, by decide⟩))]
    body := [.ite (.binary .le (.var "utilization") (.immutable (rateKinkName borrow)))
      [.internalCall "mulFactor" [.immutable (rateLowName borrow), .var "utilization"] "__c0",
       .internalCall "safe64" [.inRange (.uint ⟨256, by decide⟩)
         (.binary .add (.immutable (rateBaseName borrow)) (.var "__c0"))] "__c1",
       .return [.var "__c1"]]
      [.internalCall "mulFactor"
         [.immutable (rateLowName borrow), .immutable (rateKinkName borrow)] "__c2",
       .internalCall "mulFactor"
         [.immutable (rateHighName borrow), .inRange (.uint ⟨256, by decide⟩)
           (.binary .sub (.var "utilization") (.immutable (rateKinkName borrow)))] "__c3",
       .internalCall "safe64" [.inRange (.uint ⟨256, by decide⟩)
         (.binary .add (.inRange (.uint ⟨256, by decide⟩)
           (.binary .add (.immutable (rateBaseName borrow)) (.var "__c2"))) (.var "__c3"))] "__c4",
       .return [.var "__c4"]]] }

theorem rateCallable_lookup (borrow : Bool) :
    lookupCallable? contract (rateCallableName borrow) = some (rateCallable borrow) := by
  cases borrow <;> rfl

end Benchmarks.CompoundIII.Comet
