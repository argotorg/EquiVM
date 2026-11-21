import Benchmarks.Midnight.Uint128Arithmetic
import Benchmarks.Midnight.MulDiv
import Benchmarks.Midnight.WordMin

/-! Values and checked-arithmetic conditions for a position view. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def slashCredit (credit lastLoss loss : UInt256) : UInt256 :=
  if lastLoss.toNat < 2 ^ 128 - 1 then
    mulDivDown credit (complement128 loss) (complement128 lastLoss)
  else ⟨0⟩

def slashPending (credit pending postCredit : UInt256) : UInt256 :=
  if 0 < credit.toNat then
    UInt256.sub pending (mulDivUp pending (UInt256.sub credit postCredit) credit)
  else ⟨0⟩

def SlashPendingSafe (credit pending postCredit : UInt256) : Prop :=
  0 < credit.toNat → postCredit.toNat ≤ credit.toNat ∧
    MulDivUpSafe pending (UInt256.sub credit postCredit) credit ∧
    (mulDivUp pending (UInt256.sub credit postCredit) credit).toNat ≤ pending.toNat

instance (c p pc : UInt256) : Decidable (SlashPendingSafe c p pc) :=
  inferInstanceAs (Decidable (_ → _ ∧ _ ∧ _))

def positionAccruedFee (pending lastAccrual maturity timestamp : UInt256) : UInt256 :=
  if lastAccrual.toNat < maturity.toNat then
    low128 (mulDivDown pending (UInt256.sub (wordMin timestamp maturity) lastAccrual)
      (UInt256.sub maturity lastAccrual))
  else ⟨0⟩

def PositionAccrualSafe (pending lastAccrual maturity timestamp : UInt256) : Prop :=
  lastAccrual.toNat < maturity.toNat →
    lastAccrual.toNat ≤ (wordMin timestamp maturity).toNat ∧
    pending.toNat * (UInt256.sub (wordMin timestamp maturity) lastAccrual).toNat < UInt256.size

instance (p l m t : UInt256) : Decidable (PositionAccrualSafe p l m t) :=
  inferInstanceAs (Decidable (_ → _ ∧ _))

theorem positionAccruedFee_lt (p l m t : UInt256) :
    (positionAccruedFee p l m t).toNat < 2 ^ 128 := by
  unfold positionAccruedFee
  split
  · exact low128_lt _
  · decide

def PositionViewSafe (credit pending lastLoss loss lastAccrual maturity timestamp : UInt256) : Prop :=
  let pc := slashCredit credit lastLoss loss
  let pp := slashPending credit pending pc
  let fee := positionAccruedFee pp lastAccrual maturity timestamp
  SlashPendingSafe credit pending pc ∧ PositionAccrualSafe pp lastAccrual maturity timestamp ∧
    fee.toNat ≤ (low128 pc).toNat ∧ fee.toNat ≤ (low128 pp).toNat

instance (c p ll loss la m t : UInt256) : Decidable (PositionViewSafe c p ll loss la m t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end Benchmarks.Midnight
