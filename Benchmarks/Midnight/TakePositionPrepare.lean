import Benchmarks.Midnight.TakePositionPrepareSource
import Benchmarks.Midnight.TakePositionPrepareMemory
import Benchmarks.Midnight.TakePositionsRead
import Benchmarks.Midnight.TakeBuyerUpdateGuard
import Benchmarks.Midnight.TakeCreditSource

/-! Select the participants, form both storage aliases, and reach the buyer update branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem midnightTakePositionPrepare {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {offer : OfferData} {mem rdata : ByteArray}
    {aw marketPtr arrayPtr callbackPtr offerRoot id units taker saved : UInt256}
    {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (ht : taker.toNat < EVM.addressModulus)
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hs : SourceState s0 I evm.accountMap evm)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr offerRoot offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (htaker : memLoad (UInt256.ofNat 544) mem = taker)
    (hu : calldataWord I.calldata 68 = units)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨11826⟩ (saved :: R) mem aw rdata evm.accountMap k C) :
    ABlock config evm frame (takeTransition.body.drop 27)
      (takePositionPrepareFrame frame evm offer id taker) (takeTransition.body.drop 32) ∧
    TakeSourceFrame (takePositionPrepareFrame frame evm offer id taker) offer id units taker
      receiver callback ratifierData data ∧
    ∃ aw' k' C', MemoryFunding credit (takePositionPrepareMemory mem offer id taker) aw' C' ∧
      RD midnightBytecode I g s0
        (takeBuyerUpdatePC (positionFieldWord evm id (takeBuyer offer taker) 0)
          (low128 (healthPositionWord evm id (takeBuyer offer taker))) units)
        (positionSlot id (takeSeller offer taker) :: saved ::
          positionSlot id (takeBuyer offer taker) :: R)
        (takePositionPrepareMemory mem offer id taker) aw' rdata evm.accountMap k' C' := by
  have hmem : 1312 ≤ mem.size := by
    have hw := ho.words.size
    change 832 + 32 * 15 ≤ mem.size at hw
    omega
  have hm1 : 608 ≤ (takeParticipantsMemory mem offer taker).size :=
    (by omega : 608 ≤ mem.size).trans (takeParticipantsMemory_size mem offer taker)
  have hid1 : memLoad (UInt256.ofNat 512) (takeParticipantsMemory mem offer taker) = id := by
    rw [takeParticipantsMemory_load offer taker (UInt256.ofNat 512)
      (by change 544 ≤ mem.size; omega) (Or.inl (by decide)) (Or.inr (by decide)), hid]
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightTakeParticipantsRuntime
    (by simp only [List.length_cons]; omega) ho hoffer htaker ha rd
  obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightTakePositionsRead hstack hm1 hid1
    (takeParticipantsMemory_buyer mem offer taker) (takeParticipantsMemory_seller mem offer taker)
    (takeBuyer_canonical ht) (takeSeller_canonical ht) ha1 rd1
  obtain ⟨k3, C3, ha3, rd3⟩ := midnightTakeBuyerUpdateGuard (by omega) hu ha2 rd2
  rw [← positionCreditSourceWord hs, ← positionDebtSourceWord hs] at rd3
  exact ⟨takePositionPrepareSource hf ht, hf.positionPrepare, aw2, k3, C3, ha3, rd3⟩

end Benchmarks.Midnight
