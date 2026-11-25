import Benchmarks.Midnight.TakePositionPrepare
import Benchmarks.Midnight.TakePositionUpdatesValues
import Benchmarks.Midnight.TakeBuyerUpdate
import Benchmarks.Midnight.TakeSellerUpdate

variable {fork : Ethereum.Fork}

/-! Both conditional position updates in take, including their failure paths. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem midnightTakePositionUpdates {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {offer : OfferData} {mem rdata : ByteArray}
    {aw marketPtr arrayPtr callbackPtr offerRoot root id units taker saved : UInt256}
    {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 30 ≤ 1024) (ht : taker.toNat < EVM.addressModulus)
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hs : SourceState s0 I evm.accountMap evm)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr offerRoot offer)
    (hrootlo : 832 ≤ root.toNat) (hroot : root.toNat < 2^64)
    (hheap : offerRoot.toNat ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (htaker : memLoad (UInt256.ofNat 544) mem = taker)
    (hu : calldataWord I.calldata 68 = units)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11826⟩ (saved :: R) mem aw rdata evm.accountMap k C) :
    (ExecBlock fork config frame evm (takeTransition.body.drop 27) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 27) .staticViolation ∧
      RDstatic fork midnightBytecode g s0) ∨
    (let frame' := takePositionUpdatesFrame frame evm offer id units taker
     let evm' := takePositionUpdatesState evm offer id units taker
     let mem' := takePositionUpdatesMemory mem root evm offer id units taker
     (∀ result, ExecBlock fork config frame' evm' (takeTransition.body.drop 35) result →
       ExecBlock fork config frame evm (takeTransition.body.drop 27) result) ∧
     TakeSourceFrame frame' offer id units taker receiver callback ratifierData data ∧
     SourceState s0 I evm'.accountMap evm' ∧
     MemoryPrefix (takePositionPrepareMemory mem offer id taker) mem' root.toNat ∧
     memLoad (UInt256.ofNat 64) mem' = root ∧
     ∃ aw' k' C', MemoryFunding credit mem' aw' C' ∧
       RD fork midnightBytecode I g s0 ⟨12026⟩
         (positionSlot id (takeSeller offer taker) :: saved ::
           positionSlot id (takeBuyer offer taker) :: R)
         mem' aw' rdata evm'.accountMap k' C') := by
  have hmem : 1312 ≤ mem.size := by
    have hw := ho.words.size
    change 832 + 32 * 15 ≤ mem.size at hw
    omega
  have hmem1 : 1312 ≤ (takePositionPrepareMemory mem offer id taker).size :=
    hmem.trans (takePositionPrepareMemory_size mem offer id taker)
  have hload (off : UInt256) (hlo : 64 ≤ off.toNat) (hin : off.toNat + 32 ≤ mem.size)
      (hb : off.toNat + 32 ≤ 576 ∨ 608 ≤ off.toNat)
      (hse : off.toNat + 32 ≤ 448 ∨ 480 ≤ off.toNat) :
      memLoad off (takePositionPrepareMemory mem offer id taker) = memLoad off mem :=
    takePositionPrepareMemory_load offer id taker off hlo hin hb hse
  have hfree1 := (hload (UInt256.ofNat 64) (by decide) (by change 96 ≤ mem.size; omega)
    (Or.inl (by decide)) (Or.inl (by decide))).trans hfree
  have hoffer1 := (hload (UInt256.ofNat 384) (by decide) (by change 416 ≤ mem.size; omega)
    (Or.inl (by decide)) (Or.inl (by decide))).trans hoffer
  have hid1 := (hload (UInt256.ofNat 512) (by decide) (by change 544 ≤ mem.size; omega)
    (Or.inl (by decide)) (Or.inr (by decide))).trans hid
  have hbuyer1 := takePositionPrepareMemory_buyer offer id taker (by omega : 608 ≤ mem.size)
  have hseller1 := takePositionPrepareMemory_seller offer id taker (by omega : 480 ≤ mem.size)
  have ho1 := takePositionPrepareMemory_offer (id := id) (taker := taker) ho
  obtain ⟨hx1, hf1, aw1, k1, C1, ha1, rd1⟩ := midnightTakePositionPrepare (by omega) ht hf hs ho
    hoffer hid htaker hu ha rd
  rcases midnightTakeBuyerUpdate hstack (takeBuyer_canonical ht) hf1
      (takePositionPrepareFrame_buyer frame evm offer id taker)
      (takePositionPrepareFrame_buyerPos frame evm offer id taker)
      (takePositionPrepareFrame_credit frame evm offer id taker) hs ho1 (by omega) hroot
      hfree1 hoffer1 hid1 hbuyer1 ha1 rd1 with
    ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨hx2, hf2, hs2, hp2, hfree2, aw2, k2, C2, ha2, rd2⟩
  · exact Or.inl ⟨hx1.run hx, hr⟩
  · exact Or.inr (Or.inl ⟨hx1.run hx, hr⟩)
  · have hsource2 {result : ExecResult}
        (hx : ExecBlock fork config
          (takeBuyerUpdateFrame (takePositionPrepareFrame frame evm offer id taker) evm offer id
            (takeBuyer offer taker) units)
          (takeBuyerUpdateState evm offer id (takeBuyer offer taker) units)
          (takeTransition.body.drop 33) result) :
        ExecBlock fork config frame evm (takeTransition.body.drop 27) result := by
      apply hx1.run
      rw [takeBuyerUpdate_shape]
      exact ExecBlock.consNormal hx2 hx
    have hload2 (off : UInt256) (hlo : 96 ≤ off.toNat) (hlim : off.toNat + 32 ≤ root.toNat)
        (hin : off.toNat + 32 ≤ (takePositionPrepareMemory mem offer id taker).size) :=
      hp2.load off hlo hlim hin
    have hoffer2 := (hload2 (UInt256.ofNat 384) (by decide)
      (by change 416 ≤ root.toNat; omega) (by change 416 ≤ _; omega)).trans hoffer1
    have hid2 := (hload2 (UInt256.ofNat 512) (by decide)
      (by change 544 ≤ root.toNat; omega) (by change 544 ≤ _; omega)).trans hid1
    have hseller2 := (hload2 (UInt256.ofNat 448) (by decide)
      (by change 480 ≤ root.toNat; omega) (by change 480 ≤ _; omega)).trans hseller1
    have ho2 := ho1.preserve (hp2.mono hheap)
    have hsLocal := (takeBuyerUpdateFrame_get _ evm offer id (takeBuyer offer taker) units
      "seller" (by decide)).trans
      (takePositionPrepareFrame_seller frame evm offer id taker)
    rcases midnightTakeSellerUpdate (by simp only [List.length_cons]; omega)
        (takeSeller_canonical ht) hf2 hsLocal hs2 ho2 (by omega) hroot hfree2 hoffer2 hid2
        hseller2 ha2 rd2 with
      ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨hx3, hf3, hs3, hp3, hfree3, aw3, k3, C3, ha3, rd3⟩
    · exact Or.inl ⟨hsource2 hx, hr⟩
    · exact Or.inr (Or.inl ⟨hsource2 hx, hr⟩)
    · refine Or.inr (Or.inr ⟨?_, hf3, hs3, hp2.trans hp3, hfree3, aw3, k3, C3, ha3, rd3⟩)
      intro result hx
      apply hsource2
      rw [takeSellerUpdate_shape]
      exact execBlock_append hx3 hx

end Benchmarks.Midnight
