import Benchmarks.Dss.Clipper.TakeChostRevert

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 2000000 in
theorem RD.clipperTakeOweLeTabElim
    {P : Prop} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price slice tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (rd4057 : RD code ee g s0 ⟨4057⟩
      (UInt256.mul price slice :: slice :: ⟨0⟩ :: tab :: lot ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hle : (UInt256.mul price slice).toNat ≤ tab.toNat)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 30 ≤ 1024)
    (onPlainEq :
      tab.toNat ≤ (UInt256.mul price slice).toNat →
      (∃ k' C', RD code ee g s0 ⟨4223⟩
        (slice :: UInt256.mul price slice :: tab :: lot :: price :: tic :: packed ::
          stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
        mem (UInt256.ofNat 7) rdata (cA, σ) k' C') → P)
    (onPlainSliceGe :
      (UInt256.mul price slice).toNat < tab.toNat → lot.toNat ≤ slice.toNat →
      (∃ k' C', RD code ee g s0 ⟨4223⟩
        (slice :: UInt256.mul price slice :: tab :: lot :: price :: tic :: packed ::
          stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
        mem (UInt256.ofNat 7) rdata (cA, σ) k' C') → P)
    (onChostNoAdjust :
      (UInt256.mul price slice).toNat < tab.toNat →
      slice.toNat < lot.toNat →
      (solcSlotWord σ ee ⟨9⟩).toNat ≤
        (UInt256.sub tab (UInt256.mul price slice)).toNat →
      (∃ k' C', RD code ee g s0 ⟨4223⟩
        (slice :: UInt256.mul price slice :: tab :: lot :: price :: tic :: packed ::
          stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
        mem (UInt256.ofNat 7) rdata (cA, σ) k' C') → P)
    (onChostAdjust :
      (UInt256.mul price slice).toNat < tab.toNat →
      slice.toNat < lot.toNat →
      (UInt256.sub tab (UInt256.mul price slice)).toNat <
        (solcSlotWord σ ee ⟨9⟩).toNat →
      (solcSlotWord σ ee ⟨9⟩).toNat < tab.toNat →
      price ≠ ⟨0⟩ →
      (∃ k' C', RD code ee g s0 ⟨4223⟩
        (UInt256.div (UInt256.sub tab (solcSlotWord σ ee ⟨9⟩)) price ::
          UInt256.sub tab (solcSlotWord σ ee ⟨9⟩) :: tab :: lot :: price :: tic ::
          packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
        mem (UInt256.ofNat 7) rdata (cA, σ) k' C') → P)
    (onNoPartial :
      (UInt256.mul price slice).toNat < tab.toNat →
      slice.toNat < lot.toNat →
      (UInt256.sub tab (UInt256.mul price slice)).toNat <
        (solcSlotWord σ ee ⟨9⟩).toNat →
      tab.toNat ≤ (solcSlotWord σ ee ⟨9⟩).toNat →
      RDrev code g s0 → P) : P := by
  by_cases heq : tab.toNat ≤ (UInt256.mul price slice).toNat
  · exact onPlainEq heq
      (RD.clipperTakeOweEqTabToJoin v hpatch rd4057 hle heq hov)
  · have hlt : (UInt256.mul price slice).toNat < tab.toNat :=
      Nat.lt_of_not_ge heq
    by_cases hslice : slice.toNat < lot.toNat
    · by_cases hchost : (solcSlotWord σ ee ⟨9⟩).toNat ≤
          (UInt256.sub tab (UInt256.mul price slice)).toNat
      · exact onChostNoAdjust hlt hslice hchost
          (RD.clipperTakeOweLtTabSliceLtLotChostGeToJoin v hpatch rd4057 hle hlt
            hslice hchost hov)
      · have hremaining : (UInt256.sub tab (UInt256.mul price slice)).toNat <
            (solcSlotWord σ ee ⟨9⟩).toNat := Nat.lt_of_not_ge hchost
        by_cases htabChost : (solcSlotWord σ ee ⟨9⟩).toNat < tab.toNat
        · have hprice : price ≠ ⟨0⟩ := by
            intro hp
            subst price
            have hmulZero : UInt256.mul (⟨0⟩ : UInt256) slice = ⟨0⟩ :=
              Reasoning.Theory.clipperMul_zero_left slice
            rw [hmulZero] at hlt hremaining
            have hsubZero : (UInt256.sub tab (⟨0⟩ : UInt256)).toNat = tab.toNat := by
              rw [usub_toNat (by simp)]
              simp
            rw [hsubZero] at hremaining
            omega
          exact onChostAdjust hlt hslice hremaining htabChost hprice
            (RD.clipperTakeOweLtTabSliceLtLotChostAdjustToJoin v hpatch rd4057 hle
              hlt hslice hremaining htabChost hprice hov)
        · have htabLeChost : tab.toNat ≤ (solcSlotWord σ ee ⟨9⟩).toNat :=
            Nat.le_of_not_gt htabChost
          exact onNoPartial hlt hslice hremaining htabLeChost
            (RD.clipperTakeOweLtTabSliceLtLotNoPartialPurchaseReverts v hpatch rd4057
              hle hlt hslice hremaining htabLeChost hmem hread64 hov)
    · have hsliceGe : lot.toNat ≤ slice.toNat := Nat.le_of_not_gt hslice
      exact onPlainSliceGe hlt hsliceGe
        (RD.clipperTakeOweLtTabSliceGeLotToJoin v hpatch rd4057 hle hlt hsliceGe hov)

end Benchmarks.Dss.Clipper
