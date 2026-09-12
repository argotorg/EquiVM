import Benchmarks.Dss.Clipper.TakeDynamicRemove
import Benchmarks.Dss.Clipper.YankVatEVM
import Benchmarks.Dss.Clipper.TakePostDogRemove

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 4000000 in
theorem RD.clipperTakeRemoveContinuationElim
    {P : Prop} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd8274 : RD code ee g s0 ⟨8274⟩
      (id :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      mem aw out (cA, σ) k C)
    (hid : id = clipperYankArgWord ee)
    (hmem : clipperTakeMemoryWF mem aw) (hperm : ee.perm = true)
    (onEmpty : solcSlotWord σ ee ⟨11⟩ = ⟨0⟩ → RDinvalid code g s0 → P)
    (onIdEq :
      ∀ hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩,
        (let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
         clipperYankArgWord ee =
           solcSlotWord σ ee (clipperYankActiveSlot lastIndex)) →
        (let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
         RDret code g s0
           (cA, sstoreAccountMap ee.codeOwner
             (clipperYankRemoveAccountMap σ ee lastIndex) ⟨13⟩ ⟨0⟩)
           ByteArray.empty) → P)
    (onIdNeJoinEmpty :
      ∀ hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩,
        (let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
         clipperYankArgWord ee ≠
           solcSlotWord σ ee (clipperYankActiveSlot lastIndex)) →
        (solcSlotWord σ ee (clipperYankSalesPosSlot ee)).toNat <
          (solcSlotWord σ ee ⟨11⟩).toNat →
        (let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
         let move := solcSlotWord σ ee (clipperYankActiveSlot lastIndex)
         let idx := solcSlotWord σ ee (clipperYankSalesPosSlot ee)
         solcSlotWord (clipperYankMoveAccountMap σ ee idx move) ee ⟨11⟩ = ⟨0⟩) →
        RDinvalid code g s0 → P)
    (onIdNeSuccess :
      ∀ hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩,
        (let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
         clipperYankArgWord ee ≠
           solcSlotWord σ ee (clipperYankActiveSlot lastIndex)) →
        (solcSlotWord σ ee (clipperYankSalesPosSlot ee)).toNat <
          (solcSlotWord σ ee ⟨11⟩).toNat →
        (let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
         let move := solcSlotWord σ ee (clipperYankActiveSlot lastIndex)
         let idx := solcSlotWord σ ee (clipperYankSalesPosSlot ee)
         solcSlotWord (clipperYankMoveAccountMap σ ee idx move) ee ⟨11⟩ ≠ ⟨0⟩) →
        (let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
         let move := solcSlotWord σ ee (clipperYankActiveSlot lastIndex)
         let idx := solcSlotWord σ ee (clipperYankSalesPosSlot ee)
         let σMove := clipperYankMoveAccountMap σ ee idx move
         let lastIndexAfter := solcSlotWord σMove ee ⟨11⟩ + UInt256.lnot ⟨0⟩
         RDret code g s0
           (cA, sstoreAccountMap ee.codeOwner
             (clipperYankRemoveAccountMap σMove ee lastIndexAfter) ⟨13⟩ ⟨0⟩)
           ByteArray.empty) → P)
    (onIdNeIndexOob :
      ∀ hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩,
        (let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
         clipperYankArgWord ee ≠
           solcSlotWord σ ee (clipperYankActiveSlot lastIndex)) →
        (solcSlotWord σ ee ⟨11⟩).toNat ≤
          (solcSlotWord σ ee (clipperYankSalesPosSlot ee)).toNat →
        RDinvalid code g s0 → P) : P := by
  subst id
  by_cases hlen : solcSlotWord σ ee ⟨11⟩ = ⟨0⟩
  · exact onEmpty hlen (RD.clipperTakeRemoveEmptyInvalid v hpatch rd8274 hlen)
  · let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
    by_cases hidEq : clipperYankArgWord ee =
        solcSlotWord σ ee (clipperYankActiveSlot lastIndex)
    · obtain ⟨_, _, rd8379⟩ := RD.clipperYankRemoveIdEqMoveToJoinGeneric
        (v := v) (hpatch := hpatch) (ret := (⟨5020⟩ : UInt256))
        (R := owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
          dataStart :: who :: max :: amt :: clipperYankArgWord ee :: [⟨502⟩, sel])
        rd8274 hlen (by simpa [lastIndex] using hidEq)
        (by simp only [List.length_cons, List.length_nil]; omega)
      have haw0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw :=
        clipperTakeMemoryWF_mstore_aw mem aw ⟨0⟩ hmem (by decide)
      have hret := RD.clipperTakeRemoveJoinToReturnSuccessWF v hpatch
        (by simpa [lastIndex, haw0] using rd8379) hlen
        (clipperTakeWordAt0MemoryWF ⟨11⟩ hmem) hperm
      exact onIdEq hlen (by simpa [lastIndex] using hidEq) hret
    · let move := solcSlotWord σ ee (clipperYankActiveSlot lastIndex)
      let idx := solcSlotWord σ ee (clipperYankSalesPosSlot ee)
      by_cases hidxBound : idx.toNat < (solcSlotWord σ ee ⟨11⟩).toNat
      · obtain ⟨_, _, rd8379, _⟩ := RD.clipperYankRemoveIdNeMoveToJoin
          (v := v) (hpatch := hpatch) (ret := (⟨5020⟩ : UInt256))
          (R := owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
            dataStart :: who :: max :: amt :: clipperYankArgWord ee :: [⟨502⟩, sel])
          rd8274 hlen (by simpa [lastIndex] using hidEq)
          (by
            have hactive := clipperTakeWordAt0MemoryWF (⟨11⟩ : UInt256) hmem
            exact le_trans (by decide : 64 ≤ 260) hactive.1)
          (by simpa [idx] using hidxBound)
          (by simp only [List.length_cons, List.length_nil]; omega) hperm
        let σMove := clipperYankMoveAccountMap σ ee idx move
        have hmoveMem := clipperTakeRemoveIdNeMoveMemoryWF
          (clipperYankArgWord ee) move hmem
        by_cases hlenAfter : solcSlotWord σMove ee ⟨11⟩ = ⟨0⟩
        · exact onIdNeJoinEmpty hlen (by simpa [lastIndex] using hidEq)
            (by simpa [idx] using hidxBound)
            (by simpa [lastIndex, move, idx, σMove] using hlenAfter)
            (RD.clipperTakeRemoveJoinEmptyInvalid v hpatch
              (by simpa [lastIndex, move, idx, σMove] using rd8379) hlenAfter)
        · have hret := RD.clipperTakeRemoveJoinToReturnSuccessWF v hpatch
            (by simpa [lastIndex, move, idx, σMove] using rd8379) hlenAfter
            (by simpa [lastIndex, move, idx] using hmoveMem) hperm
          exact onIdNeSuccess hlen (by simpa [lastIndex] using hidEq)
            (by simpa [idx] using hidxBound)
            (by simpa [lastIndex, move, idx, σMove] using hlenAfter)
            (by simpa [lastIndex, move, idx, σMove] using hret)
      · have hidxOob : (solcSlotWord σ ee ⟨11⟩).toNat ≤ idx.toNat :=
          Nat.le_of_not_gt hidxBound
        exact onIdNeIndexOob hlen (by simpa [lastIndex] using hidEq)
          (by simpa [idx] using hidxOob)
          (RD.clipperTakeRemoveIdNeMoveIndexOobInvalid v hpatch rd8274 hlen
            (by simpa [lastIndex] using hidEq)
            (by
              have hactive := clipperTakeWordAt0MemoryWF (⟨11⟩ : UInt256) hmem
              exact le_trans (by decide : 64 ≤ 260) hactive.1)
            (by simpa [idx] using hidxOob))

end Benchmarks.Dss.Clipper
