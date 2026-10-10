import Benchmarks.CompoundIII.Comet.LiquidatorPointsData

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def liquidatorPointsPackedWord (p : LiquidatorPointsData) : UInt256 :=
  UInt256.lor
    (UInt256.lor
      (UInt256.lor
        (UInt256.land (UInt256.shiftLeft p.absorbed ⟨32⟩)
          (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨96⟩) (UInt256.shiftLeft ⟨1⟩ ⟨32⟩)))
        (UInt256.land p.absorbs ⟨4294967295⟩))
      (UInt256.land (UInt256.shiftLeft p.spend ⟨96⟩)
        (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨224⟩) (UInt256.shiftLeft ⟨1⟩ ⟨96⟩))))
    (UInt256.land (UInt256.shiftLeft p.reserved ⟨224⟩)
      (UInt256.lnot (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨224⟩) ⟨1⟩)))

set_option maxHeartbeats 1600000 in
theorem liquidatorPointsPacked_bits (old a b c d : BitVec 256) :
    let x := old % BitVec.ofNat 256 (256^0) +
      BitVec.ofNat 256 (256^0) * (a % BitVec.ofNat 256 (256^4)) +
      BitVec.ofNat 256 (256^4) * (old / BitVec.ofNat 256 (256^4))
    let y := x % BitVec.ofNat 256 (256^4) +
      BitVec.ofNat 256 (256^4) * (b % BitVec.ofNat 256 (256^8)) +
      BitVec.ofNat 256 (256^12) * (x / BitVec.ofNat 256 (256^12))
    let z := y % BitVec.ofNat 256 (256^12) +
      BitVec.ofNat 256 (256^12) * (c % BitVec.ofNat 256 (256^16)) +
      BitVec.ofNat 256 (256^28) * (y / BitVec.ofNat 256 (256^28))
    z % BitVec.ofNat 256 (256^28) +
      BitVec.ofNat 256 (256^28) * (d % BitVec.ofNat 256 (256^4)) =
    ((((b <<< 32) &&& BitVec.ofNat 256 (2^96-2^32)) |||
      (a &&& BitVec.ofNat 256 (2^32-1))) |||
      ((c <<< 96) &&& BitVec.ofNat 256 (2^224-2^96))) |||
      ((d <<< 224) &&& (~~~BitVec.ofNat 256 (2^224-1))) := by
  dsimp only
  bv_decide

theorem liquidatorPointsPacked_eq (old : UInt256) (p : LiquidatorPointsData) :
    packedWriteWord
      (packedWriteWord (packedWriteWord (packedWriteWord old p.absorbs 0 4)
        p.absorbed 4 8) p.spend 12 16) p.reserved 28 4 = liquidatorPointsPackedWord p := by
  let x : BitVec 256 := ⟨old.val⟩
  let a : BitVec 256 := ⟨p.absorbs.val⟩
  let b : BitVec 256 := ⟨p.absorbed.val⟩
  let c : BitVec 256 := ⟨p.spend.val⟩
  let d : BitVec 256 := ⟨p.reserved.val⟩
  have last (w t : BitVec 256) :
      packedWriteWord ⟨w.toFin⟩ ⟨t.toFin⟩ 28 4 =
      ⟨(w % BitVec.ofNat 256 (256^28) +
        BitVec.ofNat 256 (256^28) * (t % BitVec.ofNat 256 (256^4))).toFin⟩ := by
    unfold packedWriteWord
    rw [show (⟨w.toFin⟩ : UInt256).toNat / 256^(28+4) = 0 from Nat.div_eq_of_lt w.isLt,
      Nat.mul_zero, Nat.add_zero]
    apply congrArg UInt256.mk
    change (BitVec.ofNat 256 (w.toNat % 256^28 + 256^28 * (t.toNat % 256^4))).toFin = _
    rw [BitVec.ofNat_add, BitVec.ofNat_mul, bitvecOfNatMod w _ (by decide),
      bitvecOfNatMod t _ (by decide)]
  rw [packedWriteWord_bitvec x a 0 4 (by decide) (by decide) (by decide),
    packedWriteWord_bitvec _ b 4 8 (by decide) (by decide) (by decide),
    packedWriteWord_bitvec _ c 12 16 (by decide) (by decide) (by decide),
    last _ d, liquidatorPointsPacked_bits]
  simp only [liquidatorPointsPackedWord, UInt256.land, UInt256.lor, UInt256.lnot,
    BitVec.toFin_and, BitVec.toFin_or, BitVec.toFin_not]
  rfl

theorem storeLiquidatorPoints_eq (evm : State) (addr : AccountAddress)
    (p : LiquidatorPointsData) :
    storeLiquidatorPoints evm addr p =
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner (liquidatorSlot addr)
      (liquidatorPointsPackedWord p) := by
  unfold storeLiquidatorPoints
  change storePackedWord
    (storePackedWord
      (storePackedWord
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (liquidatorSlot addr)
          (packedWriteWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (liquidatorSlot addr))
            p.absorbs 0 4))
        (liquidatorSlot addr) p.absorbed 4 8)
      (liquidatorSlot addr) p.spend 12 16)
    (liquidatorSlot addr) p.reserved 28 4 = _
  rw [storePackedWord_after_modify evm _ _ _ _ (fun old ↦ packedWriteWord old p.absorbs 0 4)]
  rw [storePackedWord_after_modify evm _ _ _ _
    (fun old ↦ packedWriteWord (packedWriteWord old p.absorbs 0 4) p.absorbed 4 8)]
  rw [storePackedWord_after_modify evm _ _ _ _
    (fun old ↦ packedWriteWord (packedWriteWord (packedWriteWord old p.absorbs 0 4)
      p.absorbed 4 8) p.spend 12 16)]
  rw [liquidatorPointsPacked_eq]

theorem sourceState_liquidatorPoints {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (addr : AccountAddress) (p : LiquidatorPointsData) :
    SourceState s0 I
      (sstoreAccountMap I.codeOwner σ (liquidatorSlot addr) (liquidatorPointsPackedWord p))
      (storeLiquidatorPoints evm addr p) := by
  rw [storeLiquidatorPoints_eq]
  exact hs.readModifyWrite (liquidatorSlot addr) (fun _ ↦ liquidatorPointsPackedWord p)

end Benchmarks.CompoundIII.Comet
