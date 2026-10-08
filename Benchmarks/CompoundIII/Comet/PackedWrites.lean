import Benchmarks.CompoundIII.Comet.PackedFields
import Std.Tactic.BVDecide

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: the arithmetic form of replacing a byte-aligned packed field.
def packedWriteWord (old data : UInt256) (offset size : Nat) : UInt256 :=
  UInt256.ofNat (old.toNat % 256^offset + 256^offset * (data.toNat % 256^size) +
    256^(offset + size) * (old.toNat / 256^(offset + size)))

theorem packedWriteBytes (old data : UInt256) (offset size : Nat)
    (hoff : offset ≤ 32) (hsize : size ≤ 32) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof old).1.take offset ++
      (EVM.Word.toBytesLEWithSizeProof data).1.take size ++
      (EVM.Word.toBytesLEWithSizeProof old).1.drop (offset + size)) =
      old.toNat % 256^offset + 256^offset * (data.toNat % 256^size) +
        256^(offset + size) * (old.toNat / 256^(offset + size)) := by
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  simp only [List.length_append, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof old).2, (EVM.Word.toBytesLEWithSizeProof data).2,
    Nat.min_eq_left hoff, Nat.min_eq_left hsize, Nat.pow_mul]

-- LIBRARY CANDIDATE: writes to an arbitrary byte-aligned scalar storage location.
theorem storageLocStore_packed_int (evm : EVM.State) (slot data : UInt256)
    (offset : Fin 32) (size : Fin 33) (ty : ElemType)
    {hbound : offset.val + size.val - 1 < 32} :
    storageLocStore evm
      { slot := slot, offset := offset, size := size, hbound := hbound, type := ty }
      (.int (Int.ofNat data.toNat)) =
    some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (packedWriteWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        data offset.val size.val)) := by
  unfold storageLocStore storageLocWriteWord
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind]
  congr 2
  unfold packedWriteWord
  rw [← packedWriteBytes _ _ _ _ (by omega) (by omega)]
  exact (u256_ofNat_toNat _).symm

-- LIBRARY CANDIDATE: lift natural remainder and division into fixed-width words.
theorem bitvecOfNatMod {width : Nat} (x : BitVec width) (n : Nat) (hn : n < 2^width) :
    BitVec.ofNat width (x.toNat % n) = x % BitVec.ofNat width n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le _ _) x.isLt)]

theorem bitvecOfNatDiv {width : Nat} (x : BitVec width) (n : Nat) (hn : n < 2^width) :
    BitVec.ofNat width (x.toNat / n) = x / BitVec.ofNat width n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)]

theorem packedWriteWord_bitvec (old data : BitVec 256) (offset size : Nat)
    (hoff : offset < 32) (hsize : size < 32) (hend : offset + size < 32) :
    packedWriteWord ⟨old.toFin⟩ ⟨data.toFin⟩ offset size =
      ⟨(old % BitVec.ofNat 256 (256^offset) +
        BitVec.ofNat 256 (256^offset) * (data % BitVec.ofNat 256 (256^size)) +
        BitVec.ofNat 256 (256^(offset + size)) *
          (old / BitVec.ofNat 256 (256^(offset + size)))).toFin⟩ := by
  have hpow (n : Nat) (hn : n < 32) : 256^n < 2^256 := by
    change (2^8)^n < 2^256
    rw [← Nat.pow_mul]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  apply congrArg UInt256.mk
  change (BitVec.ofNat 256 _).toFin = _
  simp only [show (⟨old.toFin⟩ : UInt256).toNat = old.toNat from rfl,
    show (⟨data.toFin⟩ : UInt256).toNat = data.toNat from rfl]
  rw [BitVec.ofNat_add, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_mul,
    bitvecOfNatMod old _ (hpow _ hoff), bitvecOfNatMod data _ (hpow _ hsize),
    bitvecOfNatDiv old _ (hpow _ hend)]

end Benchmarks.CompoundIII.Comet
