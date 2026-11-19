import Benchmarks.Midnight.PackedFields
import Reasoning.PackedStorage

/-! Packed uint32 writes, including their byte-level storage semantics. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

-- LIBRARY CANDIDATE: the uint32 counterparts of the generic packed uint48 helpers.
def packedUInt32Int : IntType := .uint ⟨32, by decide⟩
def packedUInt32Modulus : Int := (2 : Int) ^ 32
def packedUInt32Loc (slot : UInt256) (offset : Fin 32)
    (hbound : offset.val + 4 - 1 < 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 4, hbound := hbound, type := .int packedUInt32Int }
abbrev uint32Mask : UInt256 := ⟨4294967295⟩

theorem wordOfInt_emod_uint32 (w : UInt256) :
    EVM.wordOfInt (Int.ofNat w.toNat % packedUInt32Modulus) =
      UInt256.land w uint32Mask := by
  have hnonneg : 0 ≤ Int.ofNat w.toNat % packedUInt32Modulus := by
    exact Int.emod_nonneg _ (by norm_num [packedUInt32Modulus])
  have hcast : ((w.toNat % 2 ^ 32 : Nat) : Int) =
      Int.ofNat w.toNat % packedUInt32Modulus := by
    norm_num [packedUInt32Modulus, Int.natCast_mod]
  have htoNat : (Int.ofNat w.toNat % packedUInt32Modulus).toNat = w.toNat % 2 ^ 32 := by
    have h := congrArg Int.toNat hcast
    simpa using h.symm
  rw [wordOfInt_nonneg _ hnonneg]
  apply u256_inj
  change (Int.ofNat w.toNat % packedUInt32Modulus).toNat % EVM.twoPow 256 =
    (UInt256.land w uint32Mask).toNat
  rw [htoNat]
  rw [u256_land_toNat]
  change w.toNat % 2 ^ 32 % EVM.twoPow 256 =
    Nat.land w.toNat (2 ^ 32 - 1) % UInt256.size
  rw [nat_land_mask_eq_mod]
  simp [EVM.twoPow, UInt256.size]

def setUint32Offset0Word (old data : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot uint32Mask))
    (UInt256.land data uint32Mask)

theorem setUint32Offset0Word_toNat (old data : UInt256) :
    (setUint32Offset0Word old data).toNat =
      (UInt256.land data uint32Mask).toNat + (old.toNat / 2 ^ 32) * 2 ^ 32 := by
  unfold setUint32Offset0Word
  rw [u256_lor_toNat]
  have hhighMask :
      UInt256.lnot uint32Mask = UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 32) := by
    decide
  rw [hhighMask]
  rw [u256_land_comm old (UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 32))]
  rw [u256_land_high_mask_toNat old 32 (by norm_num)]
  rw [nat_lor_comm]
  have hlow : (UInt256.land data uint32Mask).toNat < 2 ^ 32 := by
    exact u256LandMaskToNatLtOfToNat data _ (by decide)
  rw [nat_lor_shift_add _ _ 32 hlow]
  have hsumLt :
      (UInt256.land data uint32Mask).toNat + old.toNat / 2 ^ 32 * 2 ^ 32 <
        UInt256.size := by
    have hq : old.toNat / 2 ^ 32 < 2 ^ 224 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 32 * 2 ^ 224 = (2 : Nat) ^ 256 by norm_num]
      change old.val.val < 2 ^ 256
      exact old.val.isLt
    have hlowle : (UInt256.land data uint32Mask).toNat ≤ 2 ^ 32 - 1 :=
      Nat.le_pred_of_lt hlow
    have hqle : old.toNat / 2 ^ 32 ≤ 2 ^ 224 - 1 := Nat.le_pred_of_lt hq
    have hqterm : old.toNat / 2 ^ 32 * 2 ^ 32 ≤ (2 ^ 224 - 1) * 2 ^ 32 :=
      Nat.mul_le_mul_right _ hqle
    have hmax : (2 ^ 32 - 1) + (2 ^ 224 - 1) * 2 ^ 32 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  rw [Nat.mod_eq_of_lt hsumLt]

theorem storageLocStore_uint32_offset0_word (evm : EVM.State) (slot data : UInt256) :
    storageLocStore evm (packedUInt32Loc slot ⟨0, by decide⟩ (by decide))
        (.int (Int.ofNat data.toNat % packedUInt32Modulus)) =
      some (Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint32Offset0Word (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          data)) := by
  unfold storageLocStore storageLocWriteWord packedUInt32Loc
  simp only [valueToWord, wordOfInt_emod_uint32, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (4 : Fin 33).val _ ++
        List.drop ((0 : Fin 32).val + (4 : Fin 33).val) _) =
      (setUint32Offset0Word (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        data).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (4 : Fin 33).val = 4 from rfl,
    List.take_zero, List.nil_append]
  rw [fromBytes'_append]
  rw [fromBytes'_take_wordLE_land_mask _ 4 (by norm_num)]
  rw [fromBytes'_drop_wordLE]
  have hlen4 :
      ((EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint32Mask)).1.take 4).length =
        4 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint32Mask)).2]
    norm_num
  rw [hlen4]
  rw [show 2 ^ (8 * 4) = (2 : Nat) ^ 32 by norm_num]
  rw [show 256 ^ 4 = (2 : Nat) ^ 32 by norm_num]
  rw [setUint32Offset0Word_toNat]
  have hclean : UInt256.land (UInt256.land data uint32Mask)
      (UInt256.ofNat (2 ^ 32 - 1)) = UInt256.land data uint32Mask := by
    exact maskTwice data _
  rw [hclean]
  ring

-- LIBRARY CANDIDATE: shift and shifted-mask preservation for bounded words.
theorem shiftLeft_toNat_of_noOverflow (word bits : UInt256) (hbits : bits.toNat < 256)
    (hfit : word.toNat * 2 ^ bits.toNat < UInt256.size) :
    (UInt256.shiftLeft word bits).toNat = word.toNat * 2 ^ bits.toNat := by
  unfold UInt256.shiftLeft
  rw [if_neg (show ¬ bits.val ≥ 256 by exact Nat.not_le.mpr hbits)]
  change (word.toNat <<< bits.toNat) % UInt256.size = _
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hfit]

-- LIBRARY CANDIDATE: shifting a clean masked word preserves the shifted mask.
theorem shiftLeft_land_mask (word : UInt256) (width bits : Nat)
    (hbits : bits < 256) (hwidth : width + bits < 256) (hword : word.toNat < 2 ^ width) :
    UInt256.land (UInt256.shiftLeft word (UInt256.ofNat bits))
      (UInt256.ofNat ((2 ^ width - 1) * 2 ^ bits)) =
      UInt256.shiftLeft word (UInt256.ofNat bits) := by
  have hb : (UInt256.ofNat bits).toNat = bits := ulit_toNat' bits (by change bits < 2 ^ 256; omega)
  have hfit : word.toNat * 2 ^ bits < UInt256.size := by
    apply lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hword (by positivity))
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hwidth)
  have hmaskfit : (2 ^ width - 1) * 2 ^ bits < UInt256.size := by
    apply lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (by positivity) (by decide))
      (by positivity))
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hwidth)
  apply u256_inj
  rw [uland_toNat, shiftLeft_toNat_of_noOverflow word _ (by rw [hb]; exact hbits)
    (by rw [hb]; exact hfit), hb, ulit_toNat' _ hmaskfit]
  simp only [← Nat.shiftLeft_eq]
  rw [← Nat.shiftLeft_and_distrib]
  change Nat.land word.toNat (2 ^ width - 1) <<< bits = _
  rw [nat_land_mask_eq_mod, Nat.mod_eq_of_lt hword]

end Benchmarks.Midnight
