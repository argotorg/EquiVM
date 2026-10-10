import Benchmarks.Morpho.MetaMorphoV1_1.Mutation

/-! Setting a packed boolean at any byte offset. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

-- GENERALIZES Reasoning.PackedStorage.setBoolTrueOffset20Word to all byte offsets.
def setBoolByteTrueWord (old : UInt256) (offset : Fin 32) : UInt256 :=
  UInt256.lor
    (UInt256.land old (UInt256.lnot (UInt256.shiftLeft ⟨255⟩ (UInt256.ofNat (8 * offset.val)))))
    (UInt256.shiftLeft ⟨1⟩ (UInt256.ofNat (8 * offset.val)))

private theorem boolByteMaskFacts : ∀ offset : Fin 32,
    (UInt256.lnot (UInt256.shiftLeft ⟨255⟩ (UInt256.ofNat (8 * offset.val)))).toNat =
      (2 ^ (8 * offset.val) - 1) ||| (2 ^ 256 - 2 ^ (8 * (offset.val + 1))) ∧
    (UInt256.shiftLeft ⟨1⟩ (UInt256.ofNat (8 * offset.val))).toNat =
      2 ^ (8 * offset.val) := by decide +kernel

theorem setBoolByteTrueWord_toNat (old : UInt256) (offset : Fin 32) :
    (setBoolByteTrueWord old offset).toNat =
      old.toNat % 2 ^ (8 * offset.val) + 2 ^ (8 * offset.val) +
        old.toNat / 2 ^ (8 * (offset.val + 1)) * 2 ^ (8 * (offset.val + 1)) := by
  obtain ⟨hm, hp⟩ := boolByteMaskFacts offset
  have hb : 8 * (offset.val + 1) ≤ 256 := by have := offset.isLt; omega
  rw [setBoolByteTrueWord, u256_lor_toNat_exact, uland_toNat, hm, hp,
    Nat.and_or_distrib_left]
  change Nat.lor
    (Nat.lor (Nat.land old.toNat (2 ^ (8 * offset.val) - 1))
      (Nat.land old.toNat (2 ^ 256 - 2 ^ (8 * (offset.val + 1)))))
    (2 ^ (8 * offset.val)) = _
  rw [nat_land_mask_eq_mod, natLandClearLow old.toNat _ hb old.val.isLt]
  rw [show Nat.lor
      (Nat.lor (old.toNat % 2 ^ (8 * offset.val))
        (old.toNat / 2 ^ (8 * (offset.val + 1)) * 2 ^ (8 * (offset.val + 1))))
      (2 ^ (8 * offset.val)) =
      Nat.lor (Nat.lor (old.toNat % 2 ^ (8 * offset.val)) (2 ^ (8 * offset.val)))
        (old.toNat / 2 ^ (8 * (offset.val + 1)) * 2 ^ (8 * (offset.val + 1))) from
    Nat.or_right_comm _ _ _]
  have hlo : old.toNat % 2 ^ (8 * offset.val) < 2 ^ (8 * offset.val) :=
    Nat.mod_lt _ (by positivity)
  have hbit : Nat.lor (old.toNat % 2 ^ (8 * offset.val)) (2 ^ (8 * offset.val)) =
      old.toNat % 2 ^ (8 * offset.val) + 2 ^ (8 * offset.val) := by
    simpa only [Nat.one_mul] using nat_lor_shift_add _ 1 (8 * offset.val) hlo
  rw [hbit]
  apply nat_lor_shift_add
  rw [show 8 * (offset.val + 1) = 8 * offset.val + 8 by omega, Nat.pow_add]
  norm_num only [show (2 : Nat) ^ 8 = 256 by decide]
  have : 0 < 2 ^ (8 * offset.val) := by positivity
  omega

-- GENERALIZES Reasoning.PackedStorage.storageLocStore_bool_true_offset20 to every byte offset.
theorem storageLocStore_bool_true_at (evm : State) (slot : UInt256) (offset : Fin 32) :
    storageLocStore evm (packedBoolLocAt slot offset) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setBoolByteTrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) offset)) := by
  unfold storageLocStore storageLocWriteWord packedBoolLocAt
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take offset.val ++
      (EVM.Word.toBytesLEWithSizeProof true.toUInt256).1.take 1 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop (offset.val + 1)) = _
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE, setBoolByteTrueWord_toNat]
  simp only [List.length_append, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2,
    (EVM.Word.toBytesLEWithSizeProof true.toUInt256).2,
    Nat.min_eq_left (by have := offset.isLt; omega : offset.val ≤ 32)]
  change _ % 256 ^ offset.val + 2 ^ (8 * offset.val) * 1 +
    2 ^ (8 * (offset.val + 1)) * (_ / 256 ^ (offset.val + 1)) = _
  have hp (n : Nat) : 2 ^ (8 * n) = 256 ^ n := by rw [Nat.pow_mul]
  simp only [hp, Nat.mul_one]
  ac_rfl

end Benchmarks.Morpho.MetaMorphoV1_1
