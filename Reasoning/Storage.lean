import Reasoning.EVMWord
import Reasoning.Memory
import Reasoning.Stepping

/-!
# Storage — ordered-map (`Batteries.RBMap`) facts for EVM storage maps

Generic lookup/update facts for the red-black-tree maps that back EVM storage (`Storage`) and the
account map (`AccountMap`), independent of any contract or keccak layout: a write at one slot
preserves lookup at a different slot.  The `RBNode`/`RBMap` `find?_erase_ne` machinery fills the gap
left by `Batteries` (which ships `find?_insert_of_ne` but no erase analogue).  The `UInt256`
`compare` instances these rely on live in `Reasoning.EVMWord`.
-/

open Ethereum Ethereum.EVM Solm

namespace Reasoning.Theory

theorem storage_findD_insert_ne (storage : Storage) (readSlot writeSlot val default : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.insert writeSlot val).findD readSlot default =
      storage.findD readSlot default := by
  unfold Batteries.RBMap.findD
  rw [Batteries.RBMap.find?_insert_of_ne]
  intro hcmp
  exact hne (Std.LawfulEqCmp.eq_of_compare hcmp)

theorem keyValueToWord_address_of_canonical (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    keyValueToWord (.address (AccountAddress.ofNat w.toNat)) = w := by
  apply u256_inj
  unfold keyValueToWord AccountAddress.ofNat
  exact Nat.mod_eq_of_lt (by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)

theorem keyValueToWord_address (a : AccountAddress) :
    keyValueToWord (.address a) = UInt256.ofNat a.val := by
  apply u256_inj
  simp [keyValueToWord, UInt256.ofNat]
  exact (Nat.mod_eq_of_lt
    (lt_of_lt_of_le a.isLt (show AccountAddress.size ≤ UInt256.size from by decide))).symm

theorem keyValueToWord_uint256 (w : UInt256) :
    keyValueToWord (.int (Int.ofNat w.toNat)) = w := by
  unfold keyValueToWord EVM.wordOfInt
  simp only [Int.ofNat_eq_natCast]
  apply u256_inj
  show w.toNat % EVM.twoPow 256 = w.toNat
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le w.val.isLt (by decide))

theorem keyValueToWord_fixedBytes32 (w : UInt256) :
    keyValueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE w)) = w := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  simp [keyValueToWord, hlen]
  apply u256_inj
  have hfrom : fromBytesBigEndian (EVM.Word.toBytesBE w) = w.toNat := by
    have h := congrArg fromByteArrayBigEndian (word_toBytesBE_toByteArray_eq_toByteArray w)
    simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
      h.trans (fromByteArrayBigEndian_toByteArray w)
  rw [EVM.Word.ofNat, hfrom]
  exact Nat.mod_eq_of_lt w.val.isLt

/-! ## Full-slot uint256 storage -/

def uint256Loc (slot : UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide,
    type := .int (.uint ⟨256, by decide⟩) }

theorem storageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint256Loc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  have htake :
      (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0 (32 : Fin 33).val =
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1 := by
    rw [List.extract_eq_take_drop, List.drop_zero]
    exact List.take_of_length_le (by
      rw [(EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
      norm_num)
  unfold storageLocLoad uint256Loc wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  rw [htake, fromBytes'_toBytesLEWithSizeProof]
  rfl

theorem storageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (uint256Loc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  unfold storageLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof val).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = val.toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

/-! ## Full-slot bytes32 storage -/

def bytes32Loc (slot : UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide,
    type := .bytes ⟨31, by decide⟩ }

theorem storageLocLoad_bytes32 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (bytes32Loc slot) =
      .fixedBytes ⟨31, by decide⟩
        (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  have htake :
      (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0 (32 : Fin 33).val =
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1 := by
    rw [List.extract_eq_take_drop, List.drop_zero]
    exact List.take_of_length_le (by
      rw [(EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
      norm_num)
  unfold storageLocLoad bytes32Loc wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  simp only [show 32 - (31 + 1) = 0 by norm_num, List.drop_zero]
  congr
  rw [htake]
  exact fromBytes'_toBytesLEWithSizeProof _

theorem storageLocStore_bytes32 (evm : EVM.State) (slot word : UInt256) (v : Value)
    (hval : valueToWord v = some word) :
    storageLocStore evm (bytes32Loc slot) v =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot word) := by
  unfold storageLocStore storageLocWriteWord bytes32Loc
  simp only [hval, bind, Option.bind]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof word).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = word.toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

/-! ## Packed bool storage at byte offset 0 -/

def boolOffset0Loc (slot : UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 1, hbound := by decide, type := .bool }

def setBoolOffset0Word (old word : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot ⟨255⟩))
    (UInt256.isZero (UInt256.isZero word))

theorem storageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (boolOffset0Loc slot) =
      wordToElem .bool
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  unfold storageLocLoad boolOffset0Loc
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 1) = _
  rw [fromBytes'_take_wordLE_land_mask (n := 1) _ (by decide)]
  rfl

theorem storageLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm (boolOffset0Loc slot) = .bool false := by
  rw [storageLocLoad_bool_offset0 evm slot]
  simp [wordToElem, hzero]

theorem storageLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm (boolOffset0Loc slot) = .bool true := by
  rw [storageLocLoad_bool_offset0 evm slot]
  have hbeq :
      ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩).val == 0) =
        false := by
    rw [beq_eq_false_iff_ne]
    intro hval
    apply hnz
    apply u256_inj
    simpa [UInt256.toNat] using hval
  simp [wordToElem, hbeq]

theorem natLandClearLow8 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 : Nat) ^ 256 - 2 ^ 8) = (n / 2 ^ 8) * 2 ^ 8 := by
  simpa using natLandClearLow n 8 (by norm_num) hn

theorem natLorShift8One (q : Nat) : Nat.lor (q * 2 ^ 8) 1 = 1 + q * 2 ^ 8 := by
  rw [nat_lor_comm, nat_lor_shift_add 1 q 8 (by norm_num)]

theorem packedSetTrueNat_lt_size (n : Nat) (hn : n < UInt256.size) :
    1 + 256 * (n / 256) < UInt256.size := by
  have hq : n / 256 < 2 ^ 248 := by
    norm_num [UInt256.size] at hn ⊢
    omega
  have hmul : 256 * (n / 256) ≤ 256 * (2 ^ 248 - 1) :=
    Nat.mul_le_mul_left 256 (Nat.le_pred_of_lt hq)
  norm_num [UInt256.size] at hmul ⊢
  omega

theorem packedSetTrueWord_eq (w : UInt256) :
    UInt256.lor (UInt256.land w (UInt256.lnot ⟨255⟩)) ⟨1⟩ =
      UInt256.ofNat (1 + 256 * (w.toNat / 256)) := by
  apply u256_inj
  unfold UInt256.lor UInt256.land UInt256.toNat Fin.lor Fin.land
  change (Nat.lor ((Nat.land w.val.val (UInt256.lnot (⟨255⟩ : UInt256)).toNat) %
      UInt256.size) 1) %
      UInt256.size = (1 + 256 * (w.toNat / 256)) % UInt256.size
  have hlnot : (UInt256.lnot (⟨255⟩ : UInt256)).toNat = 2 ^ 256 - 2 ^ 8 := by
    native_decide
  rw [hlnot]
  change (Nat.lor ((Nat.land w.toNat (2 ^ 256 - 2 ^ 8)) % UInt256.size) 1) %
      UInt256.size = (1 + 256 * (w.toNat / 256)) % UInt256.size
  have hwlt : w.toNat < 2 ^ 256 := by
    change w.val.val < 2 ^ 256
    simpa [UInt256.size] using w.val.isLt
  have hland_lt : Nat.land w.toNat (2 ^ 256 - 2 ^ 8) < UInt256.size := by
    rw [natLandClearLow8 w.toNat hwlt]
    exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) w.val.isLt
  rw [Nat.mod_eq_of_lt hland_lt]
  rw [natLandClearLow8 w.toNat hwlt]
  rw [show 256 = 2 ^ 8 by norm_num]
  rw [Nat.mul_comm (2 ^ 8) (w.toNat / 2 ^ 8)]
  rw [natLorShift8One]

theorem packedSetTrueWord_toNat (w : UInt256) :
    (UInt256.lor (UInt256.land w (UInt256.lnot ⟨255⟩)) ⟨1⟩).toNat =
      1 + 256 * (w.toNat / 256) := by
  rw [packedSetTrueWord_eq]
  exact ulit_toNat' _ (packedSetTrueNat_lt_size w.toNat w.val.isLt)

theorem packedSetFalseWord_eq (w : UInt256) :
    UInt256.land w (UInt256.lnot ⟨255⟩) =
      UInt256.ofNat (256 * (w.toNat / 256)) := by
  apply u256_inj
  rw [u256_land_toNat]
  have hlnot : (UInt256.lnot (⟨255⟩ : UInt256)).toNat = 2 ^ 256 - 2 ^ 8 := by
    native_decide
  rw [hlnot]
  have hwlt : w.toNat < 2 ^ 256 := by
    change w.val.val < 2 ^ 256
    simpa [UInt256.size] using w.val.isLt
  rw [natLandClearLow8 w.toNat hwlt]
  have hlt : w.toNat / 2 ^ 8 * 2 ^ 8 < UInt256.size :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) w.val.isLt
  rw [Nat.mod_eq_of_lt hlt]
  have hlt' : 256 * (w.toNat / 256) < UInt256.size := by
    simpa [Nat.mul_comm] using hlt
  rw [show 2 ^ 8 = 256 by norm_num]
  rw [Nat.mul_comm (w.toNat / 256) 256]
  rw [ulit_toNat' _ hlt']

theorem packedSetFalseWord_toNat (w : UInt256) :
    (UInt256.land w (UInt256.lnot ⟨255⟩)).toNat = 256 * (w.toNat / 256) := by
  rw [packedSetFalseWord_eq]
  have hlt : 256 * (w.toNat / 256) < UInt256.size := by
    have hle : 256 * (w.toNat / 256) ≤ w.toNat :=
      Nat.mul_div_le w.toNat 256
    exact lt_of_le_of_lt hle w.val.isLt
  exact ulit_toNat' _ hlt

theorem storageLocStore_bool_true_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (boolOffset0Loc slot) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.lnot ⟨255⟩)) ⟨1⟩)) := by
  unfold storageLocStore storageLocWriteWord boolOffset0Loc
  simp only [valueToWord, Bool.toUInt256_true, bind, Option.bind]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (⟨1⟩ : UInt256)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (1 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (1 : Fin 33).val) _) =
        (UInt256.lor
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.lnot ⟨255⟩)) ⟨1⟩).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (1 : Fin 33).val = 1 from rfl,
    List.take_zero, List.nil_append]
  rw [show List.take 1 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)).1 =
      [1] by
        native_decide]
  rw [fromBytes'_append, fromBytes'_drop_wordLE]
  simp [fromBytes']
  rw [packedSetTrueWord_toNat]

theorem storageLocStore_bool_false_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (boolOffset0Loc slot) (.bool false) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.lnot ⟨255⟩))) := by
  unfold storageLocStore storageLocWriteWord boolOffset0Loc
  simp only [valueToWord, Bool.toUInt256_false, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (1 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (1 : Fin 33).val) _) =
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.lnot ⟨255⟩)).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (1 : Fin 33).val = 1 from rfl,
    List.take_zero, List.nil_append]
  rw [show List.take 1 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).1 =
      [0] by
        native_decide]
  rw [fromBytes'_append, fromBytes'_drop_wordLE]
  simp [fromBytes']
  rw [packedSetFalseWord_toNat]

theorem storageLocStore_bool_word_offset0 (evm : EVM.State) (slot word : UInt256) :
    storageLocStore evm (boolOffset0Loc slot) (wordToElem .bool word) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setBoolOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) word)) := by
  by_cases hzero : word = ⟨0⟩
  · subst hzero
    have hbool : UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ := by
      native_decide
    simp only [wordToElem, beq_self_eq_true, ↓reduceIte]
    simpa [setBoolOffset0Word, hbool, u256_lor_zero] using
      storageLocStore_bool_false_offset0 evm slot
  · have hbeq : (word.val == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hval
      apply hzero
      apply u256_inj
      simpa [UInt256.toNat] using hval
    have hiszero : UInt256.isZero word = ⟨0⟩ := isZero_eq_zero_of_ne hzero
    simp only [wordToElem, hbeq, Bool.false_eq_true, ↓reduceIte]
    simpa [setBoolOffset0Word, hiszero] using storageLocStore_bool_true_offset0 evm slot

private theorem rbnode_append_toList {α : Type u} (l r : Batteries.RBNode α) :
    (l.append r).toList = l.toList ++ r.toList := by
  fun_induction Batteries.RBNode.append l r <;> simp [List.append_assoc]
  case case3 a1 x1 b1 c y d a x b h ih1 =>
    have hnode : a.toList ++ x :: b.toList = b1.toList ++ c.toList := by
      simpa [h] using ih1
    simpa [List.append_assoc] using congrArg (fun xs => xs ++ (y :: d.toList)) hnode
  case case4 ih1 =>
    rw [ih1, List.append_assoc]
  case case5 a1 x1 b1 c y d a x b h ih1 =>
    have hnode : a.toList ++ x :: b.toList = b1.toList ++ c.toList := by
      simpa [h] using ih1
    simpa [List.append_assoc] using congrArg (fun xs => xs ++ (y :: d.toList)) hnode
  case case6 ih1 =>
    rw [ih1, List.append_assoc]
  case case7 ih1 =>
    rw [ih1]
    simp [List.append_assoc]
  case case8 ih1 =>
    simpa using ih1

private theorem rbnode_mem_of_mem_append {α : Type u} {x : α} {l r : Batteries.RBNode α}
    (h : x ∈ l.append r) : x ∈ l ∨ x ∈ r := by
  rw [← Batteries.RBNode.mem_toList] at h
  rw [rbnode_append_toList] at h
  simpa [Batteries.RBNode.mem_toList] using h

private theorem rbnode_mem_append_of_mem {α : Type u} {x : α} {l r : Batteries.RBNode α}
    (h : x ∈ l ∨ x ∈ r) : x ∈ l.append r := by
  rw [← Batteries.RBNode.mem_toList]
  rw [rbnode_append_toList]
  simpa [Batteries.RBNode.mem_toList] using h

private theorem rbnode_mem_of_mem_balLeft {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l.balLeft v r) :
    x ∈ l ∨ x = v ∨ x ∈ r := by
  rw [← Batteries.RBNode.mem_toList] at h
  rw [Batteries.RBNode.balLeft_toList] at h
  simpa [Batteries.RBNode.mem_toList] using h

private theorem rbnode_mem_balLeft_of_mem {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l ∨ x = v ∨ x ∈ r) : x ∈ l.balLeft v r := by
  rw [← Batteries.RBNode.mem_toList]
  rw [Batteries.RBNode.balLeft_toList]
  simpa [Batteries.RBNode.mem_toList] using h

private theorem rbnode_mem_of_mem_balRight {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l.balRight v r) :
    x ∈ l ∨ x = v ∨ x ∈ r := by
  rw [← Batteries.RBNode.mem_toList] at h
  rw [Batteries.RBNode.balRight_toList] at h
  simpa [Batteries.RBNode.mem_toList] using h

private theorem rbnode_mem_balRight_of_mem {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l ∨ x = v ∨ x ∈ r) : x ∈ l.balRight v r := by
  rw [← Batteries.RBNode.mem_toList]
  rw [Batteries.RBNode.balRight_toList]
  simpa [Batteries.RBNode.mem_toList] using h

private theorem rbnode_mem_node_of_left {α : Type u} {x y : α} {c : Batteries.RBColor}
    {a b : Batteries.RBNode α} (h : x ∈ a) : x ∈ Batteries.RBNode.node c a y b := by
  exact Or.inr (Or.inl h)

private theorem rbnode_mem_node_of_right {α : Type u} {x y : α} {c : Batteries.RBColor}
    {a b : Batteries.RBNode α} (h : x ∈ b) : x ∈ Batteries.RBNode.node c a y b := by
  exact Or.inr (Or.inr h)

private theorem rbnode_mem_of_mem_del {α : Type u} {x : α} (cut : α → Ordering) :
    ∀ {t : Batteries.RBNode α}, x ∈ Batteries.RBNode.del cut t → x ∈ t
  | .nil, h => by cases h
  | .node c a y b, h => by
      unfold Batteries.RBNode.del at h
      cases hcut : cut y <;> simp [hcut] at h
      · cases hblack : Batteries.RBNode.isBlack a <;> simp [hblack] at h
        · rcases h with hy | hrest
          · exact Or.inl hy
          · rcases hrest with hdel | hb
            · exact rbnode_mem_node_of_left (rbnode_mem_of_mem_del cut hdel)
            · exact rbnode_mem_node_of_right hb
        · rcases rbnode_mem_of_mem_balLeft h with hdel | hrest
          · exact rbnode_mem_node_of_left (rbnode_mem_of_mem_del cut hdel)
          · rcases hrest with hy | hb
            · exact Or.inl hy
            · exact rbnode_mem_node_of_right hb
      · rcases rbnode_mem_of_mem_append h with ha | hb
        · exact rbnode_mem_node_of_left ha
        · exact rbnode_mem_node_of_right hb
      · cases hblack : Batteries.RBNode.isBlack b <;> simp [hblack] at h
        · rcases h with hy | hrest
          · exact Or.inl hy
          · rcases hrest with ha | hdel
            · exact rbnode_mem_node_of_left ha
            · exact rbnode_mem_node_of_right (rbnode_mem_of_mem_del cut hdel)
        · rcases rbnode_mem_of_mem_balRight h with ha | hrest
          · exact rbnode_mem_node_of_left ha
          · rcases hrest with hy | hdel
            · exact Or.inl hy
            · exact rbnode_mem_node_of_right (rbnode_mem_of_mem_del cut hdel)

private theorem rbnode_mem_del_of_mem_ne {α : Type u} {x : α} (cut : α → Ordering) :
    ∀ {t : Batteries.RBNode α}, x ∈ t → cut x ≠ .eq → x ∈ Batteries.RBNode.del cut t
  | .nil, h, _ => by cases h
  | .node c a y b, h, hne => by
      unfold Batteries.RBNode.del
      cases hcut : cut y <;> simp
      · cases hblack : Batteries.RBNode.isBlack a <;> simp
        · rcases h with hy | hrest
          · exact Or.inl hy
          · rcases hrest with ha | hb
            · exact Or.inr (Or.inl (rbnode_mem_del_of_mem_ne cut ha hne))
            · exact Or.inr (Or.inr hb)
        · rcases h with hy | hrest
          · exact rbnode_mem_balLeft_of_mem (Or.inr (Or.inl hy))
          · rcases hrest with ha | hb
            · exact rbnode_mem_balLeft_of_mem
                (Or.inl (rbnode_mem_del_of_mem_ne cut ha hne))
            · exact rbnode_mem_balLeft_of_mem (Or.inr (Or.inr hb))
      · rcases h with hy | hrest
        · exact False.elim (hne (by simpa [hy] using hcut))
        · rcases hrest with ha | hb
          · exact rbnode_mem_append_of_mem (Or.inl ha)
          · exact rbnode_mem_append_of_mem (Or.inr hb)
      · cases hblack : Batteries.RBNode.isBlack b <;> simp
        · rcases h with hy | hrest
          · exact Or.inl hy
          · rcases hrest with ha | hb
            · exact Or.inr (Or.inl ha)
            · exact Or.inr (Or.inr (rbnode_mem_del_of_mem_ne cut hb hne))
        · rcases h with hy | hrest
          · exact rbnode_mem_balRight_of_mem (Or.inr (Or.inl hy))
          · rcases hrest with ha | hb
            · exact rbnode_mem_balRight_of_mem (Or.inl ha)
            · exact rbnode_mem_balRight_of_mem
                (Or.inr (Or.inr (rbnode_mem_del_of_mem_ne cut hb hne)))

private theorem rbnode_mem_of_mem_erase {α : Type u} {x : α}
    (cut : α → Ordering) {t : Batteries.RBNode α} :
    x ∈ Batteries.RBNode.erase cut t → x ∈ t := by
  intro h
  rw [← Batteries.RBNode.mem_toList] at h
  unfold Batteries.RBNode.erase at h
  rw [Batteries.RBNode.setBlack_toList] at h
  exact rbnode_mem_of_mem_del cut (Batteries.RBNode.mem_toList.1 h)

private theorem rbnode_mem_erase_of_mem_ne {α : Type u} {x : α}
    (cut : α → Ordering) {t : Batteries.RBNode α}
    (h : x ∈ t) (hne : cut x ≠ .eq) : x ∈ Batteries.RBNode.erase cut t := by
  rw [← Batteries.RBNode.mem_toList]
  unfold Batteries.RBNode.erase
  rw [Batteries.RBNode.setBlack_toList]
  exact Batteries.RBNode.mem_toList.2 (rbnode_mem_del_of_mem_ne cut h hne)

private theorem rbmap_mem_toList_of_mem_toList_erase {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} {m : Batteries.RBMap α β cmp} {write : α} {pair : α × β}
    (h : pair ∈ (m.erase write).toList) : pair ∈ m.toList := by
  have hnode : pair ∈ (m.erase write).1 := Batteries.RBMap.mem_toList.1 h
  have hmnode : pair ∈ m.1 := by
    unfold Batteries.RBMap.erase Batteries.RBSet.erase at hnode
    exact rbnode_mem_of_mem_erase (fun pair : α × β => cmp write pair.1) hnode
  exact Batteries.RBMap.mem_toList.2 hmnode

private theorem rbmap_mem_toList_erase_of_mem_toList_ne {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} {m : Batteries.RBMap α β cmp} {write : α} {pair : α × β}
    (h : pair ∈ m.toList) (hne : cmp write pair.1 ≠ .eq) : pair ∈ (m.erase write).toList := by
  have hnode : pair ∈ m.1 := Batteries.RBMap.mem_toList.1 h
  have heraseNode : pair ∈ (m.erase write).1 := by
    unfold Batteries.RBMap.erase Batteries.RBSet.erase
    exact rbnode_mem_erase_of_mem_ne (fun pair : α × β => cmp write pair.1) hnode hne
  exact Batteries.RBMap.mem_toList.2 heraseNode

/-- The generic RBMap lemma missing from `Batteries`: erasing one key preserves lookup at a
    different key. -/
theorem rbmap_find?_erase_ne {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (m : Batteries.RBMap α β cmp) (read write : α) (hne : read ≠ write) :
    (m.erase write).find? read = m.find? read := by
  cases hold : m.find? read with
  | none =>
      cases hnew : (m.erase write).find? read with
      | none => rfl
      | some v =>
          have holdSome : m.find? read = some v := by
            obtain ⟨y, hyErase, hcmp⟩ := (Batteries.RBMap.find?_some).1 hnew
            exact (Batteries.RBMap.find?_some).2
              ⟨y, rbmap_mem_toList_of_mem_toList_erase hyErase, hcmp⟩
          rw [hold] at holdSome
          cases holdSome
  | some v =>
      have hnewSome : (m.erase write).find? read = some v := by
        obtain ⟨y, hy, hcmp⟩ := (Batteries.RBMap.find?_some).1 hold
        have hcut : cmp write y ≠ .eq := by
          intro hwrite
          have hyEq : read = y := Std.LawfulEqCmp.eq_of_compare hcmp
          have hwEq : write = y := Std.LawfulEqCmp.eq_of_compare hwrite
          exact hne (hyEq.trans hwEq.symm)
        exact (Batteries.RBMap.find?_some).2
          ⟨y, rbmap_mem_toList_erase_of_mem_toList_ne hy hcut, hcmp⟩
      cases hnew : (m.erase write).find? read with
      | none =>
          rw [hnew] at hnewSome
          cases hnewSome
      | some v' =>
          have holdFromNew : m.find? read = some v' := by
            obtain ⟨y, hyErase, hcmp⟩ := (Batteries.RBMap.find?_some).1 hnew
            exact (Batteries.RBMap.find?_some).2
              ⟨y, rbmap_mem_toList_of_mem_toList_erase hyErase, hcmp⟩
          rw [hold] at holdFromNew
          cases holdFromNew
          rfl

/-- Erasing a storage word preserves lookup at a different storage slot. -/
theorem storage_findD_erase_ne (storage : Storage) (readSlot writeSlot default : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.erase writeSlot).findD readSlot default =
      storage.findD readSlot default := by
  unfold Batteries.RBMap.findD
  rw [rbmap_find?_erase_ne]
  exact hne

/-- Updating a storage slot with EVM/Solidity semantics preserves lookup at a different slot.
    Nonzero writes insert; zero writes erase. -/
theorem storage_findD_update_ne (storage : Storage) (readSlot writeSlot val default : UInt256)
    (hne : readSlot ≠ writeSlot) :
    ((if val == default then storage.erase writeSlot else storage.insert writeSlot val).findD
        readSlot default) =
      storage.findD readSlot default := by
  by_cases hzero : (val == default) = true
  · simpa [hzero] using storage_findD_erase_ne storage readSlot writeSlot default hne
  · simpa [hzero] using storage_findD_insert_ne storage readSlot writeSlot val default hne

theorem storage_find?_insert_ne (storage : Storage) (readSlot writeSlot val : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.insert writeSlot val).find? readSlot = storage.find? readSlot := by
  rw [Batteries.RBMap.find?_insert_of_ne]
  intro hcmp
  exact hne (Std.LawfulEqCmp.eq_of_compare hcmp)

theorem storage_find?_erase_ne (storage : Storage) (readSlot writeSlot : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.erase writeSlot).find? readSlot = storage.find? readSlot :=
  rbmap_find?_erase_ne storage readSlot writeSlot hne

private theorem rbnode_not_memP_del {α : Type u} {cmp : α → α → Ordering}
    {cut : α → Ordering} [Std.TransCmp cmp] [Batteries.RBNode.IsStrictCut cmp cut] :
    ∀ {t : Batteries.RBNode α}, Batteries.RBNode.Ordered cmp t →
      ¬ Batteries.RBNode.MemP cut (Batteries.RBNode.del cut t)
  | .nil, _, h => by cases h
  | .node _ a y b, ht, h => by
      unfold Batteries.RBNode.del at h
      rcases ht with ⟨ay, yb, ha, hb⟩
      cases hcut : cut y with
      | lt =>
          cases hblack : Batteries.RBNode.isBlack a <;> simp [hcut, hblack] at h
          · rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
            rcases hx with rfl | hdel | hbmem
            · exact nomatch heq.symm.trans hcut
            · exact rbnode_not_memP_del ha (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)
            · exact nomatch heq.symm.trans
                (Batteries.RBNode.IsCut.lt_trans
                  (Batteries.RBNode.All_def.1 yb _ hbmem).1 hcut)
          · rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
            rcases rbnode_mem_of_mem_balLeft hx with hdel | hrest
            · exact rbnode_not_memP_del ha (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)
            · rcases hrest with rfl | hbmem
              · exact nomatch heq.symm.trans hcut
              · exact nomatch heq.symm.trans
                  (Batteries.RBNode.IsCut.lt_trans
                    (Batteries.RBNode.All_def.1 yb _ hbmem).1 hcut)
      | eq =>
          simp [hcut] at h
          rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
          rcases rbnode_mem_of_mem_append hx with hamem | hbmem
          · have hcmp : cmp y x = .gt :=
              Std.OrientedCmp.gt_iff_lt.2 (Batteries.RBNode.All_def.1 ay _ hamem).1
            have hcutx : cut x = .gt := by
              rw [← Batteries.RBNode.IsStrictCut.exact (cmp := cmp) (cut := cut)
                (x := y) (y := x) hcut]
              exact hcmp
            exact nomatch heq.symm.trans hcutx
          · have hcmp : cmp y x = .lt := (Batteries.RBNode.All_def.1 yb _ hbmem).1
            have hcutx : cut x = .lt := by
              rw [← Batteries.RBNode.IsStrictCut.exact (cmp := cmp) (cut := cut)
                (x := y) (y := x) hcut]
              exact hcmp
            exact nomatch heq.symm.trans hcutx
      | gt =>
          cases hblack : Batteries.RBNode.isBlack b <;> simp [hcut, hblack] at h
          · rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
            rcases hx with rfl | hamem | hdel
            · exact nomatch heq.symm.trans hcut
            · exact nomatch heq.symm.trans
                (Batteries.RBNode.IsCut.gt_trans
                  (Batteries.RBNode.All_def.1 ay _ hamem).1 hcut)
            · exact rbnode_not_memP_del hb (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)
          · rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
            rcases rbnode_mem_of_mem_balRight hx with hamem | hrest
            · exact nomatch heq.symm.trans
                (Batteries.RBNode.IsCut.gt_trans
                  (Batteries.RBNode.All_def.1 ay _ hamem).1 hcut)
            · rcases hrest with rfl | hdel
              · exact nomatch heq.symm.trans hcut
              · exact rbnode_not_memP_del hb
                  (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)

private theorem rbnode_not_memP_erase {α : Type u} {cmp : α → α → Ordering}
    {cut : α → Ordering} [Std.TransCmp cmp] [Batteries.RBNode.IsStrictCut cmp cut]
    {t : Batteries.RBNode α} (ht : Batteries.RBNode.Ordered cmp t) :
    ¬ Batteries.RBNode.MemP cut (Batteries.RBNode.erase cut t) := by
  intro h
  rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
  have hxdel : x ∈ Batteries.RBNode.del cut t := by
    rw [← Batteries.RBNode.mem_toList] at hx ⊢
    unfold Batteries.RBNode.erase at hx
    simpa using hx
  exact rbnode_not_memP_del ht (Batteries.RBNode.memP_def.2 ⟨x, hxdel, heq⟩)

private theorem rbmap_find?_erase_self {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (m : Batteries.RBMap α β cmp) (write : α) :
    (m.erase write).find? write = none := by
  cases hfind : (m.erase write).find? write with
  | none => rfl
  | some v =>
      have hsome : ∃ y, (y, v) ∈ (m.erase write).toList ∧ cmp write y = .eq :=
        (Batteries.RBMap.find?_some).1 hfind
      rcases hsome with ⟨y, hymem, hcmp⟩
      have hmemNode : (y, v) ∈ (m.erase write).1 := Batteries.RBMap.mem_toList.1 hymem
      have hno := rbnode_not_memP_erase
        (cmp := Ordering.byKey Prod.fst cmp)
        (cut := Ordering.byKey Prod.fst cmp (write, v))
        (t := m.1) m.2.out.1
      cases hno (Batteries.RBNode.memP_def.2 ⟨(y, v), hmemNode, hcmp⟩)

/-- Erasing a storage slot removes lookup at that same slot. -/
theorem storage_find?_erase_self (storage : Storage) (slot : UInt256) :
    (storage.erase slot).find? slot = none :=
  rbmap_find?_erase_self storage slot

/-- Updating a storage slot with EVM/Solidity semantics preserves `find?` at a different slot.
    Nonzero writes insert; zero writes erase. -/
theorem storage_find?_update_ne (storage : Storage) (readSlot writeSlot val : UInt256)
    (hne : readSlot ≠ writeSlot) :
    ((if val == (default : UInt256) then storage.erase writeSlot
      else storage.insert writeSlot val).find? readSlot) =
      storage.find? readSlot := by
  by_cases hzero : (val == (default : UInt256)) = true
  · simpa [hzero] using storage_find?_erase_ne storage readSlot writeSlot hne
  · simpa [hzero] using storage_find?_insert_ne storage readSlot writeSlot val hne

/-- Lookup-level same-key overwrite for `RBMap.insert`.

The structurally stronger equality of `RBMap`s is false in general, because inserting a missing key
and then overwriting it can recolor the root differently from a single insert.  Lookup equivalence
is the reusable form for simplifying reads after double writes. -/
theorem rbmap_find?_insert_insert_self {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (m : Batteries.RBMap α β cmp) (write read : α) (v1 v2 : β) :
    ((m.insert write v1).insert write v2).find? read =
      (m.insert write v2).find? read := by
  by_cases h : cmp read write = .eq
  · rw [Batteries.RBMap.find?_insert_of_eq (t := m.insert write v1) (k := write)
      (v := v2) (k' := read) h,
      Batteries.RBMap.find?_insert_of_eq (t := m) (k := write) (v := v2) (k' := read) h]
  · rw [Batteries.RBMap.find?_insert_of_ne (t := m.insert write v1) (k := write)
      (v := v2) (k' := read) h,
      Batteries.RBMap.find?_insert_of_ne (t := m) (k := write) (v := v1)
        (k' := read) h,
      Batteries.RBMap.find?_insert_of_ne (t := m) (k := write) (v := v2)
        (k' := read) h]

/-- `findD` version of same-key overwrite for `RBMap.insert`. -/
theorem rbmap_findD_insert_insert_self {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (m : Batteries.RBMap α β cmp) (write read : α) (v1 v2 default : β) :
    ((m.insert write v1).insert write v2).findD read default =
      (m.insert write v2).findD read default := by
  unfold Batteries.RBMap.findD
  rw [rbmap_find?_insert_insert_self]

/-- Storage-slot lookup after two same-slot writes is the same as after the final write. -/
theorem storage_findD_insert_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 default : UInt256) :
    ((storage.insert writeSlot val1).insert writeSlot val2).findD readSlot default =
      (storage.insert writeSlot val2).findD readSlot default :=
  rbmap_findD_insert_insert_self storage writeSlot readSlot val1 val2 default

theorem storage_find?_insert_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 : UInt256) :
    ((storage.insert writeSlot val1).insert writeSlot val2).find? readSlot =
      (storage.insert writeSlot val2).find? readSlot :=
  rbmap_find?_insert_insert_self storage writeSlot readSlot val1 val2

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- Reading after an arbitrary zero-aware storage update followed by a same-slot nonzero insert is
    the same as reading after just the final insert. -/
theorem storage_findD_update_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 : UInt256) :
    (((if val1 = (default : UInt256) then storage.erase writeSlot
        else storage.insert writeSlot val1).insert writeSlot val2).findD readSlot
        (default : UInt256)) =
      (storage.insert writeSlot val2).findD readSlot (default : UInt256) := by
  by_cases hread : readSlot = writeSlot
  · subst readSlot
    unfold Batteries.RBMap.findD
    rw [Batteries.RBMap.find?_insert_of_eq
      (t := if val1 = (default : UInt256) then storage.erase writeSlot
        else storage.insert writeSlot val1)
      (k := writeSlot) (v := val2) (k' := writeSlot) Std.ReflCmp.compare_self]
    rw [Batteries.RBMap.find?_insert_of_eq (t := storage) (k := writeSlot) (v := val2)
      (k' := writeSlot) Std.ReflCmp.compare_self]
  · by_cases hzero : val1 = (default : UInt256)
    · simp only [hzero, if_true]
      rw [storage_findD_insert_ne (storage.erase writeSlot) readSlot writeSlot val2 default hread]
      rw [storage_findD_insert_ne storage readSlot writeSlot val2 default hread]
      rw [storage_findD_erase_ne storage readSlot writeSlot default hread]
    · simp only [hzero, if_false]
      rw [storage_findD_insert_insert_self]

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- `find?` after an arbitrary zero-aware storage update followed by a same-slot nonzero insert is
    the same as `find?` after just the final insert. -/
theorem storage_find?_update_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 : UInt256) :
    (((if val1 = (default : UInt256) then storage.erase writeSlot
        else storage.insert writeSlot val1).insert writeSlot val2).find? readSlot) =
      (storage.insert writeSlot val2).find? readSlot := by
  by_cases hread : readSlot = writeSlot
  · subst readSlot
    rw [Batteries.RBMap.find?_insert_of_eq
      (t := if val1 = (default : UInt256) then storage.erase writeSlot
        else storage.insert writeSlot val1)
      (k := writeSlot) (v := val2) (k' := writeSlot) Std.ReflCmp.compare_self]
    rw [Batteries.RBMap.find?_insert_of_eq (t := storage) (k := writeSlot) (v := val2)
      (k' := writeSlot) Std.ReflCmp.compare_self]
  · by_cases hzero : val1 = (default : UInt256)
    · simp only [hzero, if_true]
      rw [storage_find?_insert_ne (storage.erase writeSlot) readSlot writeSlot val2 hread]
      rw [storage_find?_insert_ne storage readSlot writeSlot val2 hread]
      rw [storage_find?_erase_ne storage readSlot writeSlot hread]
    · simp only [hzero, if_false]
      rw [storage_find?_insert_insert_self]

/-- Account lookup after two same-address writes is the same as after the final write. -/
theorem accountMap_find?_insert_insert_self (σ : AccountMap)
    (write read : AccountAddress) (acc1 acc2 : Account) :
    ((σ.insert write acc1).insert write acc2).find? read =
      (σ.insert write acc2).find? read :=
  rbmap_find?_insert_insert_self σ write read acc1 acc2

/-- Inserting one account preserves lookup at a different address. -/
theorem accountMap_find?_insert_ne (σ : AccountMap) (read write : AccountAddress)
    (acc : Account) (hne : read ≠ write) :
    (σ.insert write acc).find? read = σ.find? read := by
  rw [Batteries.RBMap.find?_insert_of_ne]
  intro hcmp
  exact hne (Std.LawfulEqCmp.eq_of_compare hcmp)

/-- Looking up the account just inserted at its own address returns that account. -/
theorem accountMap_find_insert_self (σ : AccountMap) (a : AccountAddress) (acc : Account) :
    (σ.insert a acc).find? a = some acc := by
  rw [Batteries.RBMap.find?_insert_of_eq]
  exact Std.ReflCmp.compare_self

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- A zero-aware `SSTORE` to one storage slot preserves an observable read from a different slot
    of the same account. -/
theorem sstoreAccountMap_storage_findD_ne (σ : AccountMap) (a : AccountAddress)
    (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    (((sstoreAccountMap a σ writeSlot val).find? a).option (default : UInt256)
        (fun acc => acc.storage.findD readSlot (default : UInt256))) =
      ((σ.find? a).option (default : UInt256)
        (fun acc => acc.storage.findD readSlot (default : UInt256))) := by
  unfold sstoreAccountMap
  cases hσ : σ.find? a with
  | none =>
      simp [hσ, Option.option]
  | some acc =>
      simp [Option.option, accountMap_find_insert_self]
      by_cases hzero : val = (default : UInt256)
      · simpa [hzero] using storage_findD_update_ne acc.storage readSlot writeSlot val default hne
      · simpa [hzero] using storage_findD_update_ne acc.storage readSlot writeSlot val default hne

theorem accountEquiv_refl (acc : Account) : accountEquiv acc acc := by
  exact ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem accountMapEquiv_refl (σ : AccountMap) : accountMapEquiv σ σ := by
  intro addr
  cases σ.find? addr <;> simp [accountEquiv_refl]

theorem accountEquiv_storage_findD {acc₁ acc₂ : Account} (slot default : UInt256)
    (hacc : accountEquiv acc₁ acc₂) :
    acc₁.storage.findD slot default = acc₂.storage.findD slot default := by
  unfold Batteries.RBMap.findD
  rw [hacc.2.2.2.1 slot]

theorem accountMapEquiv_storage_findD {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (addr : AccountAddress) (slot default : UInt256) :
    ((σ.find? addr).option default (fun acc => acc.storage.findD slot default)) =
      ((τ.find? addr).option default (fun acc => acc.storage.findD slot default)) := by
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;> simp [hσ, hτ, Option.option] at hστ ⊢
  exact accountEquiv_storage_findD slot default hστ

/-- Erasing the same persistent storage slot from equivalent accounts preserves equivalence. -/
theorem accountEquiv_erase_storage_of_equiv {acc₁ acc₂ : Account}
    (slot : UInt256) (hacc : accountEquiv acc₁ acc₂) :
    accountEquiv {acc₁ with storage := acc₁.storage.erase slot}
      {acc₂ with storage := acc₂.storage.erase slot} := by
  rcases hacc with ⟨hnonce, hbalance, hcode, hstorage, htstorage⟩
  refine ⟨hnonce, hbalance, hcode, ?_, htstorage⟩
  intro readSlot
  by_cases hread : readSlot = slot
  · subst readSlot
    rw [storage_find?_erase_self, storage_find?_erase_self]
  · rw [storage_find?_erase_ne acc₁.storage readSlot slot hread,
      storage_find?_erase_ne acc₂.storage readSlot slot hread, hstorage readSlot]

theorem storageLoad_accountMapEquiv {evm1 evm2 : EVM.State}
    (hAccounts : accountMapEquiv evm1.accountMap evm2.accountMap)
    (addr : AccountAddress) (slot : UInt256) :
    Solm.EVM.storageLoad evm1 addr slot = Solm.EVM.storageLoad evm2 addr slot := by
  simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
  exact accountMapEquiv_storage_findD hAccounts addr slot (default : UInt256)

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- Inserting the same nonzero storage word into equivalent accounts preserves account
    equivalence. -/
theorem accountEquiv_insert_storage_of_equiv {acc₁ acc₂ : Account} (slot val : UInt256)
    (hacc : accountEquiv acc₁ acc₂) :
    accountEquiv {acc₁ with storage := acc₁.storage.insert slot val}
      {acc₂ with storage := acc₂.storage.insert slot val} := by
  rcases hacc with ⟨hn, hb, hc, hs, ht⟩
  refine ⟨hn, hb, hc, ?_, ht⟩
  intro readSlot
  by_cases hread : readSlot = slot
  · subst readSlot
    rw [Batteries.RBMap.find?_insert_of_eq (t := acc₁.storage) (k := slot) (v := val)
      (k' := slot) Std.ReflCmp.compare_self]
    rw [Batteries.RBMap.find?_insert_of_eq (t := acc₂.storage) (k := slot) (v := val)
      (k' := slot) Std.ReflCmp.compare_self]
  · rw [storage_find?_insert_ne acc₁.storage readSlot slot val hread]
    rw [storage_find?_insert_ne acc₂.storage readSlot slot val hread]
    exact hs readSlot

theorem accountEquiv_update_insert_self (acc : Account) (slot val1 val2 : UInt256) :
    accountEquiv {acc with storage := acc.storage.insert slot val2}
      {acc with storage :=
        (if val1 = (default : UInt256) then acc.storage.erase slot
         else acc.storage.insert slot val1).insert slot val2} := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro readSlot
    exact (storage_find?_update_insert_self acc.storage slot readSlot val1 val2).symm
  · simp

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- `accountMapEquiv` is preserved by the same nonzero `SSTORE` on both maps. -/
theorem accountMapEquiv_sstoreAccountMap_insert {σ τ : AccountMap}
    (a : AccountAddress) (slot val : UInt256)
    (hστ : accountMapEquiv σ τ) (hval : (val == (default : UInt256)) = false) :
    accountMapEquiv (sstoreAccountMap a σ slot val) (sstoreAccountMap a τ slot val) := by
  intro addr
  by_cases haddr : addr = a
  · subst addr
    unfold sstoreAccountMap
    specialize hστ a
    cases hσ : σ.find? a with
    | none =>
        cases hτ : τ.find? a with
        | none =>
            simp [hσ, hτ, Option.option]
        | some accτ =>
            have hbad : False := by
              simp [hσ, hτ] at hστ
            exact False.elim hbad
    | some accσ =>
        cases hτ : τ.find? a with
        | none =>
            have hbad : False := by
              simp [hσ, hτ] at hστ
            exact False.elim hbad
        | some accτ =>
            have hacc : accountEquiv accσ accτ := by simpa [hσ, hτ] using hστ
            simpa [hσ, hτ, Option.option, hval, accountMap_find_insert_self] using
              accountEquiv_insert_storage_of_equiv slot val hacc
  · unfold sstoreAccountMap
    specialize hστ addr
    cases hσa : σ.find? a <;> cases hτa : τ.find? a <;>
      simp only [Option.option]
    · exact hστ
    · rw [accountMap_find?_insert_ne τ addr a _ haddr]
      exact hστ
    · rw [accountMap_find?_insert_ne σ addr a _ haddr]
      exact hστ
    · rw [accountMap_find?_insert_ne σ addr a _ haddr]
      rw [accountMap_find?_insert_ne τ addr a _ haddr]
      exact hστ

-- TODO: prove the zero-write branch from a reusable `RBMap.erase` same-key lookup theorem.
-- The nonzero branch is `accountMapEquiv_sstoreAccountMap_insert`; the zero branch is the
-- corresponding erase-on-both-sides fact.  This is the statement examples should consume.
axiom accountMapEquiv_sstoreAccountMap {σ τ : AccountMap}
    (a : AccountAddress) (slot val : UInt256)
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv (sstoreAccountMap a σ slot val) (sstoreAccountMap a τ slot val)

theorem storageStore_accountMapEquiv {evm1 evm2 : EVM.State}
    (hAccounts : accountMapEquiv evm1.accountMap evm2.accountMap)
    (addr : AccountAddress) (slot val : UInt256) :
    accountMapEquiv (Solm.EVM.storageStore evm1 addr slot val).accountMap
      (Solm.EVM.storageStore evm2 addr slot val).accountMap := by
  simp [storageStore_accountMap]
  exact accountMapEquiv_sstoreAccountMap addr slot val hAccounts

theorem storageStore_executionEnv (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).executionEnv = evm.executionEnv := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

structure EVMStateEquiv (evm₁ evm₂ : EVM.State) : Prop where
  executionEnv : evm₁.executionEnv = evm₂.executionEnv
  createdAccounts : evm₁.createdAccounts = evm₂.createdAccounts
  accountMap : accountMapEquiv evm₁.accountMap evm₂.accountMap

namespace EVMStateEquiv

theorem initState {cA gh bl σ₁ σ₀₁ σ₂ σ₀₂ A I g}
    (hAccounts : accountMapEquiv σ₁ σ₂) :
    EVMStateEquiv (initState cA gh bl σ₁ σ₀₁ g A I)
      (initState cA gh bl σ₂ σ₀₂ g A I) :=
  ⟨rfl, rfl, by simpa [initState] using hAccounts⟩

theorem storageLoad {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    {addr₁ addr₂ : AccountAddress} (haddr : addr₁ = addr₂) (slot : UInt256) :
    Solm.EVM.storageLoad evm₁ addr₁ slot = Solm.EVM.storageLoad evm₂ addr₂ slot := by
  subst addr₂
  exact storageLoad_accountMapEquiv h.accountMap addr₁ slot

theorem storageLoad_codeOwner {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    (slot : UInt256) :
    Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner slot =
      Solm.EVM.storageLoad evm₂ evm₂.executionEnv.codeOwner slot := by
  rw [h.executionEnv]
  exact storageLoad_accountMapEquiv h.accountMap evm₂.executionEnv.codeOwner slot

theorem storageStore {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    {addr₁ addr₂ : AccountAddress} (haddr : addr₁ = addr₂) (slot : UInt256)
    {val₁ val₂ : UInt256} (hval : val₁ = val₂) :
    EVMStateEquiv (Solm.EVM.storageStore evm₁ addr₁ slot val₁)
      (Solm.EVM.storageStore evm₂ addr₂ slot val₂) := by
  subst addr₂
  subst val₂
  refine ⟨?_, ?_, ?_⟩
  · rw [storageStore_executionEnv, storageStore_executionEnv]
    exact h.executionEnv
  · rw [storageStore_createdAccounts, storageStore_createdAccounts]
    exact h.createdAccounts
  · exact storageStore_accountMapEquiv h.accountMap addr₁ slot val₁

theorem storageStore_codeOwner {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    (slot : UInt256) {val₁ val₂ : UInt256} (hval : val₁ = val₂) :
    EVMStateEquiv
      (Solm.EVM.storageStore evm₁ evm₁.executionEnv.codeOwner slot val₁)
      (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner slot val₂) :=
  h.storageStore (congrArg ExecutionEnv.codeOwner h.executionEnv) slot hval

end EVMStateEquiv

theorem storageLoad_storageStore_accountMapEquiv {evm1 evm2 : EVM.State}
    (hAccounts : accountMapEquiv evm1.accountMap evm2.accountMap)
    (addr : AccountAddress) (writeSlot val1 val2 readSlot : UInt256)
    (hval : val1 = val2) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm1 addr writeSlot val1) addr readSlot =
      Solm.EVM.storageLoad (Solm.EVM.storageStore evm2 addr writeSlot val2) addr readSlot := by
  subst val2
  exact storageLoad_accountMapEquiv
    (storageStore_accountMapEquiv hAccounts addr writeSlot val1) addr readSlot

theorem accountMapEquiv_sstoreAccountMap_two {σ τ : AccountMap}
    (a1 a2 : AccountAddress) (slot1 val1 slot2 val2 : UInt256)
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv
      (sstoreAccountMap a2 (sstoreAccountMap a1 σ slot1 val1) slot2 val2)
      (sstoreAccountMap a2 (sstoreAccountMap a1 τ slot1 val1) slot2 val2) := by
  exact accountMapEquiv_sstoreAccountMap a2 slot2 val2
    (accountMapEquiv_sstoreAccountMap a1 slot1 val1 hστ)

theorem accountMapEquiv_sstoreAccountMap_three {σ τ : AccountMap}
    (a1 a2 a3 : AccountAddress) (slot1 val1 slot2 val2 slot3 val3 : UInt256)
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv
      (sstoreAccountMap a3
        (sstoreAccountMap a2 (sstoreAccountMap a1 σ slot1 val1) slot2 val2) slot3 val3)
      (sstoreAccountMap a3
        (sstoreAccountMap a2 (sstoreAccountMap a1 τ slot1 val1) slot2 val2) slot3 val3) := by
  exact accountMapEquiv_sstoreAccountMap a3 slot3 val3
    (accountMapEquiv_sstoreAccountMap_two a1 a2 slot1 val1 slot2 val2 hστ)

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- A single nonzero `SSTORE` is account-map equivalent to a zero-aware write followed by the same
    final same-slot nonzero `SSTORE`. -/
theorem accountMapEquiv_sstoreAccountMap_self_update_insert
    (σ : AccountMap) (a : AccountAddress) (slot val1 val2 : UInt256)
    (hfinal : (val2 == (default : UInt256)) = false) :
    accountMapEquiv (sstoreAccountMap a σ slot val2)
      (sstoreAccountMap a (sstoreAccountMap a σ slot val1) slot val2) := by
  intro addr
  by_cases haddr : addr = a
  · subst addr
    unfold sstoreAccountMap
    cases hσ : σ.find? a with
    | none =>
        simp [hσ, Option.option]
    | some acc =>
        simp [hfinal, accountMap_find_insert_self, Option.option]
        by_cases hzero : val1 = (default : UInt256)
        · simpa [hzero] using accountEquiv_update_insert_self acc slot val1 val2
        · simpa [hzero] using accountEquiv_update_insert_self acc slot val1 val2
  · unfold sstoreAccountMap
    cases hσ : σ.find? a
    · simp only [hσ, Option.option]
      cases σ.find? addr <;> simp [accountEquiv_refl]
    · simp only [Option.option, hfinal, Bool.false_eq_true, if_false]
      rw [accountMap_find_insert_self]
      rw [accountMap_find?_insert_ne σ addr a _ haddr]
      rw [accountMap_find?_insert_ne (σ.insert a _) addr a _ haddr]
      rw [accountMap_find?_insert_ne σ addr a _ haddr]
      cases σ.find? addr <;> simp [accountEquiv_refl]

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- Same-account/same-slot overwrite at the lookup level for `sstoreAccountMap` when the final write
    is nonzero.  This is the EVM/Solidity storage-update analogue of
    `storage_findD_update_insert_self`. -/
theorem sstoreAccountMap_self_storage_findD_update_insert_self
    (σ : AccountMap) (a : AccountAddress) (writeSlot readSlot val1 val2 : UInt256)
    (hfinal : (val2 == (default : UInt256)) = false) :
    (((sstoreAccountMap a (sstoreAccountMap a σ writeSlot val1) writeSlot val2).find? a).option
        (default : UInt256) (fun acc => acc.storage.findD readSlot default)) =
      (((sstoreAccountMap a σ writeSlot val2).find? a).option
        (default : UInt256) (fun acc => acc.storage.findD readSlot default)) := by
  cases hacc : σ.find? a with
  | none =>
      have hfirst : sstoreAccountMap a σ writeSlot val1 = σ := by
        simp only [sstoreAccountMap, hacc, Option.option]
      have hsecond : sstoreAccountMap a σ writeSlot val2 = σ := by
        simp only [sstoreAccountMap, hacc, Option.option]
      rw [hfirst, hsecond]
  | some acc =>
      let acc1 : Account :=
        if val1 == (default : UInt256) then {acc with storage := acc.storage.erase writeSlot}
        else {acc with storage := acc.storage.insert writeSlot val1}
      let acc2 : Account := {acc with storage := acc.storage.insert writeSlot val2}
      have hfirst : sstoreAccountMap a σ writeSlot val1 = σ.insert a acc1 := by
        simp only [sstoreAccountMap, hacc, Option.option, acc1]
      have hsecond :
          sstoreAccountMap a (sstoreAccountMap a σ writeSlot val1) writeSlot val2 =
            (σ.insert a acc1).insert a
              {acc1 with storage := acc1.storage.insert writeSlot val2} := by
        rw [hfirst]
        simp only [sstoreAccountMap, accountMap_find_insert_self, Option.option, hfinal,
          Bool.false_eq_true, if_false]
      have hright : sstoreAccountMap a σ writeSlot val2 = σ.insert a acc2 := by
        simp only [sstoreAccountMap, hacc, hfinal, Option.option, Bool.false_eq_true, if_false,
          acc2]
      rw [hsecond, hright]
      rw [accountMap_find_insert_self, accountMap_find_insert_self]
      change (acc1.storage.insert writeSlot val2).findD readSlot default =
        (acc.storage.insert writeSlot val2).findD readSlot default
      by_cases hzero : val1 = (default : UInt256)
      · simpa [acc1, hzero] using
          storage_findD_update_insert_self acc.storage writeSlot readSlot val1 val2
      · simpa [acc1, hzero] using
          storage_findD_update_insert_self acc.storage writeSlot readSlot val1 val2

end Reasoning.Theory
