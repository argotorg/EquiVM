import Examples.OpenZeppelinBench.AccessControl.Common
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.AccessControl

/-!
# AccessControl benchmark storage helpers

Helpers for the `_roles` nested mapping layout and full-slot/low-byte storage load-store facts.
-/

-- LIBRARY CANDIDATE: `Reasoning.Memory`.
theorem fromBytes'_eq_ofDigits (bs : List UInt8) :
    fromBytes' bs = Nat.ofDigits 256 (bs.map (fun b => b.toNat)) :=
  Reasoning.Theory.fromBytes'_eq_ofDigits bs

theorem accessControlWordOfInt_ofNat_toNat (a : UInt256) :
    EVM.wordOfInt (Int.ofNat a.toNat) = a := by
  rw [EVM.wordOfInt, if_neg (by simp)]
  apply u256_inj
  rw [show (Int.ofNat a.toNat).toNat = a.toNat from rfl]
  show a.toNat % EVM.twoPow 256 = a.toNat
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.val.isLt (by decide))

theorem accessControlKeyValueToWord_fixedBytes32 (w : UInt256) :
    keyValueToWord (.fixedBytes bytes32Width (EVM.Word.toBytesBE w)) = w := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  simp [keyValueToWord, bytes32Width, hlen]
  apply u256_inj
  have hfrom : fromBytesBigEndian (EVM.Word.toBytesBE w) = w.toNat := by
    have h := congrArg fromByteArrayBigEndian (word_toBytesBE_toByteArray_eq_toByteArray w)
    simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
      h.trans (fromByteArrayBigEndian_toByteArray w)
  rw [EVM.Word.ofNat, hfrom]
  exact Nat.mod_eq_of_lt w.val.isLt

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem accessControlNat_land_mask_eq_mod (n k : Nat) :
    Nat.land n (2 ^ k - 1) = n % 2 ^ k :=
  Reasoning.Theory.nat_land_mask_eq_mod n k

theorem accessControlStorageLocLoad_bytes32_raw (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 32, hbound := by decide,
          type := .bytes ⟨31, by decide⟩ }
      = .fixedBytes ⟨31, by decide⟩
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
  unfold storageLocLoad wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  simp only [show 32 - (31 + 1) = 0 by norm_num, List.drop_zero]
  congr
  rw [htake]
  exact fromBytes'_toBytesLEWithSizeProof _

theorem accessControlStorageLocLoad_bytes32 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (bytes32Loc slot)
      = .fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  simpa [bytes32Loc] using accessControlStorageLocLoad_bytes32_raw evm slot

-- LIBRARY CANDIDATE: `Reasoning.Memory`.
theorem accessControlFromBytes'_take1_wordLE (w : UInt256) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.take 1) =
      (UInt256.land w ⟨255⟩).toNat := by
  simpa using Reasoning.Theory.fromBytes'_take_wordLE_land_mask w 1 (by decide)

theorem accessControlStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (boolLoc slot)
      = wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  unfold storageLocLoad boolLoc
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 1) = _
  rw [accessControlFromBytes'_take1_wordLE]
  rfl

theorem accessControlStorageLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm (boolLoc slot) = .bool false := by
  rw [accessControlStorageLocLoad_bool_offset0 evm slot]
  simp [wordToElem, hzero]

theorem accessControlStorageLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm (boolLoc slot) = .bool true := by
  rw [accessControlStorageLocLoad_bool_offset0 evm slot]
  have hbeq :
      ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩).val == 0) =
        false := by
    rw [beq_eq_false_iff_ne]
    intro hval
    apply hnz
    apply u256_inj
    simpa [UInt256.toNat] using hval
  simp [wordToElem, hbeq]

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
private theorem accessControlRBNode_append_toList {α : Type u} (l r : Batteries.RBNode α) :
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

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
private theorem accessControlRBNode_mem_of_mem_append {α : Type u} {x : α}
    {l r : Batteries.RBNode α} (h : x ∈ l.append r) : x ∈ l ∨ x ∈ r := by
  rw [← Batteries.RBNode.mem_toList] at h
  rw [accessControlRBNode_append_toList] at h
  simpa [Batteries.RBNode.mem_toList] using h

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
private theorem accessControlRBNode_mem_of_mem_balLeft {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l.balLeft v r) :
    x ∈ l ∨ x = v ∨ x ∈ r := by
  rw [← Batteries.RBNode.mem_toList] at h
  rw [Batteries.RBNode.balLeft_toList] at h
  simpa [Batteries.RBNode.mem_toList] using h

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
private theorem accessControlRBNode_mem_of_mem_balRight {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l.balRight v r) :
    x ∈ l ∨ x = v ∨ x ∈ r := by
  rw [← Batteries.RBNode.mem_toList] at h
  rw [Batteries.RBNode.balRight_toList] at h
  simpa [Batteries.RBNode.mem_toList] using h

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
private theorem accessControlRBNode_not_memP_del {α : Type u} {cmp : α → α → Ordering}
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
            · exact accessControlRBNode_not_memP_del ha
                (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)
            · exact nomatch heq.symm.trans
                (Batteries.RBNode.IsCut.lt_trans
                  (Batteries.RBNode.All_def.1 yb _ hbmem).1 hcut)
          · rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
            rcases accessControlRBNode_mem_of_mem_balLeft hx with hdel | hrest
            · exact accessControlRBNode_not_memP_del ha
                (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)
            · rcases hrest with rfl | hbmem
              · exact nomatch heq.symm.trans hcut
              · exact nomatch heq.symm.trans
                  (Batteries.RBNode.IsCut.lt_trans
                    (Batteries.RBNode.All_def.1 yb _ hbmem).1 hcut)
      | eq =>
          simp [hcut] at h
          rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
          rcases accessControlRBNode_mem_of_mem_append hx with hamem | hbmem
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
            · exact accessControlRBNode_not_memP_del hb
                (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)
          · rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
            rcases accessControlRBNode_mem_of_mem_balRight hx with hamem | hrest
            · exact nomatch heq.symm.trans
                (Batteries.RBNode.IsCut.gt_trans
                  (Batteries.RBNode.All_def.1 ay _ hamem).1 hcut)
            · rcases hrest with rfl | hdel
              · exact nomatch heq.symm.trans hcut
              · exact accessControlRBNode_not_memP_del hb
                  (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
private theorem accessControlRBNode_not_memP_erase {α : Type u} {cmp : α → α → Ordering}
    {cut : α → Ordering} [Std.TransCmp cmp] [Batteries.RBNode.IsStrictCut cmp cut]
    {t : Batteries.RBNode α} (ht : Batteries.RBNode.Ordered cmp t) :
    ¬ Batteries.RBNode.MemP cut (Batteries.RBNode.erase cut t) := by
  intro h
  rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
  have hxdel : x ∈ Batteries.RBNode.del cut t := by
    rw [← Batteries.RBNode.mem_toList] at hx ⊢
    unfold Batteries.RBNode.erase at hx
    simpa using hx
  exact accessControlRBNode_not_memP_del ht
    (Batteries.RBNode.memP_def.2 ⟨x, hxdel, heq⟩)

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
private theorem accessControlRBMap_find?_erase_self {α : Type u} {β : Type v}
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
      have hno := accessControlRBNode_not_memP_erase
        (cmp := Ordering.byKey Prod.fst cmp)
        (cut := Ordering.byKey Prod.fst cmp (write, v))
        (t := m.1) m.2.out.1
      cases hno (Batteries.RBNode.memP_def.2 ⟨(y, v), hmemNode, hcmp⟩)

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
theorem accessControlStorage_find?_erase_self (storage : Storage) (slot : UInt256) :
    (storage.erase slot).find? slot = none :=
  accessControlRBMap_find?_erase_self storage slot

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
theorem accessControlAccountEquiv_erase_storage_of_equiv {acc₁ acc₂ : Account}
    (slot : UInt256) (hacc : accountEquiv acc₁ acc₂) :
    accountEquiv { acc₁ with storage := acc₁.storage.erase slot }
      { acc₂ with storage := acc₂.storage.erase slot } :=
  Reasoning.Theory.accountEquiv_erase_storage_of_equiv slot hacc

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
theorem accessControlAccountMapEquiv_sstoreAccountMap {σ τ : AccountMap}
    (a : AccountAddress) (slot val : UInt256) (hστ : accountMapEquiv σ τ) :
    accountMapEquiv (sstoreAccountMap a σ slot val) (sstoreAccountMap a τ slot val) := by
  by_cases hval : (val == (default : UInt256)) = false
  · exact accountMapEquiv_sstoreAccountMap_insert a slot val hστ hval
  have hzero : (val == (default : UInt256)) = true := by
    cases h : (val == (default : UInt256)) <;> simp [h] at hval ⊢
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
            simpa [hσ, hτ, Option.option, hzero, accountMap_find_insert_self] using
              accessControlAccountEquiv_erase_storage_of_equiv slot hacc
  · unfold sstoreAccountMap
    specialize hστ addr
    cases hσa : σ.find? a <;> cases hτa : τ.find? a <;> simp only [Option.option]
    · exact hστ
    · rw [accountMap_find?_insert_ne τ addr a _ haddr]
      exact hστ
    · rw [accountMap_find?_insert_ne σ addr a _ haddr]
      exact hστ
    · rw [accountMap_find?_insert_ne σ addr a _ haddr]
      rw [accountMap_find?_insert_ne τ addr a _ haddr]
      exact hστ

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
theorem accessControlEVMStateEquiv_storageStore_codeOwner {evm₁ evm₂ : EVM.State}
    (h : EVMStateEquiv evm₁ evm₂) (slot : UInt256) {val₁ val₂ : UInt256}
    (hval : val₁ = val₂) :
    EVMStateEquiv
      (Solm.EVM.storageStore evm₁ evm₁.executionEnv.codeOwner slot val₁)
      (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner slot val₂) := by
  subst val₂
  refine ⟨?_, ?_, ?_⟩
  · rw [storageStore_executionEnv, storageStore_executionEnv]
    exact h.executionEnv
  · rw [storageStore_createdAccounts, storageStore_createdAccounts]
    exact h.createdAccounts
  · rw [storageStore_accountMap, storageStore_accountMap, h.executionEnv]
    exact accessControlAccountMapEquiv_sstoreAccountMap evm₂.executionEnv.codeOwner slot val₁
      h.accountMap

end OpenZeppelinBench.AccessControl
