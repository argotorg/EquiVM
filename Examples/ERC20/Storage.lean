import Examples.ERC20.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace ERC20

/-! ## ERC20-local storage-store and bool-return helpers -/

/-- `wordOfInt (Int.ofNat a.toNat) = a` for an EVM word. -/
theorem erc20WordOfInt_ofNat_toNat (a : UInt256) :
    EVM.wordOfInt (Int.ofNat a.toNat) = a := by
  rw [EVM.wordOfInt, if_neg (by simp)]
  apply u256_inj
  rw [show (Int.ofNat a.toNat).toNat = a.toNat from rfl]
  show a.toNat % EVM.twoPow 256 = a.toNat
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.val.isLt (by decide))

/-- Storing a full-slot ERC20 `uint256` writes exactly the EVM word in the same slot. -/
theorem erc20StorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (erc20Uint256Loc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  unfold storageLocStore erc20Uint256Loc
  simp only [valueToWord, erc20WordOfInt_ofNat_toNat, bind, Option.bind, pure]
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
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytesLE_roundtrip]

/-- `EVM.storageStore`'s account map is exactly the map carried by `RD.sstore`. -/
theorem erc20StorageStore_accountMap (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).accountMap =
      sstoreAccountMap a evm.accountMap slot val := by
  simp only [Solm.EVM.storageStore, sstoreAccountMap, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

/-- `EVM.storageStore` does not create accounts. -/
theorem erc20StorageStore_createdAccounts (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).createdAccounts = evm.createdAccounts := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount]

/-! ## ERC20-local storage-map preservation helpers -/

/-- The derived `UInt256` order compares the wrapped `Fin` values. -/
@[simp] theorem erc20UInt256_compare_eq_val_compare (a b : UInt256) :
    compare a b = compare a.val b.val := by
  cases a
  cases b
  simp [compare, Ethereum.instOrdUInt256.ord]

instance : Std.OrientedCmp (compare : UInt256 → UInt256 → Ordering) where
  eq_swap := by
    intro a b
    rw [erc20UInt256_compare_eq_val_compare a b,
      erc20UInt256_compare_eq_val_compare b a]
    exact Std.OrientedCmp.eq_swap

instance : Std.TransCmp (compare : UInt256 → UInt256 → Ordering) where
  isLE_trans := by
    intro a b c hab hbc
    rw [erc20UInt256_compare_eq_val_compare a b] at hab
    rw [erc20UInt256_compare_eq_val_compare b c] at hbc
    rw [erc20UInt256_compare_eq_val_compare a c]
    exact Std.TransCmp.isLE_trans hab hbc

instance : Std.ReflCmp (compare : UInt256 → UInt256 → Ordering) where
  compare_self := by
    intro a
    rw [erc20UInt256_compare_eq_val_compare a a]
    exact Std.ReflCmp.compare_self

instance : Std.LawfulEqCmp (compare : UInt256 → UInt256 → Ordering) where
  eq_of_compare := by
    intro a b h
    rw [erc20UInt256_compare_eq_val_compare a b] at h
    have hv : a.val = b.val := Std.LawfulEqCmp.eq_of_compare h
    cases a
    cases b
    cases hv
    rfl

/-- Inserting a storage word preserves lookup at a different storage slot. -/
theorem erc20Storage_findD_insert_ne (storage : Storage) (readSlot writeSlot val default : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.insert writeSlot val).findD readSlot default =
      storage.findD readSlot default := by
  unfold Batteries.RBMap.findD
  rw [Batteries.RBMap.find?_insert_of_ne]
  intro hcmp
  exact hne (Std.LawfulEqCmp.eq_of_compare hcmp)

private theorem erc20RBNode_append_toList {α : Type u} (l r : Batteries.RBNode α) :
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

private theorem erc20RBNode_mem_of_mem_append {α : Type u} {x : α} {l r : Batteries.RBNode α}
    (h : x ∈ l.append r) : x ∈ l ∨ x ∈ r := by
  rw [← Batteries.RBNode.mem_toList] at h
  rw [erc20RBNode_append_toList] at h
  simpa [Batteries.RBNode.mem_toList] using h

private theorem erc20RBNode_mem_append_of_mem {α : Type u} {x : α} {l r : Batteries.RBNode α}
    (h : x ∈ l ∨ x ∈ r) : x ∈ l.append r := by
  rw [← Batteries.RBNode.mem_toList]
  rw [erc20RBNode_append_toList]
  simpa [Batteries.RBNode.mem_toList] using h

private theorem erc20RBNode_mem_of_mem_balLeft {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l.balLeft v r) :
    x ∈ l ∨ x = v ∨ x ∈ r := by
  rw [← Batteries.RBNode.mem_toList] at h
  rw [Batteries.RBNode.balLeft_toList] at h
  simpa [Batteries.RBNode.mem_toList] using h

private theorem erc20RBNode_mem_balLeft_of_mem {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l ∨ x = v ∨ x ∈ r) : x ∈ l.balLeft v r := by
  rw [← Batteries.RBNode.mem_toList]
  rw [Batteries.RBNode.balLeft_toList]
  simpa [Batteries.RBNode.mem_toList] using h

private theorem erc20RBNode_mem_of_mem_balRight {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l.balRight v r) :
    x ∈ l ∨ x = v ∨ x ∈ r := by
  rw [← Batteries.RBNode.mem_toList] at h
  rw [Batteries.RBNode.balRight_toList] at h
  simpa [Batteries.RBNode.mem_toList] using h

private theorem erc20RBNode_mem_balRight_of_mem {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l ∨ x = v ∨ x ∈ r) : x ∈ l.balRight v r := by
  rw [← Batteries.RBNode.mem_toList]
  rw [Batteries.RBNode.balRight_toList]
  simpa [Batteries.RBNode.mem_toList] using h

private theorem erc20RBNode_mem_node_of_left {α : Type u} {x y : α} {c : Batteries.RBColor}
    {a b : Batteries.RBNode α} (h : x ∈ a) : x ∈ Batteries.RBNode.node c a y b := by
  exact Or.inr (Or.inl h)

private theorem erc20RBNode_mem_node_of_right {α : Type u} {x y : α} {c : Batteries.RBColor}
    {a b : Batteries.RBNode α} (h : x ∈ b) : x ∈ Batteries.RBNode.node c a y b := by
  exact Or.inr (Or.inr h)

private theorem erc20RBNode_mem_of_mem_del {α : Type u} {x : α} (cut : α → Ordering) :
    ∀ {t : Batteries.RBNode α}, x ∈ Batteries.RBNode.del cut t → x ∈ t
  | .nil, h => by cases h
  | .node c a y b, h => by
      unfold Batteries.RBNode.del at h
      cases hcut : cut y <;> simp [hcut] at h
      · cases hblack : Batteries.RBNode.isBlack a <;> simp [hblack] at h
        · rcases h with hy | hrest
          · exact Or.inl hy
          · rcases hrest with hdel | hb
            · exact erc20RBNode_mem_node_of_left (erc20RBNode_mem_of_mem_del cut hdel)
            · exact erc20RBNode_mem_node_of_right hb
        · rcases erc20RBNode_mem_of_mem_balLeft h with hdel | hrest
          · exact erc20RBNode_mem_node_of_left (erc20RBNode_mem_of_mem_del cut hdel)
          · rcases hrest with hy | hb
            · exact Or.inl hy
            · exact erc20RBNode_mem_node_of_right hb
      · rcases erc20RBNode_mem_of_mem_append h with ha | hb
        · exact erc20RBNode_mem_node_of_left ha
        · exact erc20RBNode_mem_node_of_right hb
      · cases hblack : Batteries.RBNode.isBlack b <;> simp [hblack] at h
        · rcases h with hy | hrest
          · exact Or.inl hy
          · rcases hrest with ha | hdel
            · exact erc20RBNode_mem_node_of_left ha
            · exact erc20RBNode_mem_node_of_right (erc20RBNode_mem_of_mem_del cut hdel)
        · rcases erc20RBNode_mem_of_mem_balRight h with ha | hrest
          · exact erc20RBNode_mem_node_of_left ha
          · rcases hrest with hy | hdel
            · exact Or.inl hy
            · exact erc20RBNode_mem_node_of_right (erc20RBNode_mem_of_mem_del cut hdel)

private theorem erc20RBNode_mem_del_of_mem_ne {α : Type u} {x : α} (cut : α → Ordering) :
    ∀ {t : Batteries.RBNode α}, x ∈ t → cut x ≠ .eq → x ∈ Batteries.RBNode.del cut t
  | .nil, h, _ => by cases h
  | .node c a y b, h, hne => by
      unfold Batteries.RBNode.del
      cases hcut : cut y <;> simp
      · cases hblack : Batteries.RBNode.isBlack a <;> simp
        · rcases h with hy | hrest
          · exact Or.inl hy
          · rcases hrest with ha | hb
            · exact Or.inr (Or.inl (erc20RBNode_mem_del_of_mem_ne cut ha hne))
            · exact Or.inr (Or.inr hb)
        · rcases h with hy | hrest
          · exact erc20RBNode_mem_balLeft_of_mem (Or.inr (Or.inl hy))
          · rcases hrest with ha | hb
            · exact erc20RBNode_mem_balLeft_of_mem
                (Or.inl (erc20RBNode_mem_del_of_mem_ne cut ha hne))
            · exact erc20RBNode_mem_balLeft_of_mem (Or.inr (Or.inr hb))
      · rcases h with hy | hrest
        · exact False.elim (hne (by simpa [hy] using hcut))
        · rcases hrest with ha | hb
          · exact erc20RBNode_mem_append_of_mem (Or.inl ha)
          · exact erc20RBNode_mem_append_of_mem (Or.inr hb)
      · cases hblack : Batteries.RBNode.isBlack b <;> simp
        · rcases h with hy | hrest
          · exact Or.inl hy
          · rcases hrest with ha | hb
            · exact Or.inr (Or.inl ha)
            · exact Or.inr (Or.inr (erc20RBNode_mem_del_of_mem_ne cut hb hne))
        · rcases h with hy | hrest
          · exact erc20RBNode_mem_balRight_of_mem (Or.inr (Or.inl hy))
          · rcases hrest with ha | hb
            · exact erc20RBNode_mem_balRight_of_mem (Or.inl ha)
            · exact erc20RBNode_mem_balRight_of_mem
                (Or.inr (Or.inr (erc20RBNode_mem_del_of_mem_ne cut hb hne)))

private theorem erc20RBNode_mem_of_mem_erase {α : Type u} {x : α}
    (cut : α → Ordering) {t : Batteries.RBNode α} :
    x ∈ Batteries.RBNode.erase cut t → x ∈ t := by
  intro h
  rw [← Batteries.RBNode.mem_toList] at h
  unfold Batteries.RBNode.erase at h
  rw [Batteries.RBNode.setBlack_toList] at h
  exact erc20RBNode_mem_of_mem_del cut (Batteries.RBNode.mem_toList.1 h)

private theorem erc20RBNode_mem_erase_of_mem_ne {α : Type u} {x : α}
    (cut : α → Ordering) {t : Batteries.RBNode α}
    (h : x ∈ t) (hne : cut x ≠ .eq) : x ∈ Batteries.RBNode.erase cut t := by
  rw [← Batteries.RBNode.mem_toList]
  unfold Batteries.RBNode.erase
  rw [Batteries.RBNode.setBlack_toList]
  exact Batteries.RBNode.mem_toList.2 (erc20RBNode_mem_del_of_mem_ne cut h hne)

private theorem erc20RBMap_mem_toList_of_mem_toList_erase {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} {m : Batteries.RBMap α β cmp} {write : α} {pair : α × β}
    (h : pair ∈ (m.erase write).toList) : pair ∈ m.toList := by
  have hnode : pair ∈ (m.erase write).1 := Batteries.RBMap.mem_toList.1 h
  have hmnode : pair ∈ m.1 := by
    unfold Batteries.RBMap.erase Batteries.RBSet.erase at hnode
    exact erc20RBNode_mem_of_mem_erase (fun pair : α × β => cmp write pair.1) hnode
  exact Batteries.RBMap.mem_toList.2 hmnode

private theorem erc20RBMap_mem_toList_erase_of_mem_toList_ne {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} {m : Batteries.RBMap α β cmp} {write : α} {pair : α × β}
    (h : pair ∈ m.toList) (hne : cmp write pair.1 ≠ .eq) : pair ∈ (m.erase write).toList := by
  have hnode : pair ∈ m.1 := Batteries.RBMap.mem_toList.1 h
  have heraseNode : pair ∈ (m.erase write).1 := by
    unfold Batteries.RBMap.erase Batteries.RBSet.erase
    exact erc20RBNode_mem_erase_of_mem_ne (fun pair : α × β => cmp write pair.1) hnode hne
  exact Batteries.RBMap.mem_toList.2 heraseNode

/-- ERC20-local version of the missing generic RBMap lemma: erasing one key preserves
    lookup at a different key. This is storage-map infrastructure, not an ERC20
    layout assumption. -/
private theorem erc20RBMap_find?_erase_ne {α : Type u} {β : Type v}
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
              ⟨y, erc20RBMap_mem_toList_of_mem_toList_erase hyErase, hcmp⟩
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
          ⟨y, erc20RBMap_mem_toList_erase_of_mem_toList_ne hy hcut, hcmp⟩
      cases hnew : (m.erase write).find? read with
      | none =>
          rw [hnew] at hnewSome
          cases hnewSome
      | some v' =>
          have holdFromNew : m.find? read = some v' := by
            obtain ⟨y, hyErase, hcmp⟩ := (Batteries.RBMap.find?_some).1 hnew
            exact (Batteries.RBMap.find?_some).2
              ⟨y, erc20RBMap_mem_toList_of_mem_toList_erase hyErase, hcmp⟩
          rw [hold] at holdFromNew
          cases holdFromNew
          rfl

/-- Erasing a storage word preserves lookup at a different storage slot. -/
theorem erc20Storage_findD_erase_ne (storage : Storage) (readSlot writeSlot default : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.erase writeSlot).findD readSlot default =
      storage.findD readSlot default := by
  unfold Batteries.RBMap.findD
  rw [erc20RBMap_find?_erase_ne]
  exact hne

/-- Updating a storage slot with EVM/Solidity semantics preserves lookup at a different slot.
    Nonzero writes insert; zero writes erase. -/
theorem erc20Storage_findD_update_ne (storage : Storage) (readSlot writeSlot val default : UInt256)
    (hne : readSlot ≠ writeSlot) :
    ((if val == default then storage.erase writeSlot else storage.insert writeSlot val).findD
        readSlot default) =
      storage.findD readSlot default := by
  by_cases hzero : (val == default) = true
  · simpa [hzero] using erc20Storage_findD_erase_ne storage readSlot writeSlot default hne
  · simpa [hzero] using erc20Storage_findD_insert_ne storage readSlot writeSlot val default hne

/-- Looking up the account just inserted at its own address returns that account. -/
theorem erc20AccountMap_find_insert_self (σ : AccountMap) (a : AccountAddress) (acc : Account) :
    (σ.insert a acc).find? a = some acc := by
  rw [Batteries.RBMap.find?_insert_of_eq]
  exact Std.ReflCmp.compare_self

/-! ## ERC20-local storage-layout boundary -/

/-- ERC20-specific storage-layout separation: entries in `balanceOf` and nested `allowance`
    occupy distinct Solidity mapping slots.

    This is the one storage-layout fact not derivable from the current `ffi.KEC` model: Keccak is
    exposed as an opaque external function, with no injectivity or collision-resistance theorem.
    All ordinary map update/lookup behavior is proved above; this assumption is only about the
    cryptographic slot derivation used by Solidity mappings. -/
axiom erc20BalanceOfSlot_ne_allowanceSlot (owner spender : KeyValue) :
    erc20BalanceOfSlot owner ≠ erc20AllowanceSlot owner spender

/-- ABI-encoding `true` for ERC20's bool-returning functions is the one-word value `1`. -/
theorem erc20BoolTrueReturnEncoding :
    encodeReturnValue? (.elem .bool) (.bool true) = some (UInt256.toByteArray ⟨1⟩) := by
  rw [toByteArray_eq_toBytesBE]
  simp [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, abiTupleHeadSize?,
    staticABIEncodedSize?, isDynamicABIType, encodeABIValuesFrom?, encodeABIValue?,
    encodeABIWord?, Bool.toUInt256_true]
  rfl

end ERC20
