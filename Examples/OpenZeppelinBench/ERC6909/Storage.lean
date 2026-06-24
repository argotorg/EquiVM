import Examples.OpenZeppelinBench.ERC6909.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.ERC6909

/-! ## ERC6909-wide storage helpers -/

open Batteries

private theorem rbnode_append_toList {α : Type u} (l r : RBNode α) :
    (l.append r).toList = l.toList ++ r.toList := by
  fun_induction RBNode.append l r <;> simp [List.append_assoc]
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

private theorem rbnode_mem_of_mem_append {α : Type u} {x : α} {l r : RBNode α}
    (h : x ∈ l.append r) : x ∈ l ∨ x ∈ r := by
  rw [← RBNode.mem_toList] at h
  rw [rbnode_append_toList] at h
  simpa [RBNode.mem_toList] using h

private theorem rbnode_mem_of_mem_balLeft {α : Type u} {x v : α}
    {l r : RBNode α} (h : x ∈ l.balLeft v r) :
    x ∈ l ∨ x = v ∨ x ∈ r := by
  rw [← RBNode.mem_toList] at h
  rw [RBNode.balLeft_toList] at h
  simpa [RBNode.mem_toList] using h

private theorem rbnode_mem_of_mem_balRight {α : Type u} {x v : α}
    {l r : RBNode α} (h : x ∈ l.balRight v r) :
    x ∈ l ∨ x = v ∨ x ∈ r := by
  rw [← RBNode.mem_toList] at h
  rw [RBNode.balRight_toList] at h
  simpa [RBNode.mem_toList] using h

private theorem rbnode_mem_del_cut_ne {α : Type u} {cmp : α → α → Ordering}
    {cut : α → Ordering} [Std.TransCmp cmp] [RBNode.IsStrictCut cmp cut] :
    ∀ {t : RBNode α} {x : α}, t.Ordered cmp → x ∈ t.del cut → cut x ≠ .eq
  | .nil, _, _, h => by cases h
  | .node _ a y b, x, ht, hmem => by
      rcases ht with ⟨ay, yb, ha, hb⟩
      unfold RBNode.del at hmem
      cases hcut : cut y
      · cases hblack : a.isBlack
        · have hmemnode : x = y ∨ x ∈ RBNode.del cut a ∨ x ∈ b := by
            simpa [hcut, hblack] using hmem
          rcases hmemnode with hy | hdel | hr
          · subst x
            exact by simp [hcut]
          · exact rbnode_mem_del_cut_ne ha hdel
          · have hyx : cmp y x = .lt := (RBNode.All_def.1 yb x hr).1
            have hxlt : cut x = .lt := RBNode.IsCut.lt_trans hyx hcut
            intro hxeq
            cases hxeq.symm.trans hxlt
        · have hmembal : x ∈ (RBNode.del cut a).balLeft y b := by
            simpa [hcut, hblack] using hmem
          rcases rbnode_mem_of_mem_balLeft hmembal with hdel | hy | hr
          · exact rbnode_mem_del_cut_ne ha hdel
          · subst x
            exact by simp [hcut]
          · have hyx : cmp y x = .lt := (RBNode.All_def.1 yb x hr).1
            have hxlt : cut x = .lt := RBNode.IsCut.lt_trans hyx hcut
            intro hxeq
            cases hxeq.symm.trans hxlt
      · have hmemapp : x ∈ a.append b := by
          simpa [hcut] using hmem
        rcases rbnode_mem_of_mem_append hmemapp with hl | hr
        · have hxy : cmp x y = .lt := (RBNode.All_def.1 ay x hl).1
          have hyx : cmp y x = .gt := Std.OrientedCmp.gt_iff_lt.2 hxy
          have hcmp : cmp y x = cut x := RBNode.IsStrictCut.exact hcut
          intro hxeq
          have hbad : (Ordering.gt : Ordering) = .eq := by
            rw [← hyx, hcmp, hxeq]
          cases hbad
        · have hyx : cmp y x = .lt := (RBNode.All_def.1 yb x hr).1
          have hcmp : cmp y x = cut x := RBNode.IsStrictCut.exact hcut
          intro hxeq
          have hbad : (Ordering.lt : Ordering) = .eq := by
            rw [← hyx, hcmp, hxeq]
          cases hbad
      · cases hblack : b.isBlack
        · have hmemnode : x = y ∨ x ∈ a ∨ x ∈ RBNode.del cut b := by
            simpa [hcut, hblack] using hmem
          rcases hmemnode with hy | hl | hdel
          · subst x
            exact by simp [hcut]
          · have hxy : cmp x y = .lt := (RBNode.All_def.1 ay x hl).1
            have hxgt : cut x = .gt := RBNode.IsCut.gt_trans hxy hcut
            intro hxeq
            cases hxeq.symm.trans hxgt
          · exact rbnode_mem_del_cut_ne hb hdel
        · have hmembal : x ∈ a.balRight y (RBNode.del cut b) := by
            simpa [hcut, hblack] using hmem
          rcases rbnode_mem_of_mem_balRight hmembal with hl | hy | hdel
          · have hxy : cmp x y = .lt := (RBNode.All_def.1 ay x hl).1
            have hxgt : cut x = .gt := RBNode.IsCut.gt_trans hxy hcut
            intro hxeq
            cases hxeq.symm.trans hxgt
          · subst x
            exact by simp [hcut]
          · exact rbnode_mem_del_cut_ne hb hdel

private theorem rbnode_find?_erase_none {α : Type u} {cmp : α → α → Ordering}
    {cut : α → Ordering} [Std.TransCmp cmp] [RBNode.IsStrictCut cmp cut]
    {t : RBNode α} (ht : t.Ordered cmp) :
    (t.erase cut).find? cut = none := by
  cases hfind : (t.erase cut).find? cut with
  | none => rfl
  | some x =>
      have hx : x ∈ t.erase cut ∧ cut x = .eq :=
        (RBNode.Ordered.find?_some (cmp := cmp) (cut := cut)
          (x := x) (RBNode.Ordered.erase (cut := cut) ht)).1 hfind
      have hxdel : x ∈ RBNode.del cut t := by
        rw [← RBNode.mem_toList] at hx
        unfold RBNode.erase at hx
        simpa using hx.1
      exact False.elim ((rbnode_mem_del_cut_ne ht hxdel) hx.2)

private theorem erc6909StorageFindEraseSelf (storage : Storage) (slot : UInt256) :
    (storage.erase slot).find? slot = none := by
  cases storage with
  | mk tree wf =>
      have ht := wf.out.1
      change Option.map Prod.snd
          (RBNode.find? (fun x : UInt256 × UInt256 => compare slot x.1)
            (RBNode.erase (fun x : UInt256 × UInt256 => compare slot x.1) tree)) = none
      rw [rbnode_find?_erase_none
        (cmp := Ordering.byKey Prod.fst compare)
        (cut := fun x : UInt256 × UInt256 => compare slot x.1) ht]
      rfl

private theorem erc6909AccountEquivStorageUpdate {acc₁ acc₂ : Account}
    (slot val : UInt256) (hacc : accountEquiv acc₁ acc₂) :
    accountEquiv
      (if val == (default : UInt256) then {acc₁ with storage := acc₁.storage.erase slot}
       else {acc₁ with storage := acc₁.storage.insert slot val})
      (if val == (default : UInt256) then {acc₂ with storage := acc₂.storage.erase slot}
       else {acc₂ with storage := acc₂.storage.insert slot val}) := by
  by_cases hzero : (val == (default : UInt256)) = true
  · simp only [hzero, if_true]
    rcases hacc with ⟨hn, hb, hc, ht, hs⟩
    refine ⟨hn, hb, hc, ht, ?_⟩
    intro readSlot
    by_cases hread : readSlot = slot
    · subst readSlot
      rw [erc6909StorageFindEraseSelf, erc6909StorageFindEraseSelf]
    · rw [storage_find?_erase_ne acc₁.storage readSlot slot hread,
        storage_find?_erase_ne acc₂.storage readSlot slot hread]
      exact hs readSlot
  · simp only [hzero]
    exact accountEquiv_insert_storage_of_equiv slot val hacc

theorem erc6909AccountMapEquivSstore {σ τ : AccountMap}
    (a : AccountAddress) (slot val : UInt256)
    (hστ : accountMapEquiv σ τ) :
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
            have hacc : accountEquiv accσ accτ := by
              simpa [hσ, hτ] using hστ
            simpa [hσ, hτ, Option.option, accountMap_find_insert_self] using
              erc6909AccountEquivStorageUpdate slot val hacc
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

theorem erc6909StorageStoreAccountMapEquiv {evm1 evm2 : EVM.State}
    (hAccounts : accountMapEquiv evm1.accountMap evm2.accountMap)
    (addr : AccountAddress) (slot val : UInt256) :
    accountMapEquiv (Solm.EVM.storageStore evm1 addr slot val).accountMap
      (Solm.EVM.storageStore evm2 addr slot val).accountMap := by
  rw [storageStore_accountMap, storageStore_accountMap]
  exact erc6909AccountMapEquivSstore addr slot val hAccounts

theorem erc6909EVMStateEquivStorageStore {evm₁ evm₂ : EVM.State}
    (h : EVMStateEquiv evm₁ evm₂)
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
  · exact erc6909StorageStoreAccountMapEquiv h.accountMap addr₁ slot val₁

theorem erc6909EVMStateEquivStorageStoreCodeOwner {evm₁ evm₂ : EVM.State}
    (h : EVMStateEquiv evm₁ evm₂)
    (slot : UInt256) {val₁ val₂ : UInt256} (hval : val₁ = val₂) :
    EVMStateEquiv
      (Solm.EVM.storageStore evm₁ evm₁.executionEnv.codeOwner slot val₁)
      (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner slot val₂) :=
  erc6909EVMStateEquivStorageStore h (congrArg ExecutionEnv.codeOwner h.executionEnv) slot hval

/-- Loading a full-slot Solidity `uint256` returns the source-level integer for that word. -/
theorem erc6909StorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
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
  unfold storageLocLoad wordLoc wordToElem
  simp only [uint256Int, Fin.val_zero, Nat.zero_add]
  congr
  rw [htake]
  exact fromBytes'_toBytesLEWithSizeProof _

/-- `wordOfInt (Int.ofNat a.toNat) = a` for an EVM word. -/
theorem erc6909WordOfInt_ofNat_toNat (a : UInt256) :
    EVM.wordOfInt (Int.ofNat a.toNat) = a := by
  rw [EVM.wordOfInt, if_neg (by simp)]
  apply u256_inj
  rw [show (Int.ofNat a.toNat).toNat = a.toNat from rfl]
  show a.toNat % EVM.twoPow 256 = a.toNat
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.val.isLt (by decide))

/-- Storing a full-slot Solidity `uint256` is the corresponding EVM storage write. -/
theorem erc6909StorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (wordLoc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  unfold storageLocStore storageLocWriteWord wordLoc
  simp only [valueToWord, erc6909WordOfInt_ofNat_toNat, bind, Option.bind, pure]
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

end OpenZeppelinBench.ERC6909
