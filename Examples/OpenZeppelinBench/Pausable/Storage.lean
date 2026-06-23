import Examples.OpenZeppelinBench.Pausable.Bytecode
import Examples.SimpleAuction.Storage
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Pausable

/-!
# Pausable storage helpers

The benchmark has one packed `bool` in slot `0`, byte offset `0`.  Most low-byte storage facts are
reused from `SimpleAuction.Storage`; cross-example reuse here is a library-generalization candidate
for `Reasoning.Storage` / packed scalar storage.
-/

def pausedRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

def pausedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (pausedRawWord σ I) ⟨255⟩

def pausedSetTrueWord (w : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land w (UInt256.lnot ⟨255⟩)) ⟨1⟩

def pausedSetFalseWord (w : UInt256) : UInt256 :=
  UInt256.land w (UInt256.lnot ⟨255⟩)

def pausePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩ (pausedSetTrueWord (pausedRawWord σ I))

def unpausePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩ (pausedSetFalseWord (pausedRawWord σ I))

def pausePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (pausedSetTrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩))

def unpausePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (pausedSetFalseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩))

theorem pausableStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (boolLoc slot)
      = wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  simpa [boolLoc, SimpleAuction.simpleAuctionBoolLoc]
    using SimpleAuction.simpleAuctionStorageLocLoad_bool_offset0 evm slot

theorem pausableStorageLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm (boolLoc slot) = .bool false := by
  simpa [boolLoc, SimpleAuction.simpleAuctionBoolLoc]
    using SimpleAuction.simpleAuctionStorageLocLoad_bool_offset0_false evm slot hzero

theorem pausableStorageLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm (boolLoc slot) = .bool true := by
  simpa [boolLoc, SimpleAuction.simpleAuctionBoolLoc]
    using SimpleAuction.simpleAuctionStorageLocLoad_bool_offset0_true evm slot hnz

theorem pausableStorageLocStore_bool_true_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (boolLoc slot) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (pausedSetTrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  simpa [boolLoc, SimpleAuction.simpleAuctionBoolLoc, pausedSetTrueWord]
    using SimpleAuction.simpleAuctionStorageLocStore_bool_true_offset0 evm slot

-- LIBRARY CANDIDATE: `Reasoning.Storage`, packed `bool` store at byte offset 0.
theorem pausablePackedSetFalseWord_eq (w : UInt256) :
    pausedSetFalseWord w = UInt256.ofNat (256 * (w.toNat / 256)) := by
  unfold pausedSetFalseWord
  apply u256_inj
  rw [SimpleAuction.simpleAuctionU256_land_toNat]
  have hlnot : (UInt256.lnot (⟨255⟩ : UInt256)).toNat = 2 ^ 256 - 2 ^ 8 := by
    native_decide
  rw [hlnot]
  have hwlt : w.toNat < 2 ^ 256 := by
    change w.val.val < 2 ^ 256
    simpa [UInt256.size] using w.val.isLt
  rw [SimpleAuction.simpleAuctionNatLandClearLow8 w.toNat hwlt]
  have hlt : w.toNat / 2 ^ 8 * 2 ^ 8 < UInt256.size :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) w.val.isLt
  rw [Nat.mod_eq_of_lt hlt]
  have hlt' : 256 * (w.toNat / 256) < UInt256.size := by
    simpa [Nat.mul_comm] using hlt
  rw [show 2 ^ 8 = 256 by norm_num]
  rw [Nat.mul_comm (w.toNat / 256) 256]
  rw [ulit_toNat' _ hlt']

theorem pausablePackedSetFalseWord_toNat (w : UInt256) :
    (pausedSetFalseWord w).toNat = 256 * (w.toNat / 256) := by
  rw [pausablePackedSetFalseWord_eq]
  have hlt : 256 * (w.toNat / 256) < UInt256.size := by
    have hle : 256 * (w.toNat / 256) ≤ w.toNat :=
      Nat.mul_div_le w.toNat 256
    exact lt_of_le_of_lt hle w.val.isLt
  exact ulit_toNat' _ hlt

-- LIBRARY CANDIDATE: `Reasoning.Storage`, packed `bool` store at byte offset 0.
theorem pausableStorageLocStore_bool_false_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (boolLoc slot) (.bool false) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (pausedSetFalseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord boolLoc pausedSetFalseWord
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
      [0] by native_decide]
  rw [fromBytes'_append, SimpleAuction.simpleAuctionFromBytes'_drop1_wordLE]
  simp [fromBytes']
  simpa [pausedSetFalseWord] using
    (pausablePackedSetFalseWord_toNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).symm

theorem pausableStorageStore_accountMap
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).accountMap =
      sstoreAccountMap a evm.accountMap slot val := by
  exact SimpleAuction.simpleAuctionStorageStore_accountMap evm a slot val

theorem pausableStorageStore_createdAccounts
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).createdAccounts = evm.createdAccounts := by
  exact SimpleAuction.simpleAuctionStorageStore_createdAccounts evm a slot val

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
private theorem pausableRBNode_append_toList {α : Type u} (l r : Batteries.RBNode α) :
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
private theorem pausableRBNode_mem_of_mem_append {α : Type u} {x : α}
    {l r : Batteries.RBNode α} (h : x ∈ l.append r) : x ∈ l ∨ x ∈ r := by
  rw [← Batteries.RBNode.mem_toList] at h
  rw [pausableRBNode_append_toList] at h
  simpa [Batteries.RBNode.mem_toList] using h

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
private theorem pausableRBNode_mem_of_mem_balLeft {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l.balLeft v r) :
    x ∈ l ∨ x = v ∨ x ∈ r := by
  rw [← Batteries.RBNode.mem_toList] at h
  rw [Batteries.RBNode.balLeft_toList] at h
  simpa [Batteries.RBNode.mem_toList] using h

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
private theorem pausableRBNode_mem_of_mem_balRight {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l.balRight v r) :
    x ∈ l ∨ x = v ∨ x ∈ r := by
  rw [← Batteries.RBNode.mem_toList] at h
  rw [Batteries.RBNode.balRight_toList] at h
  simpa [Batteries.RBNode.mem_toList] using h

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
private theorem pausableRBNode_not_memP_del {α : Type u} {cmp : α → α → Ordering}
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
            · exact pausableRBNode_not_memP_del ha
                (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)
            · exact nomatch heq.symm.trans
                (Batteries.RBNode.IsCut.lt_trans
                  (Batteries.RBNode.All_def.1 yb _ hbmem).1 hcut)
          · rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
            rcases pausableRBNode_mem_of_mem_balLeft hx with hdel | hrest
            · exact pausableRBNode_not_memP_del ha
                (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)
            · rcases hrest with rfl | hbmem
              · exact nomatch heq.symm.trans hcut
              · exact nomatch heq.symm.trans
                  (Batteries.RBNode.IsCut.lt_trans
                    (Batteries.RBNode.All_def.1 yb _ hbmem).1 hcut)
      | eq =>
          simp [hcut] at h
          rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
          rcases pausableRBNode_mem_of_mem_append hx with hamem | hbmem
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
            · exact pausableRBNode_not_memP_del hb
                (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)
          · rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
            rcases pausableRBNode_mem_of_mem_balRight hx with hamem | hrest
            · exact nomatch heq.symm.trans
                (Batteries.RBNode.IsCut.gt_trans
                  (Batteries.RBNode.All_def.1 ay _ hamem).1 hcut)
            · rcases hrest with rfl | hdel
              · exact nomatch heq.symm.trans hcut
              · exact pausableRBNode_not_memP_del hb
                  (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
private theorem pausableRBNode_not_memP_erase {α : Type u} {cmp : α → α → Ordering}
    {cut : α → Ordering} [Std.TransCmp cmp] [Batteries.RBNode.IsStrictCut cmp cut]
    {t : Batteries.RBNode α} (ht : Batteries.RBNode.Ordered cmp t) :
    ¬ Batteries.RBNode.MemP cut (Batteries.RBNode.erase cut t) := by
  intro h
  rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
  have hxdel : x ∈ Batteries.RBNode.del cut t := by
    rw [← Batteries.RBNode.mem_toList] at hx ⊢
    unfold Batteries.RBNode.erase at hx
    simpa using hx
  exact pausableRBNode_not_memP_del ht
    (Batteries.RBNode.memP_def.2 ⟨x, hxdel, heq⟩)

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
private theorem pausableRBMap_find?_erase_self {α : Type u} {β : Type v}
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
      have hno := pausableRBNode_not_memP_erase
        (cmp := Ordering.byKey Prod.fst cmp)
        (cut := Ordering.byKey Prod.fst cmp (write, v))
        (t := m.1) m.2.out.1
      cases hno (Batteries.RBNode.memP_def.2 ⟨(y, v), hmemNode, hcmp⟩)

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
theorem pausableStorage_find?_erase_self (storage : Storage) (slot : UInt256) :
    (storage.erase slot).find? slot = none :=
  pausableRBMap_find?_erase_self storage slot

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
theorem pausableAccountEquiv_erase_storage_of_equiv {acc₁ acc₂ : Account}
    (slot : UInt256) (hacc : accountEquiv acc₁ acc₂) :
    accountEquiv { acc₁ with storage := acc₁.storage.erase slot }
      { acc₂ with storage := acc₂.storage.erase slot } := by
  rcases hacc with ⟨hnonce, hbalance, hcode, htstor, hstorage⟩
  refine ⟨hnonce, hbalance, hcode, htstor, ?_⟩
  intro readSlot
  by_cases hread : readSlot = slot
  · subst readSlot
    rw [pausableStorage_find?_erase_self, pausableStorage_find?_erase_self]
  · rw [storage_find?_erase_ne acc₁.storage readSlot slot hread,
      storage_find?_erase_ne acc₂.storage readSlot slot hread, hstorage readSlot]

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
theorem pausableAccountMapEquiv_sstoreAccountMap {σ τ : AccountMap}
    (a : AccountAddress) (slot val : UInt256)
    (hστ : accountMapEquiv σ τ) :
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
              pausableAccountEquiv_erase_storage_of_equiv slot hacc
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
theorem pausableEVMStateEquiv_storageStore_codeOwner {evm₁ evm₂ : EVM.State}
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
    exact pausableAccountMapEquiv_sstoreAccountMap evm₂.executionEnv.codeOwner slot val₁
      h.accountMap

theorem pausePostState_accountMap (evm : EVM.State) :
    (pausePostState evm).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (pausedSetTrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)) := by
  simp [pausePostState, pausableStorageStore_accountMap]

theorem unpausePostState_accountMap (evm : EVM.State) :
    (unpausePostState evm).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (pausedSetFalseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)) := by
  simp [unpausePostState, pausableStorageStore_accountMap]

theorem pausePostState_createdAccounts (evm : EVM.State) :
    (pausePostState evm).createdAccounts = evm.createdAccounts := by
  simp [pausePostState, pausableStorageStore_createdAccounts]

theorem unpausePostState_createdAccounts (evm : EVM.State) :
    (unpausePostState evm).createdAccounts = evm.createdAccounts := by
  simp [unpausePostState, pausableStorageStore_createdAccounts]

end OpenZeppelinBench.Pausable
