import Benchmarks.Dss.Flipper.BidAccess

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Generic `delete bids[id]` helpers -/

abbrev bidEvaledBaseRefOfWord (id : UInt256) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (.int (Int.ofNat id.toNat))] }

abbrev bidDeleteSlot2ClearedWord : UInt256 :=
  ⟨0⟩

abbrev bidDeletedEVM (evm : EVM.State) (id : UInt256) : EVM.State :=
  let base := bidBaseOfWord id
  let evm0 := Solm.EVM.storageStore evm evm.executionEnv.codeOwner base ⟨0⟩
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (base + ⟨1⟩) ⟨0⟩
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner (base + ⟨2⟩)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner (base + ⟨2⟩)) ⟨0⟩)
  let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner (base + ⟨2⟩)
    (setUint48Offset20Word
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner (base + ⟨2⟩)) ⟨0⟩)
  let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner (base + ⟨2⟩)
    (setUint48Offset26Word
      (Solm.EVM.storageLoad evm3 evm3.executionEnv.codeOwner (base + ⟨2⟩)) ⟨0⟩)
  let evm5 := Solm.EVM.storageStore evm4 evm4.executionEnv.codeOwner (base + ⟨3⟩)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner (base + ⟨3⟩)) ⟨0⟩)
  let evm6 := Solm.EVM.storageStore evm5 evm5.executionEnv.codeOwner (base + ⟨4⟩)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm5 evm5.executionEnv.codeOwner (base + ⟨4⟩)) ⟨0⟩)
  Solm.EVM.storageStore evm6 evm6.executionEnv.codeOwner (base + ⟨5⟩) ⟨0⟩

abbrev bidDeleteCollapsedAccountMap (owner : AccountAddress) (σ : AccountMap)
    (id : UInt256) : AccountMap :=
  let base := bidBaseOfWord id
  let σ0 := sstoreAccountMap owner σ base ⟨0⟩
  let σ1 := sstoreAccountMap owner σ0 (base + ⟨1⟩) ⟨0⟩
  let σ2 := sstoreAccountMap owner σ1 (base + ⟨2⟩) ⟨0⟩
  let σ3 := sstoreAccountMap owner σ2 (base + ⟨3⟩)
    (setAddressOffset0Word
      ((σ2.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD (base + ⟨3⟩) ⟨0⟩))
      ⟨0⟩)
  let σ4 := sstoreAccountMap owner σ3 (base + ⟨4⟩)
    (setAddressOffset0Word
      ((σ3.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD (base + ⟨4⟩) ⟨0⟩))
      ⟨0⟩)
  sstoreAccountMap owner σ4 (base + ⟨5⟩) ⟨0⟩

abbrev bidDeleteSourceAccountMap (owner : AccountAddress) (σ : AccountMap)
    (id : UInt256) : AccountMap :=
  let base := bidBaseOfWord id
  let σ0 := sstoreAccountMap owner σ base ⟨0⟩
  let σ1 := sstoreAccountMap owner σ0 (base + ⟨1⟩) ⟨0⟩
  let σ2 := sstoreAccountMap owner σ1 (base + ⟨2⟩)
    (setAddressOffset0Word
      ((σ1.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD (base + ⟨2⟩) ⟨0⟩))
      ⟨0⟩)
  let σ3 := sstoreAccountMap owner σ2 (base + ⟨2⟩)
    (setUint48Offset20Word
      ((σ2.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD (base + ⟨2⟩) ⟨0⟩))
      ⟨0⟩)
  let σ4 := sstoreAccountMap owner σ3 (base + ⟨2⟩)
    (setUint48Offset26Word
      ((σ3.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD (base + ⟨2⟩) ⟨0⟩))
      ⟨0⟩)
  let σ5 := sstoreAccountMap owner σ4 (base + ⟨3⟩)
    (setAddressOffset0Word
      ((σ4.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD (base + ⟨3⟩) ⟨0⟩))
      ⟨0⟩)
  let σ6 := sstoreAccountMap owner σ5 (base + ⟨4⟩)
    (setAddressOffset0Word
      ((σ5.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD (base + ⟨4⟩) ⟨0⟩))
      ⟨0⟩)
  sstoreAccountMap owner σ6 (base + ⟨5⟩) ⟨0⟩

theorem evalStorageRef_bidRef_of_get_id {evm : EVM.State} {locals : Store} {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    evalStorageRef config { contract := contract, locals := locals } evm (bidRef (.var "id")) =
      .ok (bidEvaledBaseRefOfWord id) := by
  rw [evalStorageRef, bidRef]
  simp only [evalStorageRefSteps, evalStorageRefStep, evalExpr?, EvalResult.bind, bind,
    pure, EvalResult.ofOption]
  rw [hid]
  simp [bidEvaledBaseRefOfWord, valueToKey?]

theorem resolveStorageRef_bidRef_of_get_id {evm : EVM.State} {locals : Store} {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    resolveStorageRef? config { contract := contract, locals := locals } evm
      (bidRef (.var "id")) = .ok (bidEvaledBaseRefOfWord id, BidStructTy) := by
  rw [resolveStorageRef?]
  simp only [EvalResult.bind, bind]
  rw [evalStorageRef_bidRef_of_get_id (evm := evm) (locals := locals) (id := id) hid]
  simp only [bidRef]
  rw [hbids]
  simp [bidEvaledBaseRefOfWord, contract, storageDecls, storageTypeAt?, storageTypeStep?,
    EvalResult.ofOption, pure]

theorem clearStorage_bid_bid {evm : EVM.State} {id : UInt256} :
    clearStorage? config evm
      { base := "bids", steps := [.mindex (.int (Int.ofNat id.toNat)), .field "bid"] }
      uint256St =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (bidBaseOfWord id) ⟨0⟩) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [uint256St, config, storageLayout, solidityStorageLayout, EvalResult.ofOption]
  simp only [storageLayoutRaw, bidsBase_intOfNatWord]
  change (match storageLocStore evm (wordLoc (bidBaseOfWord id))
      (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) with
    | some a => EvalResult.ok a
    | none => EvalResult.error EvalError.storageError) = _
  rw [flipperStorageLocStore_uint256]

theorem clearStorage_bid_lot {evm : EVM.State} {id : UInt256} :
    clearStorage? config evm
      { base := "bids", steps := [.mindex (.int (Int.ofNat id.toNat)), .field "lot"] }
      uint256St =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨1⟩) ⟨0⟩) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [uint256St, config, storageLayout, solidityStorageLayout, EvalResult.ofOption]
  simp only [storageLayoutRaw, bidsBase_intOfNatWord]
  change (match storageLocStore evm (wordLoc (bidBaseOfWord id + ⟨1⟩))
      (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) with
    | some a => EvalResult.ok a
    | none => EvalResult.error EvalError.storageError) = _
  rw [show bidSlotOfWord id ⟨1⟩ = bidBaseOfWord id + ⟨1⟩ by rfl]
  rw [flipperStorageLocStore_uint256]

theorem clearStorage_bid_guy {evm : EVM.State} {id : UInt256} :
    clearStorage? config evm
      { base := "bids", steps := [.mindex (.int (Int.ofNat id.toNat)), .field "guy"] }
      addrSt =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨2⟩)
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨2⟩))
            ⟨0⟩)) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [addrSt, config, storageLayout, solidityStorageLayout, EvalResult.ofOption]
  simp only [storageLayoutRaw, bidsBase_intOfNatWord]
  change (match storageLocStore evm (addrLoc (bidBaseOfWord id + ⟨2⟩))
      (.address (AccountAddress.ofNat (⟨0⟩ : UInt256).toNat)) with
    | some a => EvalResult.ok a
    | none => EvalResult.error EvalError.storageError) = _
  rw [show bidSlotOfWord id ⟨2⟩ = bidBaseOfWord id + ⟨2⟩ by rfl]
  rw [show addrLoc (bidBaseOfWord id + ⟨2⟩) =
    addressOffset0Loc (bidBaseOfWord id + ⟨2⟩) by rfl]
  rw [storageLocStore_address_offset0 evm (bidBaseOfWord id + ⟨2⟩) ⟨0⟩
    (by decide : (⟨0⟩ : UInt256).toNat < EVM.addressModulus)]

theorem clearStorage_bid_tic {evm : EVM.State} {id : UInt256} :
    clearStorage? config evm
      { base := "bids", steps := [.mindex (.int (Int.ofNat id.toNat)), .field "tic"] }
      uint48St =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨2⟩)
          (setUint48Offset20Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨2⟩))
            ⟨0⟩)) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [uint48St, config, storageLayout, solidityStorageLayout, EvalResult.ofOption]
  simp only [storageLayoutRaw, bidsBase_intOfNatWord]
  change (match storageLocStore evm (uint48Loc (bidBaseOfWord id + ⟨2⟩)
      ⟨20, by decide⟩ (by decide)) (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) with
    | some a => EvalResult.ok a
    | none => EvalResult.error EvalError.storageError) = _
  rw [show bidSlotOfWord id ⟨2⟩ = bidBaseOfWord id + ⟨2⟩ by rfl]
  rw [flipperStorageLocStore_uint48_offset20 evm (bidBaseOfWord id + ⟨2⟩) ⟨0⟩
    (by decide : (⟨0⟩ : UInt256).toNat < 2 ^ 48)]

theorem clearStorage_bid_end {evm : EVM.State} {id : UInt256} :
    clearStorage? config evm
      { base := "bids", steps := [.mindex (.int (Int.ofNat id.toNat)), .field "end"] }
      uint48St =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨2⟩)
          (setUint48Offset26Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨2⟩))
            ⟨0⟩)) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [uint48St, config, storageLayout, solidityStorageLayout, EvalResult.ofOption]
  simp only [storageLayoutRaw, bidsBase_intOfNatWord]
  change (match storageLocStore evm (uint48Loc (bidBaseOfWord id + ⟨2⟩)
      ⟨26, by decide⟩ (by decide)) (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) with
    | some a => EvalResult.ok a
    | none => EvalResult.error EvalError.storageError) = _
  rw [show bidSlotOfWord id ⟨2⟩ = bidBaseOfWord id + ⟨2⟩ by rfl]
  rw [flipperStorageLocStore_uint48_offset26 evm (bidBaseOfWord id + ⟨2⟩) ⟨0⟩
    (by decide : (⟨0⟩ : UInt256).toNat < 2 ^ 48)]

theorem clearStorage_bid_usr {evm : EVM.State} {id : UInt256} :
    clearStorage? config evm
      { base := "bids", steps := [.mindex (.int (Int.ofNat id.toNat)), .field "usr"] }
      addrSt =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨3⟩)
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨3⟩))
            ⟨0⟩)) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [addrSt, config, storageLayout, solidityStorageLayout, EvalResult.ofOption]
  simp only [storageLayoutRaw, bidsBase_intOfNatWord]
  change (match storageLocStore evm (addrLoc (bidBaseOfWord id + ⟨3⟩))
      (.address (AccountAddress.ofNat (⟨0⟩ : UInt256).toNat)) with
    | some a => EvalResult.ok a
    | none => EvalResult.error EvalError.storageError) = _
  rw [show bidSlotOfWord id ⟨3⟩ = bidBaseOfWord id + ⟨3⟩ by rfl]
  rw [show addrLoc (bidBaseOfWord id + ⟨3⟩) =
    addressOffset0Loc (bidBaseOfWord id + ⟨3⟩) by rfl]
  rw [storageLocStore_address_offset0 evm (bidBaseOfWord id + ⟨3⟩) ⟨0⟩
    (by decide : (⟨0⟩ : UInt256).toNat < EVM.addressModulus)]

theorem clearStorage_bid_gal {evm : EVM.State} {id : UInt256} :
    clearStorage? config evm
      { base := "bids", steps := [.mindex (.int (Int.ofNat id.toNat)), .field "gal"] }
      addrSt =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨4⟩)
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨4⟩))
            ⟨0⟩)) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [addrSt, config, storageLayout, solidityStorageLayout, EvalResult.ofOption]
  simp only [storageLayoutRaw, bidsBase_intOfNatWord]
  change (match storageLocStore evm (addrLoc (bidBaseOfWord id + ⟨4⟩))
      (.address (AccountAddress.ofNat (⟨0⟩ : UInt256).toNat)) with
    | some a => EvalResult.ok a
    | none => EvalResult.error EvalError.storageError) = _
  rw [show bidSlotOfWord id ⟨4⟩ = bidBaseOfWord id + ⟨4⟩ by rfl]
  rw [show addrLoc (bidBaseOfWord id + ⟨4⟩) =
    addressOffset0Loc (bidBaseOfWord id + ⟨4⟩) by rfl]
  rw [storageLocStore_address_offset0 evm (bidBaseOfWord id + ⟨4⟩) ⟨0⟩
    (by decide : (⟨0⟩ : UInt256).toNat < EVM.addressModulus)]

theorem clearStorage_bid_tab {evm : EVM.State} {id : UInt256} :
    clearStorage? config evm
      { base := "bids", steps := [.mindex (.int (Int.ofNat id.toNat)), .field "tab"] }
      uint256St =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨5⟩) ⟨0⟩) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [uint256St, config, storageLayout, solidityStorageLayout, EvalResult.ofOption]
  simp only [storageLayoutRaw, bidsBase_intOfNatWord]
  change (match storageLocStore evm (wordLoc (bidBaseOfWord id + ⟨5⟩))
      (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) with
    | some a => EvalResult.ok a
    | none => EvalResult.error EvalError.storageError) = _
  rw [show bidSlotOfWord id ⟨5⟩ = bidBaseOfWord id + ⟨5⟩ by rfl]
  rw [flipperStorageLocStore_uint256]

theorem bid_slot2_delete_word {old : UInt256} :
    setUint48Offset26Word
        (setUint48Offset20Word (setAddressOffset0Word old ⟨0⟩) ⟨0⟩) ⟨0⟩ =
      ⟨0⟩ := by
  apply u256_inj
  have haddr :
      (setAddressOffset0Word old ⟨0⟩).toNat =
        (old.toNat / 2 ^ 160) * 2 ^ 160 := by
    simpa using setAddressOffset0Word_toNat old ⟨0⟩
      (by decide : (⟨0⟩ : UInt256).toNat < EVM.addressModulus)
  have htic :
      (setUint48Offset20Word (setAddressOffset0Word old ⟨0⟩) ⟨0⟩).toNat =
        (old.toNat / 2 ^ 208) * 2 ^ 208 := by
    rw [setUint48Offset20Word_toNat _ ⟨0⟩
      (by decide : (⟨0⟩ : UInt256).toNat < 2 ^ 48)]
    rw [haddr]
    have hmod : old.toNat / 2 ^ 160 * 2 ^ 160 % 2 ^ 160 = 0 := by
      rw [Nat.mul_comm]
      exact Nat.mul_mod_right (2 ^ 160) (old.toNat / 2 ^ 160)
    have hdiv :
        old.toNat / 2 ^ 160 * 2 ^ 160 / 2 ^ 208 = old.toNat / 2 ^ 208 := by
      rw [show 2 ^ 208 = 2 ^ 160 * 2 ^ 48 by norm_num [Nat.pow_add]]
      rw [show old.toNat / 2 ^ 160 * 2 ^ 160 / (2 ^ 160 * 2 ^ 48) =
          old.toNat / 2 ^ 160 / 2 ^ 48 by
        rw [Nat.mul_comm (old.toNat / 2 ^ 160) (2 ^ 160)]
        rw [Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2 ^ 160)]]
      rw [Nat.div_div_eq_div_mul]
    rw [hmod, hdiv]
    norm_num
  rw [setUint48Offset26Word_toNat _ ⟨0⟩
    (by decide : (⟨0⟩ : UInt256).toNat < 2 ^ 48)]
  rw [htic]
  have hmod : old.toNat / 2 ^ 208 * 2 ^ 208 % 2 ^ 208 = 0 := by
    rw [Nat.mul_comm]
    exact Nat.mul_mod_right (2 ^ 208) (old.toNat / 2 ^ 208)
  rw [hmod]
  norm_num

theorem sstoreAccountMap_find?_owner_some_of_some
    (σ : AccountMap) (a : AccountAddress) (slot val : UInt256) {acc : Account}
    (hacc : σ.find? a = some acc) :
    ∃ acc', (sstoreAccountMap a σ slot val).find? a = some acc' := by
  unfold sstoreAccountMap
  rw [hacc]
  simp only [Option.option, accountMap_find_insert_self]
  exact ⟨if val == (default : UInt256) then { acc with storage := acc.storage.erase slot }
    else { acc with storage := acc.storage.insert slot val }, rfl⟩

theorem sstoreAccountMap_storage_findD_self_zero_present
    (σ : AccountMap) (a : AccountAddress) (slot val : UInt256) {acc : Account}
    (hacc : σ.find? a = some acc) :
    (((sstoreAccountMap a σ slot val).find? a).option (⟨0⟩ : UInt256)
        (fun acc => acc.storage.findD slot ⟨0⟩)) = val := by
  unfold sstoreAccountMap
  rw [hacc]
  simp only [Option.option, accountMap_find_insert_self]
  by_cases hzero : (val == (default : UInt256)) = true
  · have hval : val = (⟨0⟩ : UInt256) := by
      simpa using eq_of_beq hzero
    subst val
    simp [hzero, storage_findD_erase_self]
  · have hfalse : (val == (default : UInt256)) = false := by
      cases h : (val == (default : UInt256)) <;> simp [h] at hzero ⊢
    simp [hfalse]
    exact storage_findD_insert_self acc.storage slot val ⟨0⟩

theorem bidDeleteCollapsedAccountMap_equiv_source (owner : AccountAddress)
    (σ : AccountMap) (id : UInt256) :
    accountMapEquiv (bidDeleteCollapsedAccountMap owner σ id)
      (bidDeleteSourceAccountMap owner σ id) := by
  let base := bidBaseOfWord id
  let σ0 := sstoreAccountMap owner σ base ⟨0⟩
  let σ1 := sstoreAccountMap owner σ0 (base + ⟨1⟩) ⟨0⟩
  let slot2 := base + (⟨2⟩ : UInt256)
  let slot3 := base + (⟨3⟩ : UInt256)
  let slot4 := base + (⟨4⟩ : UInt256)
  let slot5 := base + (⟨5⟩ : UInt256)
  let σ2c := sstoreAccountMap owner σ1 slot2 ⟨0⟩
  let v1 := setAddressOffset0Word
    ((σ1.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot2 ⟨0⟩)) ⟨0⟩
  let σ2s := sstoreAccountMap owner σ1 slot2 v1
  let v2 := setUint48Offset20Word
    ((σ2s.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot2 ⟨0⟩)) ⟨0⟩
  let σ3s := sstoreAccountMap owner σ2s slot2 v2
  let v3 := setUint48Offset26Word
    ((σ3s.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot2 ⟨0⟩)) ⟨0⟩
  let σ4s := sstoreAccountMap owner σ3s slot2 v3
  by_cases howner : ∃ acc, σ.find? owner = some acc
  · obtain ⟨acc, hacc⟩ := howner
    obtain ⟨_, hσ0⟩ := sstoreAccountMap_find?_owner_some_of_some σ owner base ⟨0⟩ hacc
    obtain ⟨_, hσ1⟩ :=
      sstoreAccountMap_find?_owner_some_of_some σ0 owner (base + ⟨1⟩) ⟨0⟩ hσ0
    have hload2 :
        ((σ2s.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot2 ⟨0⟩)) =
          v1 := by
      exact sstoreAccountMap_storage_findD_self_zero_present σ1 owner slot2 v1 hσ1
    obtain ⟨_, hσ2s⟩ :=
      sstoreAccountMap_find?_owner_some_of_some σ1 owner slot2 v1 hσ1
    have hload3 :
        ((σ3s.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot2 ⟨0⟩)) =
          setUint48Offset20Word v1 ⟨0⟩ := by
      have h := sstoreAccountMap_storage_findD_self_zero_present σ2s owner slot2 v2 hσ2s
      simpa [σ3s, v2, hload2] using h
    have hv3 : v3 = ⟨0⟩ := by
      simpa [v3, hload3, v1] using
        (bid_slot2_delete_word (old := ((σ1.find? owner).option ⟨0⟩
          (fun acc => acc.storage.findD slot2 ⟨0⟩))))
    have hslot2a :
        accountMapEquiv σ2c (sstoreAccountMap owner σ2s slot2 ⟨0⟩) := by
      have h1 := accountMapEquiv_sstoreAccountMap_self_update σ1 owner slot2 v1 ⟨0⟩
      simpa [σ2c, σ2s] using h1
    have hslot2 : accountMapEquiv σ2c σ4s := by
      have h2 := accountMapEquiv_sstoreAccountMap_self_update σ2s owner slot2 v2 ⟨0⟩
      have htrans := accountMapEquiv.trans hslot2a h2
      simpa [σ4s, σ3s, hv3] using htrans
    let σ3c := sstoreAccountMap owner σ2c slot3
      (setAddressOffset0Word
        ((σ2c.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot3 ⟨0⟩)) ⟨0⟩)
    let σ5s := sstoreAccountMap owner σ4s slot3
      (setAddressOffset0Word
        ((σ4s.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot3 ⟨0⟩)) ⟨0⟩)
    have hval3 :
        setAddressOffset0Word
          ((σ4s.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot3 ⟨0⟩)) ⟨0⟩ =
        setAddressOffset0Word
          ((σ2c.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot3 ⟨0⟩)) ⟨0⟩ := by
      rw [accountMapEquiv_storage_findD hslot2 owner slot3 ⟨0⟩]
    have hslot3 : accountMapEquiv σ3c σ5s := by
      have h := accountMapEquiv_sstoreAccountMap owner slot3
        (setAddressOffset0Word
          ((σ2c.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot3 ⟨0⟩)) ⟨0⟩)
        hslot2
      simpa [σ3c, σ5s, hval3] using h
    let σ4c := sstoreAccountMap owner σ3c slot4
      (setAddressOffset0Word
        ((σ3c.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot4 ⟨0⟩)) ⟨0⟩)
    let σ6s := sstoreAccountMap owner σ5s slot4
      (setAddressOffset0Word
        ((σ5s.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot4 ⟨0⟩)) ⟨0⟩)
    have hval4 :
        setAddressOffset0Word
          ((σ5s.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot4 ⟨0⟩)) ⟨0⟩ =
        setAddressOffset0Word
          ((σ3c.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot4 ⟨0⟩)) ⟨0⟩ := by
      rw [accountMapEquiv_storage_findD hslot3 owner slot4 ⟨0⟩]
    have hslot4 : accountMapEquiv σ4c σ6s := by
      have h := accountMapEquiv_sstoreAccountMap owner slot4
        (setAddressOffset0Word
          ((σ3c.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot4 ⟨0⟩)) ⟨0⟩)
        hslot3
      simpa [σ4c, σ6s, hval4] using h
    have hslot5 := accountMapEquiv_sstoreAccountMap owner slot5 ⟨0⟩ hslot4
    simpa [bidDeleteCollapsedAccountMap, bidDeleteSourceAccountMap, base, σ0, σ1, slot2,
      slot3, slot4, slot5, σ2c, σ3c, σ4c, σ2s, σ3s, σ4s, σ5s, σ6s, v1, v2, v3, hv3]
      using hslot5
  · have hmissing : σ.find? owner = none := by
      cases h : σ.find? owner with
      | none => rfl
      | some acc => exact False.elim (howner ⟨acc, h⟩)
    simp [bidDeleteCollapsedAccountMap, bidDeleteSourceAccountMap, sstoreAccountMap_absent_same,
      hmissing, accountMapEquiv.refl]

theorem bidDeleteCollapsedAccountMap_accountMapEquiv {owner : AccountAddress}
    {σ τ : AccountMap} {id : UInt256} (hστ : accountMapEquiv σ τ) :
    accountMapEquiv (bidDeleteCollapsedAccountMap owner σ id)
      (bidDeleteCollapsedAccountMap owner τ id) := by
  let base := bidBaseOfWord id
  let slot2 := base + (⟨2⟩ : UInt256)
  let slot3 := base + (⟨3⟩ : UInt256)
  let slot4 := base + (⟨4⟩ : UInt256)
  let slot5 := base + (⟨5⟩ : UInt256)
  let σ0 := sstoreAccountMap owner σ base ⟨0⟩
  let τ0 := sstoreAccountMap owner τ base ⟨0⟩
  have h0 : accountMapEquiv σ0 τ0 := by
    simpa [σ0, τ0] using accountMapEquiv_sstoreAccountMap owner base ⟨0⟩ hστ
  let σ1 := sstoreAccountMap owner σ0 (base + ⟨1⟩) ⟨0⟩
  let τ1 := sstoreAccountMap owner τ0 (base + ⟨1⟩) ⟨0⟩
  have h1 : accountMapEquiv σ1 τ1 := by
    simpa [σ1, τ1] using accountMapEquiv_sstoreAccountMap owner (base + ⟨1⟩) ⟨0⟩ h0
  let σ2 := sstoreAccountMap owner σ1 slot2 ⟨0⟩
  let τ2 := sstoreAccountMap owner τ1 slot2 ⟨0⟩
  have h2 : accountMapEquiv σ2 τ2 := by
    simpa [σ2, τ2] using accountMapEquiv_sstoreAccountMap owner slot2 ⟨0⟩ h1
  let σ3 := sstoreAccountMap owner σ2 slot3
    (setAddressOffset0Word
      ((σ2.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot3 ⟨0⟩)) ⟨0⟩)
  let τ3 := sstoreAccountMap owner τ2 slot3
    (setAddressOffset0Word
      ((τ2.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot3 ⟨0⟩)) ⟨0⟩)
  have hslot3 :
      ((σ2.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot3 ⟨0⟩)) =
        ((τ2.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot3 ⟨0⟩)) :=
    accountMapEquiv_storage_findD h2 owner slot3 ⟨0⟩
  have h3 : accountMapEquiv σ3 τ3 := by
    have h :=
      accountMapEquiv_sstoreAccountMap owner slot3
        (setAddressOffset0Word
          ((σ2.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot3 ⟨0⟩)) ⟨0⟩)
        h2
    simpa [σ3, τ3, hslot3] using h
  let σ4 := sstoreAccountMap owner σ3 slot4
    (setAddressOffset0Word
      ((σ3.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot4 ⟨0⟩)) ⟨0⟩)
  let τ4 := sstoreAccountMap owner τ3 slot4
    (setAddressOffset0Word
      ((τ3.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot4 ⟨0⟩)) ⟨0⟩)
  have hslot4 :
      ((σ3.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot4 ⟨0⟩)) =
        ((τ3.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot4 ⟨0⟩)) :=
    accountMapEquiv_storage_findD h3 owner slot4 ⟨0⟩
  have h4 : accountMapEquiv σ4 τ4 := by
    have h :=
      accountMapEquiv_sstoreAccountMap owner slot4
        (setAddressOffset0Word
          ((σ3.find? owner).option ⟨0⟩ (fun acc => acc.storage.findD slot4 ⟨0⟩)) ⟨0⟩)
        h3
    simpa [σ4, τ4, hslot4] using h
  have h5 := accountMapEquiv_sstoreAccountMap owner slot5 ⟨0⟩ h4
  simpa [bidDeleteCollapsedAccountMap, base, slot2, slot3, slot4, slot5, σ0, τ0, σ1,
    τ1, σ2, τ2, σ3, τ3, σ4, τ4] using h5

theorem bidDeletedEVM_accountMap (evm : EVM.State) (id : UInt256) :
    (bidDeletedEVM evm id).accountMap =
      bidDeleteSourceAccountMap evm.executionEnv.codeOwner evm.accountMap id := by
  simp [bidDeletedEVM, bidDeleteSourceAccountMap, storageStore_accountMap,
    storageStore_executionEnv, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]

theorem bidDeleteCollapsedAccountMap_accountMapEquiv_bidDeletedEVM
    (evm : EVM.State) (id : UInt256) :
    accountMapEquiv
      (bidDeleteCollapsedAccountMap evm.executionEnv.codeOwner evm.accountMap id)
      (bidDeletedEVM evm id).accountMap := by
  rw [bidDeletedEVM_accountMap]
  exact bidDeleteCollapsedAccountMap_equiv_source evm.executionEnv.codeOwner evm.accountMap id

theorem clearStorage_bid_struct {evm : EVM.State} {id : UInt256} :
    clearStorage? config evm (bidEvaledBaseRefOfWord id) BidStructTy =
      .ok (bidDeletedEVM evm id) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [BidStructTy]
  change clearFields? config evm
      { base := "bids", steps := [.mindex (.int (Int.ofNat id.toNat))] }
      [("bid", uint256St), ("lot", uint256St), ("guy", addrSt), ("tic", uint48St),
        ("end", uint48St), ("usr", addrSt), ("gal", addrSt), ("tab", uint256St)] =
    .ok (bidDeletedEVM evm id)
  rw [Solm.clearFields?.eq_def]
  simp only [List.singleton_append]
  rw [clearStorage_bid_bid (evm := evm) (id := id)]
  simp only
  rw [Solm.clearFields?.eq_def]
  simp only [List.singleton_append]
  rw [clearStorage_bid_lot]
  simp only
  rw [Solm.clearFields?.eq_def]
  simp only [List.singleton_append]
  rw [clearStorage_bid_guy]
  simp only
  rw [Solm.clearFields?.eq_def]
  simp only [List.singleton_append]
  rw [clearStorage_bid_tic]
  simp only
  rw [Solm.clearFields?.eq_def]
  simp only [List.singleton_append]
  rw [clearStorage_bid_end]
  simp only
  rw [Solm.clearFields?.eq_def]
  simp only [List.singleton_append]
  rw [clearStorage_bid_usr]
  simp only
  rw [Solm.clearFields?.eq_def]
  simp only [List.singleton_append]
  rw [clearStorage_bid_gal]
  simp only
  rw [Solm.clearFields?.eq_def]
  simp only [List.singleton_append]
  rw [clearStorage_bid_tab]
  simp only
  rw [Solm.clearFields?.eq_def]

theorem deleteStorage_bidRef_of_get_id {evm : EVM.State} {locals : Store} {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    deleteStorage? config { contract := contract, locals := locals } evm (bidRef (.var "id")) =
      .ok (bidDeletedEVM evm id) := by
  rw [deleteStorage?]
  simp only [EvalResult.bind, bind]
  rw [resolveStorageRef_bidRef_of_get_id (evm := evm) (locals := locals) (id := id)
    hid hbids]
  exact clearStorage_bid_struct (evm := evm) (id := id)

end Benchmarks.Dss.Flipper
