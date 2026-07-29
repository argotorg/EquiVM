import Benchmarks.Dss.Flopper.AuctionCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper

/-! ## `tick(uint256)` -/

abbrev tickIdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev tickIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (tickIdWord I).toNat)

abbrev tickLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "id" (tickIdValue I)

abbrev tickEndEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (tickIdWord I)), .field "end"] }

abbrev tickTicEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (tickIdWord I)), .field "tic"] }

abbrev tickLotEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (tickIdWord I)), .field "lot"] }

abbrev tickPadEvaledRef : EvaledStorageRef :=
  { base := "pad", steps := [] }

abbrev tickTauEvaledRef : EvaledStorageRef :=
  { base := "tau", steps := [] }

abbrev tickEndWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) evm.accountMap
    evm.executionEnv

abbrev tickTicWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flopperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) evm.accountMap
    evm.executionEnv

abbrev tickLotWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flopperSlotWord (auctionLotSlot (tickIdWord I)) evm.accountMap evm.executionEnv

abbrev tickPadWord (evm : EVM.State) : UInt256 :=
  flopperSlotWord ⟨5⟩ evm.accountMap evm.executionEnv

abbrev tickTauWord (evm : EVM.State) : UInt256 :=
  flopperUint48Offset6Word ⟨6⟩ evm.accountMap evm.executionEnv

abbrev tickTimestampWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp

abbrev tickNow48Word (evm : EVM.State) : UInt256 :=
  UInt256.land (tickTimestampWord evm) flopperUint48Mask

abbrev tickOneWord : UInt256 :=
  ⟨1000000000000000000⟩

abbrev tickLotBaseWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  tickPadWord evm * tickLotWord evm I

abbrev tickLotPostWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.div (tickLotBaseWord evm I) tickOneWord

abbrev tickLotBaseLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (tickLocals I).insert "lotBase" (.int (Int.ofNat (tickLotBaseWord evm I).toNat))

def tickAfterLotStore (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (auctionLotSlot (tickIdWord I))
    (tickLotPostWord evm I)

abbrev tickEndPostWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((tickNow48Word evm).toNat + (tickTauWord (tickAfterLotStore evm I)).toNat)

abbrev tickEndLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (tickLotBaseLocals evm I).insert "end_" (.int (Int.ofNat (tickEndPostWord evm I).toNat))

abbrev tickEndWrappedNat (evm : EVM.State) (I : ExecutionEnv) : Nat :=
  ((tickNow48Word evm).toNat + (tickTauWord (tickAfterLotStore evm I)).toNat) % 2 ^ 48

abbrev tickEndWrappedLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (tickLotBaseLocals evm I).insert "end_" (.int (Int.ofNat (tickEndWrappedNat evm I)))

def tickEndStoredWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  setUint48Offset26Word
    (Solm.EVM.storageLoad (tickAfterLotStore evm I)
      (tickAfterLotStore evm I).executionEnv.codeOwner (auctionPackedSlot (tickIdWord I)))
    (tickEndPostWord evm I)

def tickPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (tickAfterLotStore evm I)
    (tickAfterLotStore evm I).executionEnv.codeOwner (auctionPackedSlot (tickIdWord I))
    (tickEndStoredWord evm I)

def tickRuntimePostAccountMap (owner : AccountAddress) (evm : EVM.State)
    (I : ExecutionEnv) : AccountMap :=
  let lotWord := tickLotPostWord evm I
  let endWord :=
    setUint48Offset26Word
      (solcSlotWord (sstoreAccountMap owner evm.accountMap (auctionLotSlot (tickIdWord I)) lotWord)
        evm.executionEnv (auctionPackedSlot (tickIdWord I)))
      (tickEndPostWord evm I)
  sstoreAccountMap owner
    (sstoreAccountMap owner evm.accountMap (auctionLotSlot (tickIdWord I)) lotWord)
    (auctionPackedSlot (tickIdWord I)) endWord

abbrev tickRuntimeLotBaseWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flopperSlotWord ⟨5⟩ σ I * flopperSlotWord (auctionLotSlot (tickIdWord I)) σ I

abbrev tickRuntimeLotPostWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.div (tickRuntimeLotBaseWord σ I) tickOneWord

def tickRuntimeAfterLotMap (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap owner σ (auctionLotSlot (tickIdWord I)) (tickRuntimeLotPostWord σ I)

abbrev tickRuntimeTauWord (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : UInt256 :=
  flopperUint48Offset6Word ⟨6⟩ (tickRuntimeAfterLotMap owner σ I) I

abbrev tickRuntimeAddWord (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp + tickRuntimeTauWord owner σ I

abbrev tickRuntimeEndClearMask : UInt256 :=
  UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩ - ⟨1⟩

abbrev tickRuntimeEndShiftedWord (data : UInt256) : UInt256 :=
  UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩ * UInt256.land flopperUint48Mask data

abbrev tickRuntimeEndStoredRawWord (old data : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old tickRuntimeEndClearMask) (tickRuntimeEndShiftedWord data)

def tickRuntimeSuccessAccountMap (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : AccountMap :=
  let σLot := tickRuntimeAfterLotMap owner σ I
  let old := solcSlotWord σLot I (auctionPackedSlot (tickIdWord I))
  sstoreAccountMap owner σLot (auctionPackedSlot (tickIdWord I))
    (tickRuntimeEndStoredRawWord old (tickRuntimeAddWord owner σ I))

theorem tickRuntimeEndStoredRawWord_eq_setUint48Offset26Word (old data : UInt256) :
    tickRuntimeEndStoredRawWord old data = setUint48Offset26Word old data := by
  apply u256_inj
  rw [tickRuntimeEndStoredRawWord, tickRuntimeEndShiftedWord, tickRuntimeEndClearMask]
  rw [setUint48Offset26Word_toNat]
  rw [u256_lor_toNat, u256_land_toNat, u256_mul_op_toNat]
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩).toNat = 2 ^ 208 by
    native_decide]
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩ - ⟨1⟩).toNat =
      2 ^ 208 - 1 by native_decide]
  rw [nat_land_mask_eq_mod]
  rw [show (UInt256.land flopperUint48Mask data).toNat =
      (UInt256.land data flopperUint48Mask).toNat by rw [u256_land_comm]]
  let data48 := (UInt256.land data flopperUint48Mask).toNat
  have hdata : (UInt256.land data flopperUint48Mask).toNat < 2 ^ 48 := by
    simpa [flopperUint48Mask, EVM.twoPow] using flopperUint48Masked_lt data
  have hdata' : data48 < 2 ^ 48 := by simpa [data48] using hdata
  have hlowLt : old.toNat % 2 ^ 208 < 2 ^ 208 := Nat.mod_lt _ (by norm_num)
  have hlowLtSize : old.toNat % 2 ^ 208 < UInt256.size :=
    lt_trans hlowLt (by norm_num [UInt256.size])
  have hmulLt : 2 ^ 208 * data48 < UInt256.size := by
    have h := Nat.mul_lt_mul_of_pos_left hdata' (by norm_num : 0 < 2 ^ 208)
    simpa [UInt256.size, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using h
  rw [Nat.mod_eq_of_lt hmulLt]
  rw [Nat.mod_eq_of_lt hlowLtSize]
  rw [Nat.mul_comm (2 ^ 208) data48]
  rw [nat_lor_shift_add (old.toNat % 2 ^ 208) data48 208 hlowLt]
  have hsumLt : old.toNat % 2 ^ 208 + data48 * 2 ^ 208 < UInt256.size := by
    have hlowLe : old.toNat % 2 ^ 208 ≤ 2 ^ 208 - 1 := Nat.le_pred_of_lt hlowLt
    have hdataLe : data48 ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hdata'
    have hdataTerm : data48 * 2 ^ 208 ≤ (2 ^ 48 - 1) * 2 ^ 208 :=
      Nat.mul_le_mul_right _ hdataLe
    have hmax : (2 ^ 208 - 1) + (2 ^ 48 - 1) * 2 ^ 208 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  exact Nat.mod_eq_of_lt hsumLt

theorem tickRuntimeLotPostWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    tickRuntimeLotPostWord σ I = tickRuntimeLotPostWord τ I := by
  have hpad := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨5⟩
  have hlot := flopperSlotWord_accountMapEquiv (I := I) hAccounts
    (auctionLotSlot (tickIdWord I))
  simp [tickRuntimeLotPostWord, tickRuntimeLotBaseWord, hpad, hlot]

theorem tickRuntimeAfterLotMap_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (owner : AccountAddress) (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv (tickRuntimeAfterLotMap owner σ I)
      (tickRuntimeAfterLotMap owner τ I) := by
  have hpost := tickRuntimeLotPostWord_accountMapEquiv (I := I) hAccounts
  unfold tickRuntimeAfterLotMap
  rw [hpost]
  exact accountMapEquiv_sstoreAccountMap owner (auctionLotSlot (tickIdWord I))
    (tickRuntimeLotPostWord τ I) hAccounts

theorem tickLocals_get_id (I : ExecutionEnv) :
    (tickLocals I).get? "id" = some (tickIdValue I) := by
  simp [tickLocals]

theorem tickLocals_get_bids (I : ExecutionEnv) :
    (tickLocals I).get? "bids" = none := by
  rw [tickLocals, store_get_ne _ _ (by decide)]
  simp [Std.HashMap.get?_eq_getElem?]

theorem tickLotBaseLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (tickLotBaseLocals evm I).get? "id" = some (tickIdValue I) := by
  rw [tickLotBaseLocals, store_get_ne _ _ (by decide)]
  exact tickLocals_get_id I

theorem tickLotBaseLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) :
    (tickLotBaseLocals evm I).get? "bids" = none := by
  rw [tickLotBaseLocals, store_get_ne _ _ (by decide)]
  exact tickLocals_get_bids I

theorem tickLotBaseLocals_get_lotBase (evm : EVM.State) (I : ExecutionEnv) :
    (tickLotBaseLocals evm I).get? "lotBase" =
      some (.int (Int.ofNat (tickLotBaseWord evm I).toNat)) := by
  rw [tickLotBaseLocals, store_get_self]

theorem tickEndLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (tickEndLocals evm I).get? "id" = some (tickIdValue I) := by
  rw [tickEndLocals, store_get_ne _ _ (by decide)]
  exact tickLotBaseLocals_get_id evm I

theorem tickEndLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) :
    (tickEndLocals evm I).get? "bids" = none := by
  rw [tickEndLocals, store_get_ne _ _ (by decide)]
  exact tickLotBaseLocals_get_bids evm I

theorem tickEndLocals_get_end (evm : EVM.State) (I : ExecutionEnv) :
    (tickEndLocals evm I).get? "end_" =
      some (.int (Int.ofNat (tickEndPostWord evm I).toNat)) := by
  rw [tickEndLocals, store_get_self]

theorem tickEndWrappedLocals_get_end (evm : EVM.State) (I : ExecutionEnv) :
    (tickEndWrappedLocals evm I).get? "end_" =
      some (.int (Int.ofNat (tickEndWrappedNat evm I))) := by
  rw [tickEndWrappedLocals, store_get_self]

theorem tickNow48Word_toNat (evm : EVM.State) :
    (tickNow48Word evm).toNat = (tickTimestampWord evm).toNat % 2 ^ 48 := by
  unfold tickNow48Word
  rw [u256_land_toNat]
  change Nat.land (tickTimestampWord evm).toNat (2 ^ 48 - 1) % UInt256.size =
    (tickTimestampWord evm).toNat % 2 ^ 48
  rw [nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt
    (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num [UInt256.size]))

theorem uint48Mask_add_no_wrap_toNat (a b : UInt256)
    (hfit : (UInt256.land a flopperUint48Mask).toNat + b.toNat < 2 ^ 48) :
    (UInt256.land (a + b) flopperUint48Mask).toNat =
      (UInt256.land a flopperUint48Mask).toNat + b.toNat := by
  rw [u256_land_toNat]
  change Nat.land (a + b).toNat (2 ^ 48 - 1) % UInt256.size = _
  rw [nat_land_mask_eq_mod]
  rw [uadd_toNat]
  have h48pos : 0 < 2 ^ 48 := by norm_num
  have h48ltSize : 2 ^ 48 < UInt256.size := by norm_num [UInt256.size]
  have hdvd : 2 ^ 48 ∣ UInt256.size := by
    change 2 ^ 48 ∣ 2 ^ 256
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [← Nat.mod_mod_eq_mod_mod_of_dvd hdvd]
  rw [Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ h48pos) h48ltSize)]
  have ha : (UInt256.land a flopperUint48Mask).toNat = a.toNat % 2 ^ 48 := by
    rw [u256_land_toNat]
    change Nat.land a.toNat (2 ^ 48 - 1) % UInt256.size = a.toNat % 2 ^ 48
    rw [nat_land_mask_eq_mod]
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ h48pos) h48ltSize)
  rw [ha] at hfit ⊢
  rw [Nat.add_mod]
  have hbmod : b.toNat % 2 ^ 48 = b.toNat := by
    have hb : b.toNat < 2 ^ 48 := by omega
    exact Nat.mod_eq_of_lt hb
  rw [hbmod]
  rw [Nat.mod_eq_of_lt hfit]
  exact Nat.mod_eq_of_lt (lt_trans hfit h48ltSize)

theorem uint48Mask_add_toNat_mod (a b : UInt256) (hb : b.toNat < 2 ^ 48) :
    (UInt256.land (a + b) flopperUint48Mask).toNat =
      ((UInt256.land a flopperUint48Mask).toNat + b.toNat) % 2 ^ 48 := by
  rw [u256_land_toNat]
  change Nat.land (a + b).toNat (2 ^ 48 - 1) % UInt256.size = _
  rw [nat_land_mask_eq_mod]
  rw [uadd_toNat]
  have h48pos : 0 < 2 ^ 48 := by norm_num
  have h48ltSize : 2 ^ 48 < UInt256.size := by norm_num [UInt256.size]
  have hdvd : 2 ^ 48 ∣ UInt256.size := by
    change 2 ^ 48 ∣ 2 ^ 256
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [← Nat.mod_mod_eq_mod_mod_of_dvd hdvd]
  rw [Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ h48pos) h48ltSize)]
  have ha : (UInt256.land a flopperUint48Mask).toNat = a.toNat % 2 ^ 48 := by
    rw [u256_land_toNat]
    change Nat.land a.toNat (2 ^ 48 - 1) % UInt256.size = a.toNat % 2 ^ 48
    rw [nat_land_mask_eq_mod]
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ h48pos) h48ltSize)
  rw [ha]
  rw [Nat.add_mod]
  rw [Nat.mod_eq_of_lt hb]
  exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ h48pos) h48ltSize)

theorem uint48AddGuard_false_of_no_wrap (a b : UInt256)
    (hfit : (UInt256.land a flopperUint48Mask).toNat + b.toNat < 2 ^ 48) :
    UInt256.lt (UInt256.land (a + b) flopperUint48Mask)
        (UInt256.land a flopperUint48Mask) = ⟨0⟩ := by
  have hsum := uint48Mask_add_no_wrap_toNat a b hfit
  apply ult_zero
  rw [hsum]
  exact Nat.le_add_right _ _

theorem uint48AddGuard_true_of_wrap (a b : UInt256)
    (hb : b.toNat < 2 ^ 48)
    (hover : 2 ^ 48 ≤ (UInt256.land a flopperUint48Mask).toNat + b.toNat) :
    UInt256.lt (UInt256.land (a + b) flopperUint48Mask)
        (UInt256.land a flopperUint48Mask) = ⟨1⟩ := by
  apply ult_one
  rw [uint48Mask_add_toNat_mod a b hb]
  have hx : (UInt256.land a flopperUint48Mask).toNat < 2 ^ 48 := by
    simpa [EVM.twoPow] using flopperUint48Masked_lt a
  have hsumLt : (UInt256.land a flopperUint48Mask).toNat + b.toNat < 2 ^ 49 := by
    omega
  rw [Nat.mod_eq_sub_mod hover]
  have hsubLt : (UInt256.land a flopperUint48Mask).toNat + b.toNat - 2 ^ 48 < 2 ^ 48 := by
    omega
  rw [Nat.mod_eq_of_lt hsubLt]
  omega

theorem tickEndPostWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (tickNow48Word evm).toNat + (tickTauWord (tickAfterLotStore evm I)).toNat <
        2 ^ 48) :
    (tickEndPostWord evm I).toNat =
      (tickNow48Word evm).toNat + (tickTauWord (tickAfterLotStore evm I)).toNat := by
  unfold tickEndPostWord
  exact UInt256.toNat_ofNat_of_lt (lt_trans hfit (by norm_num [UInt256.size]))

theorem evalExpr_tick_end_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickLocals I } evm
        (.storage (bidsF (.var "id") "end")) =
      .ok (.int (Int.ofNat (tickEndWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := tickLocals I }
  have hload :
      storageLocLoad evm
          (uint48Loc (auctionPackedSlot (tickIdWord I)) ⟨26, by decide⟩ (by decide)) =
        .int (Int.ofNat (tickEndWord evm I).toNat) := by
    rw [flopperStorageLocLoad_uint48_offset26]
    rw [u256_land_comm
      (UInt256.div
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (auctionPackedSlot (tickIdWord I)))
        (UInt256.ofNat (256 ^ 26)))
      flopperUint48Mask]
    rfl
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "end") (er := tickEndEvaledRef I)
    (t := .int uint48Int)
    (loc := uint48Loc (auctionPackedSlot (tickIdWord I)) ⟨26, by decide⟩ (by decide))
    (value := .int (Int.ofNat (tickEndWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simp [frame, tickEndEvaledRef, auctionIdKey, tickLocals, tickIdValue,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?,
        valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint48St])
    (by rfl)
    hload

theorem evalExpr_tick_tic_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickLocals I } evm
        (.storage (bidsF (.var "id") "tic")) =
      .ok (.int (Int.ofNat (tickTicWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := tickLocals I }
  have hload :
      storageLocLoad evm
          (uint48Loc (auctionPackedSlot (tickIdWord I)) ⟨20, by decide⟩ (by decide)) =
        .int (Int.ofNat (tickTicWord evm I).toNat) := by
    rw [flopperStorageLocLoad_uint48_offset20]
    rw [u256_land_comm
      (UInt256.div
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (auctionPackedSlot (tickIdWord I)))
        (UInt256.ofNat (256 ^ 20)))
      flopperUint48Mask]
    rfl
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "tic") (er := tickTicEvaledRef I)
    (t := .int uint48Int)
    (loc := uint48Loc (auctionPackedSlot (tickIdWord I)) ⟨20, by decide⟩ (by decide))
    (value := .int (Int.ofNat (tickTicWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simp [frame, tickTicEvaledRef, auctionIdKey, tickLocals, tickIdValue,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?,
        valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint48St])
    (by rfl)
    hload

theorem evalExpr_tick_lot_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickLocals I } evm
        (.storage (bidsF (.var "id") "lot")) =
      .ok (.int (Int.ofNat (tickLotWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := tickLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "lot") (er := tickLotEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (auctionLotSlot (tickIdWord I)))
    (value := .int (Int.ofNat (tickLotWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simp [frame, tickLotEvaledRef, auctionIdKey, tickLocals, tickIdValue,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?,
        valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
    (by rfl)
    (by simpa [tickLotWord, flopperSlotWord] using
      flopperStorageLocLoad_uint256 evm (auctionLotSlot (tickIdWord I)))

theorem evalExpr_tick_pad_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickLocals I } evm (.storage padRef) =
      .ok (.int (Int.ofNat (tickPadWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := tickLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := padRef) (er := tickPadEvaledRef)
    (t := .int uint256Int) (loc := wordLoc ⟨5⟩)
    (value := .int (Int.ofNat (tickPadWord evm).toNat))
    (by simp [frame, padRef])
    (by simp [frame, tickPadEvaledRef, evalStorageRef, evalStorageRefSteps,
      padRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [tickPadWord, flopperSlotWord] using flopperStorageLocLoad_uint256 evm ⟨5⟩)

theorem evalExpr_tick_tau_storage (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickLotBaseLocals evm0 I } evm
        (.storage tauRef) =
      .ok (.int (Int.ofNat (tickTauWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := tickLotBaseLocals evm0 I }
  have hload :
      storageLocLoad evm (uint48Loc ⟨6⟩ ⟨6, by decide⟩ (by decide)) =
        .int (Int.ofNat (tickTauWord evm).toNat) := by
    rw [flopperStorageLocLoad_uint48_offset6]
    rw [u256_land_comm
      (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩)
        (UInt256.ofNat (256 ^ 6))) flopperUint48Mask]
    rfl
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := tauRef) (er := tickTauEvaledRef)
    (t := .int uint48Int) (loc := uint48Loc ⟨6⟩ ⟨6, by decide⟩ (by decide))
    (value := .int (Int.ofNat (tickTauWord evm).toNat))
    (by simp [frame, tauRef, tickLotBaseLocals, tickLocals])
    (by simp [frame, tickTauEvaledRef, evalStorageRef, evalStorageRefSteps,
      tauRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint48St])
    (by rfl)
    hload

theorem evalExpr_tick_end_lt_timestamp_true (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (tickEndWord evm I).toNat < (tickTimestampWord evm).toNat) :
    evalExpr? config { contract := contract, locals := tickLocals I } evm
      (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool true) := by
  have hendEval := evalExpr_tick_end_storage evm I
  simp only [evalExpr?, hendEval, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  simpa [tickTimestampWord] using hlt

theorem evalExpr_tick_end_lt_timestamp_false (evm : EVM.State) (I : ExecutionEnv)
    (hle : (tickTimestampWord evm).toNat ≤ (tickEndWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := tickLocals I } evm
      (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool false) := by
  have hendEval := evalExpr_tick_end_storage evm I
  have hnlt : ¬ (Int.ofNat (tickEndWord evm I).toNat <
      Int.ofNat (tickTimestampWord evm).toNat) := by
    intro hlt
    exact (Nat.not_lt.mpr hle) (Int.ofNat_lt.mp hlt)
  have hdec :
      decide (Int.ofNat (tickEndWord evm I).toNat <
        Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) = false := by
    rw [decide_eq_false_iff_not]
    simpa [tickTimestampWord] using hnlt
  simp only [evalExpr?, hendEval, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hdec]

theorem evalExpr_tick_tic_eq_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (htic : tickTicWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tickLocals I } evm
      (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) = .ok (.bool true) := by
  have hticEval := evalExpr_tick_tic_storage evm I
  simp only [evalExpr?, hticEval, EvalResult.bind, bind, pure]
  rw [htic]
  simp [evalBinaryOp?]

theorem evalExpr_tick_tic_eq_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (htic : tickTicWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tickLocals I } evm
      (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) = .ok (.bool false) := by
  have hticEval := evalExpr_tick_tic_storage evm I
  have hne :
      Value.int (Int.ofNat (tickTicWord evm I).toNat) ≠ Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    exact htic (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hbeq :
      (Value.int (Int.ofNat (tickTicWord evm I).toNat) == Value.int 0) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hticEval, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_tick_lot_storage_lotBaseLocals (evm0 evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickLotBaseLocals evm0 I } evm
        (.storage (bidsF (.var "id") "lot")) =
      .ok (.int (Int.ofNat (tickLotWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := tickLotBaseLocals evm0 I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "lot") (er := tickLotEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (auctionLotSlot (tickIdWord I)))
    (value := .int (Int.ofNat (tickLotWord evm I).toNat))
    (by simp [frame, bidsF, tickLotBaseLocals, tickLocals])
    (by
      simpa [frame, tickLotEvaledRef, tickIdValue] using
        evalStorageRef_auction_field evm (tickLotBaseLocals evm0 I) (tickIdWord I) "lot"
          (by simpa [tickIdValue] using tickLotBaseLocals_get_id evm0 I))
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
    (by rfl)
    (by simpa [tickLotWord, flopperSlotWord] using
      flopperStorageLocLoad_uint256 evm (auctionLotSlot (tickIdWord I)))

theorem evalExpr_tick_pad_storage_lotBaseLocals (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickLotBaseLocals evm0 I } evm
        (.storage padRef) =
      .ok (.int (Int.ofNat (tickPadWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := tickLotBaseLocals evm0 I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := padRef) (er := tickPadEvaledRef)
    (t := .int uint256Int) (loc := wordLoc ⟨5⟩)
    (value := .int (Int.ofNat (tickPadWord evm).toNat))
    (by simp [frame, padRef, tickLotBaseLocals, tickLocals])
    (by simp [frame, tickPadEvaledRef, evalStorageRef, evalStorageRefSteps,
      padRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [tickPadWord, flopperSlotWord] using flopperStorageLocLoad_uint256 evm ⟨5⟩)

theorem evalExpr_tick_lotBase_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickLotBaseLocals evm I } evm
        (.var "lotBase") =
      .ok (.int (Int.ofNat (tickLotBaseWord evm I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((tickLotBaseLocals evm I).get? "lotBase") =
    .ok (.int (Int.ofNat (tickLotBaseWord evm I).toNat))
  rw [tickLotBaseLocals_get_lotBase]
  rfl

theorem tickLotBaseWord_toNat_of_fit (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (tickPadWord evm).toNat * (tickLotWord evm I).toNat < UInt256.size) :
    (tickLotBaseWord evm I).toNat =
      (tickPadWord evm).toNat * (tickLotWord evm I).toNat := by
  rw [tickLotBaseWord, u256_mul_op_toNat, Nat.mod_eq_of_lt hfit]

theorem evalExpr_tick_lotBase_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (tickPadWord evm).toNat * (tickLotWord evm I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := tickLocals I } evm
        (mul256 (.storage padRef) (.storage (bidsF (.var "id") "lot"))) =
      .ok (.int (Int.ofNat (tickLotBaseWord evm I).toNat)) := by
  have hpad := evalExpr_tick_pad_storage evm I
  have hlot := evalExpr_tick_lot_storage evm I
  have hprod := tickLotBaseWord_toNat_of_fit evm I hfit
  unfold mul256 u256
  simp only [evalExpr?, hpad, hlot, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hfitNat :
      (tickPadWord evm).toNat * (tickLotWord evm I).toNat < 2 ^ 256 := by
    simpa [UInt256.size] using hfit
  have hltInt :
      Int.ofNat ((tickPadWord evm).toNat * (tickLotWord evm I).toNat) <
        (2 : Int) ^ (256 : Nat) := by
    change Int.ofNat ((tickPadWord evm).toNat * (tickLotWord evm I).toNat) <
      Int.ofNat (2 ^ 256)
    exact Int.ofNat_lt.mpr hfitNat
  simp [uint256Int, hprod]
  constructor
  · exact Int.natCast_nonneg _
  · exact hltInt

theorem evalExpr_tick_lotBase_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hoverflow : UInt256.size ≤ (tickPadWord evm).toNat * (tickLotWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := tickLocals I } evm
        (mul256 (.storage padRef) (.storage (bidsF (.var "id") "lot"))) =
      .revert := by
  have hpad := evalExpr_tick_pad_storage evm I
  have hlot := evalExpr_tick_lot_storage evm I
  unfold mul256 u256
  simp only [evalExpr?, hpad, hlot, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hoverflowNat :
      2 ^ 256 ≤ (tickPadWord evm).toNat * (tickLotWord evm I).toNat := by
    simpa [UInt256.size] using hoverflow
  have hgeInt :
      (2 : Int) ^ (256 : Nat) ≤
        Int.ofNat ((tickPadWord evm).toNat * (tickLotWord evm I).toNat) := by
    change Int.ofNat (2 ^ 256) ≤
      Int.ofNat ((tickPadWord evm).toNat * (tickLotWord evm I).toNat)
    exact Int.ofNat_le.mpr hoverflowNat
  simp [uint256Int]
  intro _hnonneg
  exact hgeInt

theorem evalExpr_tick_lot_eq_zero_true_lotBaseLocals (evm : EVM.State) (I : ExecutionEnv)
    (hlot : tickLotWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tickLotBaseLocals evm I } evm
      (.binary .eq (.storage (bidsF (.var "id") "lot")) (.intLit 0)) = .ok (.bool true) := by
  have hlotEval := evalExpr_tick_lot_storage_lotBaseLocals evm evm I
  simp only [evalExpr?, hlotEval, EvalResult.bind, bind, pure]
  rw [hlot]
  simp [evalBinaryOp?]

theorem evalExpr_tick_lot_eq_zero_false_lotBaseLocals (evm : EVM.State) (I : ExecutionEnv)
    (hlot : tickLotWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tickLotBaseLocals evm I } evm
      (.binary .eq (.storage (bidsF (.var "id") "lot")) (.intLit 0)) = .ok (.bool false) := by
  have hlotEval := evalExpr_tick_lot_storage_lotBaseLocals evm evm I
  have hne :
      Value.int (Int.ofNat (tickLotWord evm I).toNat) ≠ Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    exact hlot (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hbeq :
      (Value.int (Int.ofNat (tickLotWord evm I).toNat) == Value.int 0) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hlotEval, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_tick_lotBase_div_lot_eq_pad (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (tickPadWord evm).toNat * (tickLotWord evm I).toNat < UInt256.size)
    (hlot : tickLotWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tickLotBaseLocals evm I } evm
      (.binary .eq
        (.binary .div (.var "lotBase") (.storage (bidsF (.var "id") "lot")))
        (.storage padRef)) = .ok (.bool true) := by
  have hbase := evalExpr_tick_lotBase_var evm I
  have hlotEval := evalExpr_tick_lot_storage_lotBaseLocals evm evm I
  have hpadEval := evalExpr_tick_pad_storage_lotBaseLocals evm evm I
  have hbaseNat := tickLotBaseWord_toNat_of_fit evm I hfit
  have hlotPos : 0 < (tickLotWord evm I).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hlot (uint256_toNat_eq_zero hzero))
  have hdivNat :
      (tickLotBaseWord evm I).toNat / (tickLotWord evm I).toNat =
        (tickPadWord evm).toNat := by
    rw [hbaseNat]
    rw [Nat.mul_comm]
    exact Nat.mul_div_right _ hlotPos
  have hdivInt :
      Int.ofNat (tickLotBaseWord evm I).toNat / Int.ofNat (tickLotWord evm I).toNat =
        Int.ofNat (tickPadWord evm).toNat := by
    simpa [Int.natCast_ediv] using
      (congrArg (fun n : Nat => (n : Int)) hdivNat)
  simp only [evalExpr?, hbase, hlotEval, hpadEval, EvalResult.bind, bind]
  simp [evalBinaryOp?, hlotPos.ne']
  exact hdivInt

theorem evalExpr_tick_mul_guard_true (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (tickPadWord evm).toNat * (tickLotWord evm I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := tickLotBaseLocals evm I } evm
      (.binary .or
        (.binary .eq (.storage (bidsF (.var "id") "lot")) (.intLit 0))
        (.binary .eq
          (.binary .div (.var "lotBase") (.storage (bidsF (.var "id") "lot")))
          (.storage padRef))) = .ok (.bool true) := by
  by_cases hlotZero : tickLotWord evm I = ⟨0⟩
  · simp only [evalExpr?, evalExpr_tick_lot_eq_zero_true_lotBaseLocals evm I hlotZero,
      EvalResult.bind, bind, pure]
  · simp only [evalExpr?, evalExpr_tick_lot_eq_zero_false_lotBaseLocals evm I hlotZero,
      evalExpr_tick_lotBase_div_lot_eq_pad evm I hfit hlotZero, EvalResult.bind, bind, pure]

theorem evalExpr_tick_lotPost (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickLotBaseLocals evm I } evm
      (.binary .div (.var "lotBase") (.intLit ONE)) =
        .ok (.int (Int.ofNat (tickLotPostWord evm I).toNat)) := by
  have hbase := evalExpr_tick_lotBase_var evm I
  have hone : (tickOneWord).toNat = 1000000000000000000 := by native_decide
  have hdivNat :
      (tickLotPostWord evm I).toNat =
        (tickLotBaseWord evm I).toNat / 1000000000000000000 := by
    rw [tickLotPostWord, udiv_toNat, hone]
  have hdivInt :
      Int.ofNat (tickLotBaseWord evm I).toNat / ONE =
        Int.ofNat (tickLotPostWord evm I).toNat := by
    have hcast := congrArg (fun n : Nat => (n : Int)) hdivNat
    simpa [ONE, Int.natCast_ediv] using hcast.symm
  simp only [evalExpr?, hbase, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.div
      (Value.int (Int.ofNat (tickLotBaseWord evm I).toNat))
      (Value.int ONE) =
    .ok (.int (Int.ofNat (tickLotPostWord evm I).toNat))
  simp [evalBinaryOp?, ONE]
  exact hdivInt

theorem assign_tickLotStorage (evm0 evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := tickLotBaseLocals evm0 I } evm
      .storage (bidsF (.var "id") "lot")
        (.int (Int.ofNat (tickLotPostWord evm0 I).toNat)) =
      .ok ({ contract := contract, locals := tickLotBaseLocals evm0 I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (auctionLotSlot (tickIdWord I))
          (tickLotPostWord evm0 I)) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := tickLotEvaledRef I)
      (loc := wordLoc (auctionLotSlot (tickIdWord I)))
      (hbase := tickLotBaseLocals_get_bids evm0 I)
      (her := by
        simpa [tickLotEvaledRef, tickIdValue] using
          evalStorageRef_auction_field evm (tickLotBaseLocals evm0 I) (tickIdWord I) "lot"
            (by simpa [tickIdValue] using tickLotBaseLocals_get_id evm0 I))
      (hty := by
        simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          BidStructTy, uint256St])
      (hloc := by
        funext evm'
        exact auctionLotLayout evm' (tickIdWord I))
  simpa [wordLoc, uint256Loc] using
    storageLocStore_uint256 evm (auctionLotSlot (tickIdWord I)) (tickLotPostWord evm0 I)

theorem tickAfterLotStore_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (tickAfterLotStore evm I).executionEnv = evm.executionEnv := by
  simp [tickAfterLotStore, storageStore_executionEnv]

theorem evalExpr_tick_now48_lotBaseLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickLotBaseLocals evm I }
        (tickAfterLotStore evm I) now48 =
      .ok (.int (Int.ofNat (tickNow48Word evm).toNat)) := by
  unfold now48 wrap48
  simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hmod :
      Int.ofNat (UInt256.ofNat (tickAfterLotStore evm I).executionEnv.header.timestamp).toNat %
          uint48Modulus =
        Int.ofNat (tickNow48Word evm).toNat := by
    have hnow := tickNow48Word_toNat evm
    have henv :
        (UInt256.ofNat (tickAfterLotStore evm I).executionEnv.header.timestamp).toNat =
          (tickTimestampWord evm).toNat := by
      simp [tickTimestampWord, tickAfterLotStore_executionEnv]
    rw [henv, hnow]
    norm_num [uint48Modulus, Int.natCast_mod]
  simpa [uint48Modulus] using hmod

theorem evalExpr_tick_endAdd_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (tickNow48Word evm).toNat + (tickTauWord (tickAfterLotStore evm I)).toNat <
        2 ^ 48) :
    evalExpr? config { contract := contract, locals := tickLotBaseLocals evm I }
        (tickAfterLotStore evm I)
        (wrap48 (.binary .add now48 (.storage tauRef))) =
      .ok (.int (Int.ofNat (tickEndPostWord evm I).toNat)) := by
  have hnow := evalExpr_tick_now48_lotBaseLocals evm I
  have htau := evalExpr_tick_tau_storage evm (tickAfterLotStore evm I) I
  have hendNat := tickEndPostWord_toNat evm I hfit
  unfold wrap48
  simp only [evalExpr?, hnow, htau, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hsumMod :
      (Int.ofNat (tickNow48Word evm).toNat +
          Int.ofNat (tickTauWord (tickAfterLotStore evm I)).toNat) %
          uint48Modulus =
        Int.ofNat (tickEndPostWord evm I).toNat := by
    rw [hendNat]
    have hsumCast :
        Int.ofNat ((tickNow48Word evm).toNat +
            (tickTauWord (tickAfterLotStore evm I)).toNat) =
          Int.ofNat (tickNow48Word evm).toNat +
            Int.ofNat (tickTauWord (tickAfterLotStore evm I)).toNat := by
      norm_num
    rw [← hsumCast]
    have hfitInt :
        Int.ofNat ((tickNow48Word evm).toNat +
            (tickTauWord (tickAfterLotStore evm I)).toNat) < uint48Modulus := by
      change Int.ofNat ((tickNow48Word evm).toNat +
          (tickTauWord (tickAfterLotStore evm I)).toNat) < Int.ofNat (2 ^ 48)
      exact Int.ofNat_lt.mpr hfit
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) hfitInt
  simpa [uint48Modulus] using hsumMod

theorem evalExpr_tick_endAdd_wrapped (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickLotBaseLocals evm I }
        (tickAfterLotStore evm I)
        (wrap48 (.binary .add now48 (.storage tauRef))) =
      .ok (.int (Int.ofNat (tickEndWrappedNat evm I))) := by
  have hnow := evalExpr_tick_now48_lotBaseLocals evm I
  have htau := evalExpr_tick_tau_storage evm (tickAfterLotStore evm I) I
  unfold wrap48
  simp only [evalExpr?, hnow, htau, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hsumMod :
      (Int.ofNat (tickNow48Word evm).toNat +
          Int.ofNat (tickTauWord (tickAfterLotStore evm I)).toNat) %
          uint48Modulus =
        Int.ofNat (tickEndWrappedNat evm I) := by
    have hsumCast :
        Int.ofNat ((tickNow48Word evm).toNat +
            (tickTauWord (tickAfterLotStore evm I)).toNat) =
          Int.ofNat (tickNow48Word evm).toNat +
            Int.ofNat (tickTauWord (tickAfterLotStore evm I)).toNat := by
      norm_num
    rw [← hsumCast]
    norm_num [tickEndWrappedNat, uint48Modulus, Int.natCast_mod]
  simpa [uint48Modulus] using hsumMod

theorem evalExpr_tick_end_guard_true (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (tickNow48Word evm).toNat + (tickTauWord (tickAfterLotStore evm I)).toNat <
        2 ^ 48) :
    evalExpr? config { contract := contract, locals := tickEndLocals evm I }
        (tickAfterLotStore evm I)
      (.binary .ge (.var "end_") now48) = .ok (.bool true) := by
  have hend :
      evalExpr? config { contract := contract, locals := tickEndLocals evm I }
          (tickAfterLotStore evm I) (.var "end_") =
        .ok (.int (Int.ofNat (tickEndPostWord evm I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((tickEndLocals evm I).get? "end_") =
      .ok (.int (Int.ofNat (tickEndPostWord evm I).toNat))
    rw [tickEndLocals_get_end]
    rfl
  have hnow :
      evalExpr? config { contract := contract, locals := tickEndLocals evm I }
          (tickAfterLotStore evm I) now48 =
        .ok (.int (Int.ofNat (tickNow48Word evm).toNat)) := by
    unfold now48 wrap48
    simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
    have hmod :
        Int.ofNat (UInt256.ofNat (tickAfterLotStore evm I).executionEnv.header.timestamp).toNat %
            uint48Modulus =
          Int.ofNat (tickNow48Word evm).toNat := by
      have hnowNat := tickNow48Word_toNat evm
      have henv :
          (UInt256.ofNat (tickAfterLotStore evm I).executionEnv.header.timestamp).toNat =
            (tickTimestampWord evm).toNat := by
        simp [tickTimestampWord, tickAfterLotStore_executionEnv]
      rw [henv, hnowNat]
      norm_num [uint48Modulus, Int.natCast_mod]
    simpa [uint48Modulus] using hmod
  have hendNat := tickEndPostWord_toNat evm I hfit
  have hge :
      Int.ofNat (tickNow48Word evm).toNat ≤
        Int.ofNat (tickEndPostWord evm I).toNat := by
    rw [hendNat]
    change Int.ofNat (tickNow48Word evm).toNat ≤
      Int.ofNat ((tickNow48Word evm).toNat +
        (tickTauWord (tickAfterLotStore evm I)).toNat)
    exact Int.ofNat_le.mpr (Nat.le_add_right _ _)
  simp only [evalExpr?, hend, hnow, EvalResult.bind, bind, evalBinaryOp?]
  simpa using hge

theorem evalExpr_tick_end_guard_false_wrapped (evm : EVM.State) (I : ExecutionEnv)
    (hoverflow :
      2 ^ 48 ≤
        (tickNow48Word evm).toNat + (tickTauWord (tickAfterLotStore evm I)).toNat) :
    evalExpr? config { contract := contract, locals := tickEndWrappedLocals evm I }
        (tickAfterLotStore evm I)
      (.binary .ge (.var "end_") now48) = .ok (.bool false) := by
  have hend :
      evalExpr? config { contract := contract, locals := tickEndWrappedLocals evm I }
          (tickAfterLotStore evm I) (.var "end_") =
        .ok (.int (Int.ofNat (tickEndWrappedNat evm I))) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((tickEndWrappedLocals evm I).get? "end_") =
      .ok (.int (Int.ofNat (tickEndWrappedNat evm I)))
    rw [tickEndWrappedLocals_get_end]
    rfl
  have hnow :
      evalExpr? config { contract := contract, locals := tickEndWrappedLocals evm I }
          (tickAfterLotStore evm I) now48 =
        .ok (.int (Int.ofNat (tickNow48Word evm).toNat)) := by
    unfold now48 wrap48
    simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
    have hmod :
        Int.ofNat (UInt256.ofNat (tickAfterLotStore evm I).executionEnv.header.timestamp).toNat %
            uint48Modulus =
          Int.ofNat (tickNow48Word evm).toNat := by
      have hnowNat := tickNow48Word_toNat evm
      have henv :
          (UInt256.ofNat (tickAfterLotStore evm I).executionEnv.header.timestamp).toNat =
            (tickTimestampWord evm).toNat := by
        simp [tickTimestampWord, tickAfterLotStore_executionEnv]
      rw [henv, hnowNat]
      norm_num [uint48Modulus, Int.natCast_mod]
    simpa [uint48Modulus] using hmod
  have hnowLt : (tickNow48Word evm).toNat < 2 ^ 48 := by
    have h := tickNow48Word_toNat evm
    rw [h]
    exact Nat.mod_lt _ (by norm_num)
  have htauLt : (tickTauWord (tickAfterLotStore evm I)).toNat < 2 ^ 48 := by
    simpa [tickTauWord, flopperUint48Offset6Word, EVM.twoPow, u256_land_comm] using
      flopperUint48Masked_lt
        (UInt256.div
          (flopperSlotWord ⟨6⟩ (tickAfterLotStore evm I).accountMap
            (tickAfterLotStore evm I).executionEnv)
          (UInt256.ofNat (256 ^ 6)))
  have hwrappedLt :
      tickEndWrappedNat evm I < (tickNow48Word evm).toNat := by
    unfold tickEndWrappedNat
    have hsumLt :
        (tickNow48Word evm).toNat + (tickTauWord (tickAfterLotStore evm I)).toNat <
          2 ^ 49 := by
      omega
    rw [Nat.mod_eq_sub_mod hoverflow]
    have hsubLt :
        (tickNow48Word evm).toNat + (tickTauWord (tickAfterLotStore evm I)).toNat -
            2 ^ 48 < 2 ^ 48 := by
      omega
    rw [Nat.mod_eq_of_lt hsubLt]
    omega
  have hdec :
      decide
          (Int.ofNat (tickNow48Word evm).toNat ≤
            Int.ofNat (tickEndWrappedNat evm I)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    exact (Nat.not_le_of_gt hwrappedLt) (Int.ofNat_le.mp hle)
  simp only [evalExpr?, hend, hnow, EvalResult.bind, bind, evalBinaryOp?]
  rw [hdec]

theorem assign_tickEndStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := tickEndLocals evm I }
        (tickAfterLotStore evm I)
      .storage (bidsF (.var "id") "end")
        (.int (Int.ofNat (tickEndPostWord evm I).toNat % uint48Modulus)) =
      .ok ({ contract := contract, locals := tickEndLocals evm I }, tickPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint48St)
      (er := tickEndEvaledRef I)
      (loc := uint48Loc (auctionPackedSlot (tickIdWord I)) ⟨26, by decide⟩ (by decide))
      (hbase := tickEndLocals_get_bids evm I)
      (her := by
        simpa [tickEndEvaledRef, tickIdValue] using
          evalStorageRef_auction_field (tickAfterLotStore evm I) (tickEndLocals evm I)
            (tickIdWord I) "end"
            (by simpa [tickIdValue] using tickEndLocals_get_id evm I))
      (hty := by
        simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          BidStructTy, uint48St])
      (hloc := by
        funext evm'
        exact auctionEndLayout evm' (tickIdWord I))
  simpa [tickPostState, tickEndStoredWord, uint48Loc] using
    storageLocStore_uint48_offset26_word (tickAfterLotStore evm I)
      (auctionPackedSlot (tickIdWord I)) (tickEndPostWord evm I)

theorem tickEndPostWord_mod (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (tickNow48Word evm).toNat + (tickTauWord (tickAfterLotStore evm I)).toNat <
        2 ^ 48) :
    Int.ofNat (tickEndPostWord evm I).toNat % uint48Modulus =
      Int.ofNat (tickEndPostWord evm I).toNat := by
  have hendNat := tickEndPostWord_toNat evm I hfit
  have hendLt : (tickEndPostWord evm I).toNat < 2 ^ 48 := by
    rw [hendNat]
    exact hfit
  have hendLtInt :
      Int.ofNat (tickEndPostWord evm I).toNat < uint48Modulus := by
    change Int.ofNat (tickEndPostWord evm I).toNat < Int.ofNat (2 ^ 48)
    exact Int.ofNat_lt.mpr hendLt
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) hendLtInt

theorem assign_tickEndStorage_value (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (tickNow48Word evm).toNat + (tickTauWord (tickAfterLotStore evm I)).toNat <
        2 ^ 48) :
    assignStorageRef? config { contract := contract, locals := tickEndLocals evm I }
        (tickAfterLotStore evm I)
      .storage (bidsF (.var "id") "end")
        (.int (Int.ofNat (tickEndPostWord evm I).toNat)) =
      .ok ({ contract := contract, locals := tickEndLocals evm I }, tickPostState evm I) := by
  rw [← tickEndPostWord_mod evm I hfit]
  exact assign_tickEndStorage evm I

theorem evalExpr_tick_end_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickEndLocals evm I }
        (tickAfterLotStore evm I) (.var "end_") =
      .ok (.int (Int.ofNat (tickEndPostWord evm I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((tickEndLocals evm I).get? "end_") =
    .ok (.int (Int.ofNat (tickEndPostWord evm I).toNat))
  rw [tickEndLocals_get_end]
  rfl

theorem flopperTickBodyReverts_endNotExpired (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hendGe : (tickTimestampWord evm).toNat ≤ (tickEndWord evm I).toNat) :
    ExecTransitionBody config contract evm (tickLocals I) tickTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tickTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_tick_end_lt_timestamp_false evm I hendGe)))

theorem flopperTickBodyReverts_ticNonzero (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hendLt : (tickEndWord evm I).toNat < (tickTimestampWord evm).toNat)
    (htic : tickTicWord evm I ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (tickLocals I) tickTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tickTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tick_end_lt_timestamp_true evm I hendLt)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_tick_tic_eq_zero_false evm I htic)))

theorem flopperTickBodyReverts_mulOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hendLt : (tickEndWord evm I).toNat < (tickTimestampWord evm).toNat)
    (htic : tickTicWord evm I = ⟨0⟩)
    (hoverflow : UInt256.size ≤ (tickPadWord evm).toNat * (tickLotWord evm I).toNat) :
    ExecTransitionBody config contract evm (tickLocals I) tickTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tickTransition, nonpayable, checkedMulUintInto] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tick_end_lt_timestamp_true evm I hendLt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tick_tic_eq_zero_true evm I htic)) <|
      ExecBlock.consRevert
        (ExecStmt.letDeclRevert (evalExpr_tick_lotBase_overflow evm I hoverflow)))

theorem flopperTickBodyReverts_addOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hendLt : (tickEndWord evm I).toNat < (tickTimestampWord evm).toNat)
    (htic : tickTicWord evm I = ⟨0⟩)
    (hmulFit : (tickPadWord evm).toNat * (tickLotWord evm I).toNat < UInt256.size)
    (haddOverflow :
      2 ^ 48 ≤
        (tickNow48Word evm).toNat + (tickTauWord (tickAfterLotStore evm I)).toNat) :
    ExecTransitionBody config contract evm (tickLocals I) tickTransition.body .reverted := by
  let evmLot := tickAfterLotStore evm I
  have hlotAssign :
      ExecBlock config { contract := contract, locals := tickLotBaseLocals evm I } evm
        [.assign .storage (bidsF (.var "id") "lot")
          (.binary .div (.var "lotBase") (.intLit ONE))]
        (.ok { contract := contract, locals := tickLotBaseLocals evm I } evmLot) := by
    exact ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_tick_lotPost evm I)
        (by simpa [evmLot] using assign_tickLotStorage evm evm I))
      ExecBlock.nil
  have hendChecked :
      ExecBlock config { contract := contract, locals := tickLotBaseLocals evm I } evmLot
        (checkedAdd48Into "end_" now48 (.storage tauRef)) .reverted := by
    simpa [checkedAdd48Into, evmLot] using
      (ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_tick_endAdd_wrapped evm I)) <|
        ExecBlock.consRevert
          (ExecStmt.requireFalse
            (evalExpr_tick_end_guard_false_wrapped evm I haddOverflow)))
  have hendTail :
      ExecBlock config { contract := contract, locals := tickLotBaseLocals evm I } evmLot
        (checkedAdd48Into "end_" now48 (.storage tauRef) ++
          [.assign .storage (bidsF (.var "id") "end") (.var "end_")]) .reverted :=
   execBlock_append_term hendChecked (by intro f e h; cases h)
  have htail :
      ExecBlock config { contract := contract, locals := tickLotBaseLocals evm I } evm
        ([.assign .storage (bidsF (.var "id") "lot")
            (.binary .div (.var "lotBase") (.intLit ONE))] ++
          (checkedAdd48Into "end_" now48 (.storage tauRef) ++
            [.assign .storage (bidsF (.var "id") "end") (.var "end_")]))
        .reverted :=
   execBlock_append hlotAssign hendTail
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tickTransition, nonpayable, checkedMulUintInto, List.cons_append, List.nil_append]
    using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tick_end_lt_timestamp_true evm I hendLt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tick_tic_eq_zero_true evm I htic)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_tick_lotBase_ok evm I hmulFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tick_mul_guard_true evm I hmulFit)) <|
      htail)

theorem flopperTickBodyReturns_success (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hendLt : (tickEndWord evm I).toNat < (tickTimestampWord evm).toNat)
    (htic : tickTicWord evm I = ⟨0⟩)
    (hmulFit : (tickPadWord evm).toNat * (tickLotWord evm I).toNat < UInt256.size)
    (haddFit :
      (tickNow48Word evm).toNat + (tickTauWord (tickAfterLotStore evm I)).toNat <
        2 ^ 48) :
    ExecTransitionBody config contract evm (tickLocals I) tickTransition.body
      (.returned { contract := contract, locals := tickEndLocals evm I }
        (tickPostState evm I) none) := by
  let evmLot := tickAfterLotStore evm I
  have hlotAssign :
      ExecBlock config { contract := contract, locals := tickLotBaseLocals evm I } evm
        [.assign .storage (bidsF (.var "id") "lot")
          (.binary .div (.var "lotBase") (.intLit ONE))]
        (.ok { contract := contract, locals := tickLotBaseLocals evm I } evmLot) := by
    exact ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_tick_lotPost evm I)
        (by simpa [evmLot] using assign_tickLotStorage evm evm I))
      ExecBlock.nil
  have hendLet :
      ExecBlock config { contract := contract, locals := tickLotBaseLocals evm I } evmLot
        (checkedAdd48Into "end_" now48 (.storage tauRef) ++
          [.assign .storage (bidsF (.var "id") "end") (.var "end_")])
        (.ok { contract := contract, locals := tickEndLocals evm I } (tickPostState evm I)) := by
    simpa [checkedAdd48Into, evmLot] using
      (ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_tick_endAdd_ok evm I haddFit)) <|
        ExecBlock.consNormal
          (ExecStmt.requireTrue (evalExpr_tick_end_guard_true evm I haddFit)) <|
        ExecBlock.consNormal
          (ExecStmt.assign (evalExpr_tick_end_var evm I)
            (assign_tickEndStorage_value evm I haddFit))
          ExecBlock.nil)
  have htail :
      ExecBlock config { contract := contract, locals := tickLotBaseLocals evm I } evm
        ([.assign .storage (bidsF (.var "id") "lot")
            (.binary .div (.var "lotBase") (.intLit ONE))] ++
          (checkedAdd48Into "end_" now48 (.storage tauRef) ++
            [.assign .storage (bidsF (.var "id") "end") (.var "end_")]))
        (.ok { contract := contract, locals := tickEndLocals evm I } (tickPostState evm I)) :=
   execBlock_append hlotAssign hendLet
  refine ExecFuncBody.execBlockOK ?_
  simpa [tickTransition, nonpayable, checkedMulUintInto, List.cons_append, List.nil_append]
    using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tick_end_lt_timestamp_true evm I hendLt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tick_tic_eq_zero_true evm I htic)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_tick_lotBase_ok evm I hmulFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tick_mul_guard_true evm I hmulFit)) <|
      htail)


theorem flopperDecode_tick_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (tickTransition.params.map Param.name)
      (transitionSignature tickTransition).paramTypes I.calldata = some (tickLocals I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [uint256] I.calldata =
    some (tickLocals I)
  simpa [config, tickLocals, tickIdValue, tickIdWord, uint256] using
    decodeCalldata_legacyUint256_ok (cd := I.calldata) (x := "id") hsz36

theorem flopperDecode_tick_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (tickTransition.params.map Param.name)
      (transitionSignature tickTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [uint256] I.calldata = none
  simpa [config, uint256] using
    decodeCalldata_legacyUint256_none_short (cd := I.calldata) (x := "id") hsz4 hshort

theorem flopperReachTickBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flopperSelBytes 14)) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨849⟩ [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flopperSelWord I = ⟨0xfc7b6aee⟩ := by
    simpa [flopperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0xfc 0x7b 0x6a 0xee ⟨0xfc7b6aee⟩
        (by native_decide) (by simpa [flopperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flopperBytecode flopperHighSplitPc)
      (flopperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flopperReachHighHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have heq0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighHighFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighHighFirstArmPc 4))
        (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨849⟩ 4 hfirst
    (fun j hj => flopperHighHighArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flopperTickX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨849⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flopperBytecode) (sel := sel) (entry := ⟨849⟩) (ret := ⟨334⟩)
    (decoded := ⟨871⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  have rd872 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd873 := rd872.pop (by native_decide) (by evm_ov)
  have rd874 := rd873.calldataload (by native_decide) (by evm_ov)
  have rd877 := rd874.push2 ⟨4292⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [tickIdWord, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd877.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flopperTickX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨849⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flopperBytecode) (sel := sel) (entry := ⟨849⟩) (ret := ⟨334⟩)
    (decoded := ⟨871⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem flopperTickX_toEndLtGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd4292 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tickIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4329⟩
      [UInt256.lt (flopperUint48Offset26Word (auctionPackedSlot id) σ I)
        (UInt256.ofNat I.header.timestamp), id, ⟨334⟩, sel]
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memMap
  let memKey := wordAt0Mem id solcFreePtrMem
  let base := solcMappingSlot ⟨1⟩ id
  have rd4297pre := evm_run rd4292 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd4298 := rd4297pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd4302pre := evm_run rd4298 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd4303 := rd4302pre.mstore 0 memMap (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd4306pre := evm_run rd4303 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id solcFreePtrMem
  have rd4307 := rd4306pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd4310pre := evm_run rd4307 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd4310pre
  obtain ⟨k4311, C4311, rd4311raw⟩ := rd4310pre.sload (by native_decide) (by evm_ov)
  have rd4311 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4311⟩
      [flopperSlotWord (auctionPackedSlot id) σ I, id, ⟨334⟩, sel]
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4311 C4311 := by
    simpa [flopperSlotWord] using rd4311raw
  have rd4320 := evm_run rd4311 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd4327 := rd4320.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4328 := rd4327.and (by native_decide) (by evm_ov)
  have rd4329 := rd4328.lt (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, flopperUint48Offset26Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩ = UInt256.ofNat (256 ^ 26)
        from by native_decide]
      using rd4329⟩

theorem flopperTickX_endNotExpired {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hendGe :
      (UInt256.ofNat I.header.timestamp).toNat ≤
        (flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat)
    (rd4292 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let id := tickIdWord I
  let memMap := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  obtain ⟨_, _, rd4292'⟩ := rd4292
  obtain ⟨_, _, rd4329⟩ := flopperTickX_toEndLtGuard rd4292'
  have hendLt :
      UInt256.lt (flopperUint48Offset26Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨0⟩ := by
    apply ult_zero
    simpa [id] using hendGe
  have rd4332 := rd4329.push2 ⟨4400⟩ (by native_decide) (by evm_ov)
  have rd4333raw := rd4332.jumpiNT (by native_decide) hendLt (by evm_ov)
  have hpc4333 : (⟨4329⟩ : UInt256) + UInt256.ofNat 3 + ⟨1⟩ = ⟨4333⟩ := by
    native_decide
  rw [hpc4333] at rd4333raw
  exact RD.solcErrorStringRevertTail
    (pc := ⟨4333⟩)
    (len := ⟨20⟩)
    (rawWord := ⟨0x119b1bdc1c195c8bdb9bdd0b599a5b9a5cda1959⟩)
    (shift := ⟨98⟩)
    (word := ⟨0x466c6f707065722f6e6f742d66696e6973686564000000000000000000000000⟩)
    (op := .PUSH20)
    (width := 20)
    rd4333raw
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    (by
      simpa [memMap, id] using
        twoWordHashMem_size_96 (tickIdWord I) ⟨1⟩ solcFreePtrMem_size)
    (by
      simpa [memMap, id] using
        twoWordHashMem_read64 (tickIdWord I) ⟨1⟩ solcFreePtrMem_size
          solcFreePtrMem_read64)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem flopperTickX_toTicZeroGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hendLt :
      (flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (rd4292 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tickIdWord I
    let memEnd := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memTic := twoWordHashMem id ⟨1⟩ memEnd
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4435⟩
      [UInt256.isZero (flopperUint48Offset20Word (auctionPackedSlot id) σ I),
        id, ⟨334⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memEnd memTic
  obtain ⟨_, _, rd4292'⟩ := rd4292
  obtain ⟨_, _, rd4329⟩ := flopperTickX_toEndLtGuard rd4292'
  have hendLtWord :
      UInt256.lt (flopperUint48Offset26Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨1⟩ := by
    apply ult_one
    simpa [id] using hendLt
  have rd4332 := rd4329.push2 ⟨4400⟩ (by native_decide) (by evm_ov)
  have rd4400 := rd4332.jumpiT (by native_decide)
    (by rw [hendLtWord]; exact one_ne_zero_uint) (by jump_dest) (by evm_ov)
  let memKey := wordAt0Mem id memEnd
  let base := solcMappingSlot ⟨1⟩ id
  have rd4405pre := evm_run rd4400 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd4406 := rd4405pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, memEnd, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd4410pre := evm_run rd4406 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd4411 := rd4410pre.mstore 0 memTic (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memTic, memEnd, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd4414pre := evm_run rd4411 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memTic.readWithPadding 0 64))) = base := by
    simpa [base, memTic, memEnd, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memEnd
  have rd4415 := rd4414pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd4418pre := evm_run rd4415 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd4418pre
  obtain ⟨k4419, C4419, rd4419raw⟩ := rd4418pre.sload (by native_decide) (by evm_ov)
  have rd4419 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4419⟩
      [flopperSlotWord (auctionPackedSlot id) σ I, id, ⟨334⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4419 C4419 := by
    simpa [flopperSlotWord] using rd4419raw
  have rd4426 := evm_run rd4419 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd4433 := rd4426.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4434 := rd4433.and (by native_decide) (by evm_ov)
  have rd4435 := rd4434.iszero (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, flopperUint48Offset20Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = UInt256.ofNat (256 ^ 20)
        from by native_decide]
      using rd4435⟩

@[reducible] def solcErrorStringRevertTailFullWordWf
    (code : ByteArray) (pc len word : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p8 := p4 + UInt256.ofNat 4
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p24 := p22 + UInt256.ofNat 2
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p68 := p27 + UInt256.ofNat 33
  let pDup3 := p68 + UInt256.ofNat 2
  let pAdd := pDup3 + ⟨1⟩
  let pMstore3 := pAdd + ⟨1⟩
  let pSwap := pMstore3 + ⟨1⟩
  let pMload := pSwap + ⟨1⟩
  let pSwap2 := pMload + ⟨1⟩
  let pDup2 := pSwap2 + ⟨1⟩
  let pSwap3 := pDup2 + ⟨1⟩
  let pSub := pSwap3 + ⟨1⟩
  let p100 := pSub + ⟨1⟩
  let pAdd2 := p100 + UInt256.ofNat 2
  let pSwap4 := pAdd2 + ⟨1⟩
  let pRev := pSwap4 + ⟨1⟩
  decode code pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p2 = some (.DUP1, .none)
  ∧ decode code p3 = some (.MLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode code p10 = some (.SHL, .none)
  ∧ decode code p11 = some (.DUP2, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p17 = some (.DUP3, .none)
  ∧ decode code p18 = some (.ADD, .none)
  ∧ decode code p19 = some (.MSTORE, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (len, 1))
  ∧ decode code p22 = some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode code p24 = some (.DUP3, .none)
  ∧ decode code p25 = some (.ADD, .none)
  ∧ decode code p26 = some (.MSTORE, .none)
  ∧ decode code p27 = some (.Push .PUSH32, some (word, 32))
  ∧ decode code p68 = some (.Push .PUSH1, some (⟨68⟩, 1))
  ∧ decode code pDup3 = some (.DUP3, .none)
  ∧ decode code pAdd = some (.ADD, .none)
  ∧ decode code pMstore3 = some (.MSTORE, .none)
  ∧ decode code pSwap = some (.SWAP1, .none)
  ∧ decode code pMload = some (.MLOAD, .none)
  ∧ decode code pSwap2 = some (.SWAP1, .none)
  ∧ decode code pDup2 = some (.DUP2, .none)
  ∧ decode code pSwap3 = some (.SWAP1, .none)
  ∧ decode code pSub = some (.SUB, .none)
  ∧ decode code p100 = some (.Push .PUSH1, some (⟨100⟩, 1))
  ∧ decode code pAdd2 = some (.ADD, .none)
  ∧ decode code pSwap4 = some (.SWAP1, .none)
  ∧ decode code pRev = some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem solcErrorStringRevertTailFullWord {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {pc len word : UInt256}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcErrorStringRevertTailFullWordWf code pc len word)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hd68, hdDup3, hdAdd,
      hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3, hdSub, hd100,
      hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdWord := rdPrefix.pushConst word (width := 32) (op := .PUSH32)
    (by decide : Operation.POp.PUSH32 ≠ .PUSH0) hd27
    (by simp only [List.length_cons]; omega)
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 8) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hdMload
      mem_cost
      (solcErrorStringMem3_mload64 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

theorem flopperTickX_ticNonzero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hendLt :
      (flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ I ≠ ⟨0⟩)
    (rd4292 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let id := tickIdWord I
  let memEnd := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memEnd
  obtain ⟨_, _, rd4435⟩ := flopperTickX_toTicZeroGuard hendLt rd4292
  have hcond :
      UInt256.isZero (flopperUint48Offset20Word (auctionPackedSlot id) σ I) = ⟨0⟩ := by
    exact isZero_eq_zero_of_ne (by simpa [id] using htic)
  have rd4438 := rd4435.push2 ⟨4515⟩ (by native_decide) (by evm_ov)
  have rd4439raw := rd4438.jumpiNT (by native_decide) hcond (by evm_ov)
  have hpc4439 : (⟨4435⟩ : UInt256) + UInt256.ofNat 3 + ⟨1⟩ = ⟨4439⟩ := by
    native_decide
  rw [hpc4439] at rd4439raw
  have hmemEnd : memEnd.size = 96 := by
    simpa [memEnd, id] using
      twoWordHashMem_size_96 (tickIdWord I) ⟨1⟩ solcFreePtrMem_size
  have hreadEnd : memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memEnd, id] using
      twoWordHashMem_read64 (tickIdWord I) ⟨1⟩ solcFreePtrMem_size
        solcFreePtrMem_read64
  exact solcErrorStringRevertTailFullWord
    (pc := ⟨4439⟩)
    (len := ⟨26⟩)
    (word :=
      ⟨0x466c6f707065722f6269642d616c72656164792d706c61636564000000000000⟩)
    rd4439raw
    (by
      unfold solcErrorStringRevertTailFullWordWf
      repeat' first | apply And.intro | native_decide)
    (by
      simpa [memTic, id] using
        twoWordHashMem_size_96 (tickIdWord I) ⟨1⟩ hmemEnd)
    (by
      simpa [memTic, id] using
        twoWordHashMem_read64 (tickIdWord I) ⟨1⟩ hmemEnd hreadEnd)
    (by simp)

end Benchmarks.Dss.Flopper
