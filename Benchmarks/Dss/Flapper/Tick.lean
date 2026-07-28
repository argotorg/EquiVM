import Benchmarks.Dss.Flapper.Yank
import Benchmarks.Dss.Flopper.Tick.Part1

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flapper

/-! ## `tick(uint256)` -/

theorem evalStorageRef_auction_field (evm : EVM.State) (locals : Store)
    (id : UInt256) (field : Ident)
    (hget : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    evalStorageRef config { contract := contract, locals := locals } evm
        (bidsF (.var "id") field) =
      .ok { base := "bids", steps := [.mindex (auctionIdKey id), .field field] } := by
  have hgetElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hget
  simp [bidsF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    hgetElem, auctionIdKey, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]

theorem flapperUint48Offset6Word_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flapperUint48Offset6Word slot σ I = flapperUint48Offset6Word slot τ I := by
  simp [flapperUint48Offset6Word, flapperSlotWord_accountMapEquiv hAccounts slot]

theorem flapperUint48Offset20Word_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flapperUint48Offset20Word slot σ I = flapperUint48Offset20Word slot τ I := by
  simp [flapperUint48Offset20Word, flapperSlotWord_accountMapEquiv hAccounts slot]

theorem flapperUint48Offset26Word_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flapperUint48Offset26Word slot σ I = flapperUint48Offset26Word slot τ I := by
  simp [flapperUint48Offset26Word, flapperSlotWord_accountMapEquiv hAccounts slot]

def setUint48Offset26Word (old data : UInt256) : UInt256 :=
  UInt256.ofNat
    (old.toNat % 2 ^ 208 + (UInt256.land data flapperUint48Mask).toNat * 2 ^ 208)

theorem setUint48Offset26Word_toNat (old data : UInt256) :
    (setUint48Offset26Word old data).toNat =
      old.toNat % 2 ^ 208 + (UInt256.land data flapperUint48Mask).toNat * 2 ^ 208 := by
  unfold setUint48Offset26Word
  have hsumLt :
      old.toNat % 2 ^ 208 + (UInt256.land data flapperUint48Mask).toNat * 2 ^ 208 <
        UInt256.size := by
    have hlow : old.toNat % 2 ^ 208 < 2 ^ 208 := Nat.mod_lt _ (by norm_num)
    have hdata : (UInt256.land data flapperUint48Mask).toNat < 2 ^ 48 := by
      simpa [flapperUint48Mask, EVM.twoPow] using flapperUint48Masked_lt data
    have hlowLe : old.toNat % 2 ^ 208 ≤ 2 ^ 208 - 1 := Nat.le_pred_of_lt hlow
    have hdataLe : (UInt256.land data flapperUint48Mask).toNat ≤ 2 ^ 48 - 1 :=
      Nat.le_pred_of_lt hdata
    have hdataTerm :
        (UInt256.land data flapperUint48Mask).toNat * 2 ^ 208 ≤
          (2 ^ 48 - 1) * 2 ^ 208 :=
      Nat.mul_le_mul_right _ hdataLe
    have hmax : (2 ^ 208 - 1) + (2 ^ 48 - 1) * 2 ^ 208 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  exact UInt256.toNat_ofNat_of_lt hsumLt

abbrev tickRuntimeEndClearMask : UInt256 :=
  UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩ - ⟨1⟩

abbrev tickRuntimeEndShiftedWord (data : UInt256) : UInt256 :=
  UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩ * UInt256.land flapperUint48Mask data

abbrev tickRuntimeEndStoredRawWord (old data : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old tickRuntimeEndClearMask) (tickRuntimeEndShiftedWord data)

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
  rw [show (UInt256.land flapperUint48Mask data).toNat =
      (UInt256.land data flapperUint48Mask).toNat by rw [u256_land_comm]]
  let data48 := (UInt256.land data flapperUint48Mask).toNat
  have hdata : (UInt256.land data flapperUint48Mask).toNat < 2 ^ 48 := by
    simpa [flapperUint48Mask, EVM.twoPow] using flapperUint48Masked_lt data
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

theorem tickWordOfInt_emod_uint48 (w : UInt256) :
    EVM.wordOfInt (Int.ofNat w.toNat % uint48Modulus) =
      UInt256.land w flapperUint48Mask := by
  simpa [uint48Modulus, flapperUint48Mask, Benchmarks.Dss.Flopper.uint48Modulus,
    Benchmarks.Dss.Flopper.flopperUint48Mask] using
    Benchmarks.Dss.Flopper.auctionWordOfInt_emod_uint48 w

theorem storageLocStore_uint48_offset26_word (evm : EVM.State) (slot data : UInt256) :
    storageLocStore evm (uint48Loc slot ⟨26, by decide⟩ (by decide))
        (.int (Int.ofNat data.toNat % uint48Modulus)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint48Offset26Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) data)) := by
  unfold storageLocStore storageLocWriteWord uint48Loc
  simp only [valueToWord, tickWordOfInt_emod_uint48, bind, Option.bind]
  congr 2
  apply u256_inj
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot
  show fromBytes'
      (List.take (26 : Fin 32).val _ ++ List.take (6 : Fin 33).val _ ++
        List.drop ((26 : Fin 32).val + (6 : Fin 33).val) _) =
      (setUint48Offset26Word old data).toNat
  rw [show (26 : Fin 32).val = 26 from rfl, show (6 : Fin 33).val = 6 from rfl]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE_land_mask _ 6 (by norm_num),
    fromBytes'_drop_wordLE]
  have hlenOld26 :
      ((EVM.Word.toBytesLEWithSizeProof old).1.take 26).length = 26 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof old).2]
    norm_num
  have hlenData6 :
      ((EVM.Word.toBytesLEWithSizeProof (UInt256.land data flapperUint48Mask)).1.take 6).length =
        6 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.land data flapperUint48Mask)).2]
    norm_num
  rw [List.length_append, hlenOld26, hlenData6]
  rw [show 2 ^ (8 * 26) = (2 : Nat) ^ 208 by norm_num]
  rw [show 2 ^ (8 * 6) = (2 : Nat) ^ 48 by norm_num]
  rw [show 2 ^ (8 * (26 + 6)) = (2 : Nat) ^ 256 by norm_num]
  rw [show 256 ^ (26 + 6) = (2 : Nat) ^ 256 by norm_num]
  rw [setUint48Offset26Word_toNat]
  have hclean : UInt256.land (UInt256.land data flapperUint48Mask)
      (UInt256.ofNat (2 ^ 48 - 1)) = UInt256.land data flapperUint48Mask := by
    simpa [flapperUint48Mask] using flapperUint48Mask_clean data
  rw [hclean]
  have hdiv : old.toNat / 2 ^ 256 = 0 := by
    exact Nat.div_eq_of_lt (by
      change old.val.val < 2 ^ 256
      exact old.val.isLt)
  dsimp [old]
  ring_nf
  have hdiv' :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat /
          115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        0 := by
    simpa [old] using hdiv
  rw [hdiv']
  simp

theorem uint48Mask_add_no_wrap_toNat (a b : UInt256)
    (hfit : (UInt256.land a flapperUint48Mask).toNat + b.toNat < 2 ^ 48) :
    (UInt256.land (a + b) flapperUint48Mask).toNat =
      (UInt256.land a flapperUint48Mask).toNat + b.toNat := by
  simpa [flapperUint48Mask, Benchmarks.Dss.Flopper.flopperUint48Mask] using
    Benchmarks.Dss.Flopper.uint48Mask_add_no_wrap_toNat a b hfit

theorem uint48Mask_add_toNat_mod (a b : UInt256) (hb : b.toNat < 2 ^ 48) :
    (UInt256.land (a + b) flapperUint48Mask).toNat =
      ((UInt256.land a flapperUint48Mask).toNat + b.toNat) % 2 ^ 48 := by
  simpa [flapperUint48Mask, Benchmarks.Dss.Flopper.flopperUint48Mask] using
    Benchmarks.Dss.Flopper.uint48Mask_add_toNat_mod a b hb

theorem uint48AddGuard_false_of_no_wrap (a b : UInt256)
    (hfit : (UInt256.land a flapperUint48Mask).toNat + b.toNat < 2 ^ 48) :
    UInt256.lt (UInt256.land (a + b) flapperUint48Mask)
        (UInt256.land a flapperUint48Mask) = ⟨0⟩ := by
  simpa [flapperUint48Mask, Benchmarks.Dss.Flopper.flopperUint48Mask] using
    Benchmarks.Dss.Flopper.uint48AddGuard_false_of_no_wrap a b hfit

theorem uint48AddGuard_true_of_wrap (a b : UInt256)
    (hb : b.toNat < 2 ^ 48)
    (hover : 2 ^ 48 ≤ (UInt256.land a flapperUint48Mask).toNat + b.toNat) :
    UInt256.lt (UInt256.land (a + b) flapperUint48Mask)
        (UInt256.land a flapperUint48Mask) = ⟨1⟩ := by
  simpa [flapperUint48Mask, Benchmarks.Dss.Flopper.flopperUint48Mask] using
    Benchmarks.Dss.Flopper.uint48AddGuard_true_of_wrap a b hb hover

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

abbrev tickTauEvaledRef : EvaledStorageRef :=
  { base := "tau", steps := [] }

abbrev tickEndWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flapperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) evm.accountMap
    evm.executionEnv

abbrev tickTicWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flapperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) evm.accountMap
    evm.executionEnv

abbrev tickTauWord (evm : EVM.State) : UInt256 :=
  flapperUint48Offset6Word ⟨5⟩ evm.accountMap evm.executionEnv

abbrev tickTimestampWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp

abbrev tickNow48Word (evm : EVM.State) : UInt256 :=
  UInt256.land (tickTimestampWord evm) flapperUint48Mask

abbrev tickEndPostWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat ((tickNow48Word evm).toNat + (tickTauWord evm).toNat)

abbrev tickEndLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (tickLocals I).insert "end_" (.int (Int.ofNat (tickEndPostWord evm).toNat))

abbrev tickEndWrappedNat (evm : EVM.State) : Nat :=
  ((tickNow48Word evm).toNat + (tickTauWord evm).toNat) % 2 ^ 48

abbrev tickEndWrappedLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (tickLocals I).insert "end_" (.int (Int.ofNat (tickEndWrappedNat evm)))

def tickEndStoredWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  setUint48Offset26Word
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (auctionPackedSlot (tickIdWord I)))
    (tickEndPostWord evm)

def tickPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (auctionPackedSlot (tickIdWord I))
    (tickEndStoredWord evm I)

abbrev tickRuntimeTauWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperUint48Offset6Word ⟨5⟩ σ I

abbrev tickRuntimeAddWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp + tickRuntimeTauWord σ I

def tickRuntimeSuccessAccountMap (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : AccountMap :=
  let old := solcSlotWord σ I (auctionPackedSlot (tickIdWord I))
  sstoreAccountMap owner σ (auctionPackedSlot (tickIdWord I))
    (tickRuntimeEndStoredRawWord old (tickRuntimeAddWord σ I))

theorem tickLocals_get_id (I : ExecutionEnv) :
    (tickLocals I).get? "id" = some (tickIdValue I) := by
  simp [tickLocals]

theorem tickLocals_get_bids (I : ExecutionEnv) :
    (tickLocals I).get? "bids" = none := by
  rw [tickLocals, store_get_ne _ _ (by decide)]
  simp [Std.HashMap.get?_eq_getElem?]

theorem tickEndLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (tickEndLocals evm I).get? "id" = some (tickIdValue I) := by
  rw [tickEndLocals, store_get_ne _ _ (by decide)]
  exact tickLocals_get_id I

theorem tickEndLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) :
    (tickEndLocals evm I).get? "bids" = none := by
  rw [tickEndLocals, store_get_ne _ _ (by decide)]
  exact tickLocals_get_bids I

theorem tickEndLocals_get_end (evm : EVM.State) (I : ExecutionEnv) :
    (tickEndLocals evm I).get? "end_" =
      some (.int (Int.ofNat (tickEndPostWord evm).toNat)) := by
  rw [tickEndLocals, store_get_self]

theorem tickEndWrappedLocals_get_end (evm : EVM.State) (I : ExecutionEnv) :
    (tickEndWrappedLocals evm I).get? "end_" =
      some (.int (Int.ofNat (tickEndWrappedNat evm))) := by
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

theorem tickEndPostWord_toNat (evm : EVM.State)
    (hfit : (tickNow48Word evm).toNat + (tickTauWord evm).toNat < 2 ^ 48) :
    (tickEndPostWord evm).toNat =
      (tickNow48Word evm).toNat + (tickTauWord evm).toNat := by
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
    rw [flapperStorageLocLoad_uint48_offset26]
    rw [u256_land_comm
      (UInt256.div
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (auctionPackedSlot (tickIdWord I)))
        (UInt256.ofNat (256 ^ 26)))
      flapperUint48Mask]
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
    (by
      funext evm'
      exact auctionEndLayout evm' (tickIdWord I))
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
    rw [flapperStorageLocLoad_uint48_offset20]
    rw [u256_land_comm
      (UInt256.div
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (auctionPackedSlot (tickIdWord I)))
        (UInt256.ofNat (256 ^ 20)))
      flapperUint48Mask]
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
    (by
      funext evm'
      exact auctionTicLayout evm' (tickIdWord I))
    hload

theorem evalExpr_tick_tau_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickLocals I } evm
        (.storage tauRef) =
      .ok (.int (Int.ofNat (tickTauWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := tickLocals I }
  have hload :
      storageLocLoad evm (uint48Loc ⟨5⟩ ⟨6, by decide⟩ (by decide)) =
        .int (Int.ofNat (tickTauWord evm).toNat) := by
    rw [flapperStorageLocLoad_uint48_offset6]
    rw [u256_land_comm
      (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
        (UInt256.ofNat (256 ^ 6))) flapperUint48Mask]
    rfl
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := tauRef) (er := tickTauEvaledRef)
    (t := .int uint48Int) (loc := uint48Loc ⟨5⟩ ⟨6, by decide⟩ (by decide))
    (value := .int (Int.ofNat (tickTauWord evm).toNat))
    (by simp [frame, tauRef, tickLocals])
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

theorem evalExpr_tick_now48 (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickLocals I } evm now48 =
      .ok (.int (Int.ofNat (tickNow48Word evm).toNat)) := by
  unfold now48 wrap48
  simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hmod :
      Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat %
          uint48Modulus =
        Int.ofNat (tickNow48Word evm).toNat := by
    have hnow := tickNow48Word_toNat evm
    rw [hnow]
    norm_num [uint48Modulus, Int.natCast_mod]
  simpa [uint48Modulus] using hmod

theorem evalExpr_tick_endAdd_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (tickNow48Word evm).toNat + (tickTauWord evm).toNat < 2 ^ 48) :
    evalExpr? config { contract := contract, locals := tickLocals I } evm
        (wrap48 (.binary .add now48 (.storage tauRef))) =
      .ok (.int (Int.ofNat (tickEndPostWord evm).toNat)) := by
  have hnow := evalExpr_tick_now48 evm I
  have htau := evalExpr_tick_tau_storage evm I
  have hendNat := tickEndPostWord_toNat evm hfit
  unfold wrap48
  simp only [evalExpr?, hnow, htau, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hsumMod :
      (Int.ofNat (tickNow48Word evm).toNat +
          Int.ofNat (tickTauWord evm).toNat) % uint48Modulus =
        Int.ofNat (tickEndPostWord evm).toNat := by
    rw [hendNat]
    have hsumCast :
        Int.ofNat ((tickNow48Word evm).toNat + (tickTauWord evm).toNat) =
          Int.ofNat (tickNow48Word evm).toNat + Int.ofNat (tickTauWord evm).toNat := by
      norm_num
    rw [← hsumCast]
    have hfitInt :
        Int.ofNat ((tickNow48Word evm).toNat + (tickTauWord evm).toNat) <
          uint48Modulus := by
      change Int.ofNat ((tickNow48Word evm).toNat + (tickTauWord evm).toNat) <
        Int.ofNat (2 ^ 48)
      exact Int.ofNat_lt.mpr hfit
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) hfitInt
  simpa [uint48Modulus] using hsumMod

theorem evalExpr_tick_endAdd_wrapped (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickLocals I } evm
        (wrap48 (.binary .add now48 (.storage tauRef))) =
      .ok (.int (Int.ofNat (tickEndWrappedNat evm))) := by
  have hnow := evalExpr_tick_now48 evm I
  have htau := evalExpr_tick_tau_storage evm I
  unfold wrap48
  simp only [evalExpr?, hnow, htau, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hsumMod :
      (Int.ofNat (tickNow48Word evm).toNat + Int.ofNat (tickTauWord evm).toNat) %
          uint48Modulus =
        Int.ofNat (tickEndWrappedNat evm) := by
    have hsumCast :
        Int.ofNat ((tickNow48Word evm).toNat + (tickTauWord evm).toNat) =
          Int.ofNat (tickNow48Word evm).toNat + Int.ofNat (tickTauWord evm).toNat := by
      norm_num
    rw [← hsumCast]
    norm_num [tickEndWrappedNat, uint48Modulus, Int.natCast_mod]
  simpa [uint48Modulus] using hsumMod

theorem evalExpr_tick_end_guard_true (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (tickNow48Word evm).toNat + (tickTauWord evm).toNat < 2 ^ 48) :
    evalExpr? config { contract := contract, locals := tickEndLocals evm I } evm
      (.binary .ge (.var "end_") now48) = .ok (.bool true) := by
  have hend :
      evalExpr? config { contract := contract, locals := tickEndLocals evm I } evm (.var "end_") =
        .ok (.int (Int.ofNat (tickEndPostWord evm).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((tickEndLocals evm I).get? "end_") =
      .ok (.int (Int.ofNat (tickEndPostWord evm).toNat))
    rw [tickEndLocals_get_end]
    rfl
  have hnow :
      evalExpr? config { contract := contract, locals := tickEndLocals evm I } evm now48 =
        .ok (.int (Int.ofNat (tickNow48Word evm).toNat)) := by
    unfold now48 wrap48
    simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
    have hmod :
        Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat %
            uint48Modulus =
          Int.ofNat (tickNow48Word evm).toNat := by
      have hnowNat := tickNow48Word_toNat evm
      rw [hnowNat]
      norm_num [uint48Modulus, Int.natCast_mod]
    simpa [uint48Modulus] using hmod
  have hendNat := tickEndPostWord_toNat evm hfit
  have hge :
      Int.ofNat (tickNow48Word evm).toNat ≤
        Int.ofNat (tickEndPostWord evm).toNat := by
    rw [hendNat]
    change Int.ofNat (tickNow48Word evm).toNat ≤
      Int.ofNat ((tickNow48Word evm).toNat + (tickTauWord evm).toNat)
    exact Int.ofNat_le.mpr (Nat.le_add_right _ _)
  simp only [evalExpr?, hend, hnow, EvalResult.bind, bind, evalBinaryOp?]
  simpa using hge

theorem evalExpr_tick_end_guard_false_wrapped (evm : EVM.State) (I : ExecutionEnv)
    (hoverflow : 2 ^ 48 ≤ (tickNow48Word evm).toNat + (tickTauWord evm).toNat) :
    evalExpr? config { contract := contract, locals := tickEndWrappedLocals evm I } evm
      (.binary .ge (.var "end_") now48) = .ok (.bool false) := by
  have hend :
      evalExpr? config { contract := contract, locals := tickEndWrappedLocals evm I } evm
          (.var "end_") =
        .ok (.int (Int.ofNat (tickEndWrappedNat evm))) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((tickEndWrappedLocals evm I).get? "end_") =
      .ok (.int (Int.ofNat (tickEndWrappedNat evm)))
    rw [tickEndWrappedLocals_get_end]
    rfl
  have hnow :
      evalExpr? config { contract := contract, locals := tickEndWrappedLocals evm I } evm now48 =
        .ok (.int (Int.ofNat (tickNow48Word evm).toNat)) := by
    unfold now48 wrap48
    simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
    have hmod :
        Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat %
            uint48Modulus =
          Int.ofNat (tickNow48Word evm).toNat := by
      have hnowNat := tickNow48Word_toNat evm
      rw [hnowNat]
      norm_num [uint48Modulus, Int.natCast_mod]
    simpa [uint48Modulus] using hmod
  have hnowLt : (tickNow48Word evm).toNat < 2 ^ 48 := by
    have h := tickNow48Word_toNat evm
    rw [h]
    exact Nat.mod_lt _ (by norm_num)
  have htauLt : (tickTauWord evm).toNat < 2 ^ 48 := by
    simpa [tickTauWord, flapperUint48Offset6Word, EVM.twoPow, u256_land_comm] using
      flapperUint48Masked_lt
        (UInt256.div
          (flapperSlotWord ⟨5⟩ evm.accountMap evm.executionEnv)
          (UInt256.ofNat (256 ^ 6)))
  have hwrappedLt : tickEndWrappedNat evm < (tickNow48Word evm).toNat := by
    unfold tickEndWrappedNat
    have hsumLt :
        (tickNow48Word evm).toNat + (tickTauWord evm).toNat < 2 ^ 49 := by
      omega
    rw [Nat.mod_eq_sub_mod hoverflow]
    have hsubLt :
        (tickNow48Word evm).toNat + (tickTauWord evm).toNat - 2 ^ 48 < 2 ^ 48 := by
      omega
    rw [Nat.mod_eq_of_lt hsubLt]
    omega
  have hdec :
      decide (Int.ofNat (tickNow48Word evm).toNat ≤
          Int.ofNat (tickEndWrappedNat evm)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    exact (Nat.not_le_of_gt hwrappedLt) (Int.ofNat_le.mp hle)
  simp only [evalExpr?, hend, hnow, EvalResult.bind, bind, evalBinaryOp?]
  rw [hdec]

theorem assign_tickEndStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := tickEndLocals evm I } evm
      .storage (bidsF (.var "id") "end")
        (.int (Int.ofNat (tickEndPostWord evm).toNat % uint48Modulus)) =
      .ok ({ contract := contract, locals := tickEndLocals evm I }, tickPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint48St)
      (er := tickEndEvaledRef I)
      (loc := uint48Loc (auctionPackedSlot (tickIdWord I)) ⟨26, by decide⟩ (by decide))
      (hbase := tickEndLocals_get_bids evm I)
      (her := by
        simpa [tickEndEvaledRef, tickIdValue] using
          evalStorageRef_auction_field evm (tickEndLocals evm I) (tickIdWord I) "end"
            (by simpa [tickIdValue] using tickEndLocals_get_id evm I))
      (hty := by
        simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          BidStructTy, uint48St])
      (hloc := by
        funext evm'
        exact auctionEndLayout evm' (tickIdWord I))
  simpa [tickPostState, tickEndStoredWord, uint48Loc] using
    storageLocStore_uint48_offset26_word evm
      (auctionPackedSlot (tickIdWord I)) (tickEndPostWord evm)

theorem tickEndPostWord_mod (evm : EVM.State)
    (hfit : (tickNow48Word evm).toNat + (tickTauWord evm).toNat < 2 ^ 48) :
    Int.ofNat (tickEndPostWord evm).toNat % uint48Modulus =
      Int.ofNat (tickEndPostWord evm).toNat := by
  have hendNat := tickEndPostWord_toNat evm hfit
  have hendLt : (tickEndPostWord evm).toNat < 2 ^ 48 := by
    rw [hendNat]
    exact hfit
  have hendLtInt :
      Int.ofNat (tickEndPostWord evm).toNat < uint48Modulus := by
    change Int.ofNat (tickEndPostWord evm).toNat < Int.ofNat (2 ^ 48)
    exact Int.ofNat_lt.mpr hendLt
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) hendLtInt

theorem assign_tickEndStorage_value (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (tickNow48Word evm).toNat + (tickTauWord evm).toNat < 2 ^ 48) :
    assignStorageRef? config { contract := contract, locals := tickEndLocals evm I } evm
      .storage (bidsF (.var "id") "end")
        (.int (Int.ofNat (tickEndPostWord evm).toNat)) =
      .ok ({ contract := contract, locals := tickEndLocals evm I }, tickPostState evm I) := by
  rw [← tickEndPostWord_mod evm hfit]
  exact assign_tickEndStorage evm I

theorem evalExpr_tick_end_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tickEndLocals evm I } evm (.var "end_") =
      .ok (.int (Int.ofNat (tickEndPostWord evm).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((tickEndLocals evm I).get? "end_") =
    .ok (.int (Int.ofNat (tickEndPostWord evm).toNat))
  rw [tickEndLocals_get_end]
  rfl

theorem flapperTickBodyReverts_endNotExpired (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hendGe : (tickTimestampWord evm).toNat ≤ (tickEndWord evm I).toNat) :
    ExecTransitionBody config contract evm (tickLocals I) tickTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tickTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_tick_end_lt_timestamp_false evm I hendGe)))

theorem flapperTickBodyReverts_ticNonzero (evm : EVM.State) (I : ExecutionEnv)
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

theorem flapperTickBodyReverts_addOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hendLt : (tickEndWord evm I).toNat < (tickTimestampWord evm).toNat)
    (htic : tickTicWord evm I = ⟨0⟩)
    (haddOverflow : 2 ^ 48 ≤ (tickNow48Word evm).toNat + (tickTauWord evm).toNat) :
    ExecTransitionBody config contract evm (tickLocals I) tickTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tickTransition, nonpayable, checkedAdd48Into, List.cons_append, List.nil_append]
    using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tick_end_lt_timestamp_true evm I hendLt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tick_tic_eq_zero_true evm I htic)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_tick_endAdd_wrapped evm I)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_tick_end_guard_false_wrapped evm I haddOverflow)))

theorem flapperTickBodyReturns_success (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hendLt : (tickEndWord evm I).toNat < (tickTimestampWord evm).toNat)
    (htic : tickTicWord evm I = ⟨0⟩)
    (haddFit : (tickNow48Word evm).toNat + (tickTauWord evm).toNat < 2 ^ 48) :
    ExecTransitionBody config contract evm (tickLocals I) tickTransition.body
      (.returned { contract := contract, locals := tickEndLocals evm I }
        (tickPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [tickTransition, nonpayable, checkedAdd48Into, List.cons_append, List.nil_append]
    using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tick_end_lt_timestamp_true evm I hendLt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tick_tic_eq_zero_true evm I htic)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_tick_endAdd_ok evm I haddFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tick_end_guard_true evm I haddFit)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_tick_end_var evm I)
          (assign_tickEndStorage_value evm I haddFit))
        ExecBlock.nil)

/-- Legacy solc-0.5 single-`uint256` calldata decode, local to `tick`. -/
theorem tickDecodeCalldata_legacyUint256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

theorem tickDecodeCalldata_legacyUint256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
    (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem flapperDecode_tick_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (tickTransition.params.map Param.name)
      (transitionSignature tickTransition).paramTypes I.calldata = some (tickLocals I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [uint256] I.calldata =
    some (tickLocals I)
  simpa [config, tickLocals, tickIdValue, tickIdWord, uint256] using
    tickDecodeCalldata_legacyUint256_ok (cd := I.calldata) (x := "id") hsz36

theorem flapperDecode_tick_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (tickTransition.params.map Param.name)
      (transitionSignature tickTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [uint256] I.calldata = none
  simpa [config, uint256] using
    tickDecodeCalldata_legacyUint256_none_short (cd := I.calldata) (x := "id") hsz4 hshort

theorem flapperReachTickBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flapperSelBytes 15)) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨855⟩ [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flapperSelWord I = ⟨0xfc7b6aee⟩ := by
    simpa [flapperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0xfc 0x7b 0x6a 0xee ⟨0xfc7b6aee⟩
        (by native_decide) (by simpa [flapperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flapperBytecode flapperHighSplitPc)
      (flapperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flapperReachHighHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have heq0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighHighFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighHighFirstArmPc 4))
        (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨855⟩ 4 hfirst
    (fun j hj => flapperHighHighArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flapperTickX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨855⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4586⟩
      [tickIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flapperBytecode) (sel := sel) (entry := ⟨855⟩) (ret := ⟨360⟩)
    (decoded := ⟨877⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  have rd878 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd879 := rd878.pop (by native_decide) (by evm_ov)
  have rd880 := rd879.calldataload (by native_decide) (by evm_ov)
  have rd883 := rd880.push2 ⟨4586⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [tickIdWord, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd883.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flapperTickX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨855⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flapperBytecode) (sel := sel) (entry := ⟨855⟩) (ret := ⟨360⟩)
    (decoded := ⟨877⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem flapperTickX_toEndLtGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd4586 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4586⟩
      [tickIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tickIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4623⟩
      [UInt256.lt (flapperUint48Offset26Word (auctionPackedSlot id) σ I)
        (UInt256.ofNat I.header.timestamp), id, ⟨360⟩, sel]
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memMap
  let memKey := wordAt0Mem id solcFreePtrMem
  let base := solcMappingSlot ⟨1⟩ id
  have rd4591pre := evm_run rd4586 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd4592 := rd4591pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd4596pre := evm_run rd4592 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd4597 := rd4596pre.mstore 0 memMap (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd4600pre := evm_run rd4597 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id] using
      Benchmarks.Dss.Flopper.twoWordHashMem_solcMappingSlot_any ⟨1⟩ id solcFreePtrMem
  have rd4601 := rd4600pre.keccak256 0 base (UInt256.ofNat 3)
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
  have rd4604pre := evm_run rd4601 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd4604pre
  obtain ⟨k4605, C4605, rd4605raw⟩ := rd4604pre.sload (by native_decide) (by evm_ov)
  have rd4605 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4605⟩
      [flapperSlotWord (auctionPackedSlot id) σ I, id, ⟨360⟩, sel]
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4605 C4605 := by
    simpa [flapperSlotWord] using rd4605raw
  have rd4614 := evm_run rd4605 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd4621 := rd4614.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4622 := rd4621.and (by native_decide) (by evm_ov)
  have rd4623 := rd4622.lt (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, flapperUint48Offset26Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩ = UInt256.ofNat (256 ^ 26)
        from by native_decide]
      using rd4623⟩

theorem flapperTickX_endNotExpired {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hendGe :
      (UInt256.ofNat I.header.timestamp).toNat ≤
        (flapperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat)
    (rd4586 : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4586⟩
      [tickIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let id := tickIdWord I
  let memMap := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  obtain ⟨_, _, rd4586'⟩ := rd4586
  obtain ⟨_, _, rd4623⟩ := flapperTickX_toEndLtGuard rd4586'
  have hendLt :
      UInt256.lt (flapperUint48Offset26Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨0⟩ := by
    apply ult_zero
    simpa [id] using hendGe
  have rd4626 := rd4623.push2 ⟨4694⟩ (by native_decide) (by evm_ov)
  have rd4627raw := rd4626.jumpiNT (by native_decide) hendLt (by evm_ov)
  have hpc4627 : (⟨4623⟩ : UInt256) + UInt256.ofNat 3 + ⟨1⟩ = ⟨4627⟩ := by
    native_decide
  rw [hpc4627] at rd4627raw
  exact RD.solcErrorStringRevertTail
    (pc := ⟨4627⟩)
    (len := ⟨20⟩)
    (rawWord := ⟨0x119b185c1c195c8bdb9bdd0b599a5b9a5cda1959⟩)
    (shift := ⟨98⟩)
    (word := ⟨0x466c61707065722f6e6f742d66696e6973686564000000000000000000000000⟩)
    (op := .PUSH20)
    (width := 20)
    rd4627raw
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
theorem flapperTickX_toTicZeroGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hendLt :
      (flapperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (rd4586 : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4586⟩
      [tickIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tickIdWord I
    let memEnd := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memTic := twoWordHashMem id ⟨1⟩ memEnd
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4729⟩
      [UInt256.isZero (flapperUint48Offset20Word (auctionPackedSlot id) σ I),
        id, ⟨360⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memEnd memTic
  obtain ⟨_, _, rd4586'⟩ := rd4586
  obtain ⟨_, _, rd4623⟩ := flapperTickX_toEndLtGuard rd4586'
  have hendLtWord :
      UInt256.lt (flapperUint48Offset26Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨1⟩ := by
    apply ult_one
    simpa [id] using hendLt
  have rd4626 := rd4623.push2 ⟨4694⟩ (by native_decide) (by evm_ov)
  have rd4694 := rd4626.jumpiT (by native_decide)
    (by rw [hendLtWord]; exact one_ne_zero_uint) (by jump_dest) (by evm_ov)
  let memKey := wordAt0Mem id memEnd
  let base := solcMappingSlot ⟨1⟩ id
  have rd4699pre := evm_run rd4694 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd4700 := rd4699pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, memEnd, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd4704pre := evm_run rd4700 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd4705 := rd4704pre.mstore 0 memTic (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memTic, memEnd, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd4708pre := evm_run rd4705 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memTic.readWithPadding 0 64))) = base := by
    simpa [base, memTic, memEnd, id] using
      Benchmarks.Dss.Flopper.twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memEnd
  have rd4709 := rd4708pre.keccak256 0 base (UInt256.ofNat 3)
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
  have rd4712pre := evm_run rd4709 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd4712pre
  obtain ⟨k4713, C4713, rd4713raw⟩ := rd4712pre.sload (by native_decide) (by evm_ov)
  have rd4713 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4713⟩
      [flapperSlotWord (auctionPackedSlot id) σ I, id, ⟨360⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4713 C4713 := by
    simpa [flapperSlotWord] using rd4713raw
  have rd4720 := evm_run rd4713 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd4727 := rd4720.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4728 := rd4727.and (by native_decide) (by evm_ov)
  have rd4729 := rd4728.iszero (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, flapperUint48Offset20Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = UInt256.ofNat (256 ^ 20)
        from by native_decide]
      using rd4729⟩

theorem flapperTickX_ticNonzero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hendLt :
      (flapperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ I ≠ ⟨0⟩)
    (rd4586 : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4586⟩
      [tickIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let id := tickIdWord I
  let memEnd := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memEnd
  obtain ⟨_, _, rd4729⟩ := flapperTickX_toTicZeroGuard hendLt rd4586
  have hcond :
      UInt256.isZero (flapperUint48Offset20Word (auctionPackedSlot id) σ I) = ⟨0⟩ := by
    exact isZero_eq_zero_of_ne (by simpa [id] using htic)
  have rd4732 := rd4729.push2 ⟨4809⟩ (by native_decide) (by evm_ov)
  have rd4733raw := rd4732.jumpiNT (by native_decide) hcond (by evm_ov)
  have hpc4733 : (⟨4729⟩ : UInt256) + UInt256.ofNat 3 + ⟨1⟩ = ⟨4733⟩ := by
    native_decide
  rw [hpc4733] at rd4733raw
  have hmemEnd : memEnd.size = 96 := by
    simpa [memEnd, id] using
      twoWordHashMem_size_96 (tickIdWord I) ⟨1⟩ solcFreePtrMem_size
  have hreadEnd : memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memEnd, id] using
      twoWordHashMem_read64 (tickIdWord I) ⟨1⟩ solcFreePtrMem_size
        solcFreePtrMem_read64
  exact Benchmarks.Dss.Flopper.solcErrorStringRevertTailFullWord
    (pc := ⟨4733⟩)
    (len := ⟨26⟩)
    (word :=
      ⟨0x466c61707065722f6269642d616c72656164792d706c61636564000000000000⟩)
    rd4733raw
    (by
      unfold Benchmarks.Dss.Flopper.solcErrorStringRevertTailFullWordWf
      repeat' first | apply And.intro | native_decide)
    (by
      simpa [memTic, id] using
        twoWordHashMem_size_96 (tickIdWord I) ⟨1⟩ hmemEnd)
    (by
      simpa [memTic, id] using
        twoWordHashMem_read64 (tickIdWord I) ⟨1⟩ hmemEnd hreadEnd)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem flapperTickX_toCheckedAddStart
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hendLt :
      (flapperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ I = ⟨0⟩)
    (rd4586 : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4586⟩
      [tickIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tickIdWord I
    let memEnd := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memTic := twoWordHashMem id ⟨1⟩ memEnd
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4936⟩
      [tickRuntimeTauWord σ I, UInt256.ofNat I.header.timestamp, ⟨4838⟩,
        id, ⟨360⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memEnd memTic
  obtain ⟨_, _, rd4729⟩ := flapperTickX_toTicZeroGuard hendLt rd4586
  have hcond :
      UInt256.isZero (flapperUint48Offset20Word (auctionPackedSlot id) σ I) ≠ ⟨0⟩ := by
    rw [show flapperUint48Offset20Word (auctionPackedSlot id) σ I =
      flapperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ I from rfl, htic]
    decide
  have rd4732 := rd4729.push2 ⟨4809⟩ (by native_decide) (by evm_ov)
  have rd4809 := rd4732.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
  have rd4812 := rd4809.jumpdest (by native_decide) (by evm_ov)
  have rd4813 := rd4812.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨k4813, C4813, rd4813raw⟩ := rd4813.sload (by native_decide) (by evm_ov)
  have rd4813' : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4813⟩
      [flapperSlotWord ⟨5⟩ σ I, id, ⟨360⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4813 C4813 := by
    simpa [flapperSlotWord, id] using rd4813raw
  have rd4825 := evm_run rd4813' with [
    raw push2 ⟨4838⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw timestamp (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨48⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd4833 := rd4825.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4834 := rd4833.and (by native_decide) (by evm_ov)
  have rd4837 := rd4834.push2 ⟨4936⟩ (by native_decide) (by evm_ov)
  have rd4936 := rd4837.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, tickRuntimeTauWord, flapperUint48Offset6Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨48⟩ = UInt256.ofNat (256 ^ 6)
        from by native_decide]
      using rd4936⟩

set_option maxHeartbeats 1000000 in
theorem flapperTickX_toEndStoreStart
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hendLt :
      (flapperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ I = ⟨0⟩)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
        (tickRuntimeTauWord σ I).toNat < 2 ^ 48)
    (rd4586 : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4586⟩
      [tickIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tickIdWord I
    let memEnd := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memTic := twoWordHashMem id ⟨1⟩ memEnd
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4838⟩
      [tickRuntimeAddWord σ I, id, ⟨360⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memEnd memTic
  obtain ⟨_, _, rd4936⟩ :=
    flapperTickX_toCheckedAddStart hendLt htic rd4586
  let tau := tickRuntimeTauWord σ I
  let timestamp := UInt256.ofNat I.header.timestamp
  let addWord := tickRuntimeAddWord σ I
  have rd4940 := evm_run rd4936 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have rd4947 := rd4940.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4958 := evm_run rd4947 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨4930⟩ (by native_decide) (by evm_ov)]
  have hltFalse :
      UInt256.lt (UInt256.land (timestamp + tau) flapperUint48Mask)
          (UInt256.land timestamp flapperUint48Mask) = ⟨0⟩ := by
    simpa [timestamp, tau] using uint48AddGuard_false_of_no_wrap timestamp tau haddFit
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.land (timestamp + tau) flapperUint48Mask)
            (UInt256.land timestamp flapperUint48Mask)) ≠ ⟨0⟩ := by
    rw [hltFalse]
    decide
  have rd4930 := rd4958.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
  have rd4935 := evm_run rd4930 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd4838 := rd4935.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa [timestamp, tau, addWord, tickRuntimeAddWord] using rd4838⟩

set_option maxHeartbeats 1000000 in
theorem flapperTickX_addOverflow
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hendLt :
      (flapperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ I = ⟨0⟩)
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
        (tickRuntimeTauWord σ I).toNat)
    (rd4586 : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4586⟩
      [tickIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4936⟩ :=
    flapperTickX_toCheckedAddStart hendLt htic rd4586
  let tau := tickRuntimeTauWord σ I
  let timestamp := UInt256.ofNat I.header.timestamp
  have rd4940 := evm_run rd4936 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have rd4947 := rd4940.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4958 := evm_run rd4947 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨4930⟩ (by native_decide) (by evm_ov)]
  have htauLt : tau.toNat < 2 ^ 48 := by
    simpa [tau, tickRuntimeTauWord, flapperUint48Offset6Word, EVM.twoPow,
      u256_land_comm] using
      flapperUint48Masked_lt
        (UInt256.div (flapperSlotWord ⟨5⟩ σ I) (UInt256.ofNat (256 ^ 6)))
  have hltTrue :
      UInt256.lt (UInt256.land (timestamp + tau) flapperUint48Mask)
          (UInt256.land timestamp flapperUint48Mask) = ⟨1⟩ := by
    simpa [timestamp, tau] using
      uint48AddGuard_true_of_wrap timestamp tau htauLt haddOverflow
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.land (timestamp + tau) flapperUint48Mask)
            (UInt256.land timestamp flapperUint48Mask)) = ⟨0⟩ := by
    rw [hltTrue]
    native_decide
  have rd4959 := rd4958.jumpiNT (by native_decide) hcond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd4959
    (by native_decide) (by native_decide) (by native_decide)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem flapperTickX_success
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hendLt :
      (flapperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ I = ⟨0⟩)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
        (tickRuntimeTauWord σ I).toNat < 2 ^ 48)
    (rd4586 : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4586⟩
      [tickIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, tickRuntimeSuccessAccountMap I.codeOwner σ I) ByteArray.empty := by
  let id := tickIdWord I
  let memEnd := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memEnd
  let memEndStore := twoWordHashMem id ⟨1⟩ memTic
  let addWord := tickRuntimeAddWord σ I
  let base := solcMappingSlot ⟨1⟩ id
  let packedSlot := auctionPackedSlot id
  let oldPacked := solcSlotWord σ I packedSlot
  obtain ⟨_, _, rd4838⟩ :=
    flapperTickX_toEndStoreStart hendLt htic haddFit rd4586
  let memKey := wordAt0Mem id memTic
  have rd4843pre := evm_run rd4838 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd4844 := rd4843pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, memTic, memEnd, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd4848pre := evm_run rd4844 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd4849 := rd4848pre.mstore 0 memEndStore (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memEndStore, memTic, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd4853pre := evm_run rd4849 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memEndStore.readWithPadding 0 64))) = base := by
    simpa [base, memEndStore, memTic, id] using
      Benchmarks.Dss.Flopper.twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memTic
  have rd4854 := rd4853pre.keccak256 0 base (UInt256.ofNat 3)
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
  have rd4857pre := evm_run rd4854 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hpackedSlot : (⟨2⟩ : UInt256) + base = packedSlot := by
    rw [u256_add_comm]
    simp [packedSlot, base, auctionPackedSlot_eq, id]
  rw [hpackedSlot] at rd4857pre
  obtain ⟨k4859, C4859, rd4859raw⟩ := rd4857pre.sload (by native_decide) (by evm_ov)
  have rd4859 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4859⟩
      [oldPacked, packedSlot, addWord, ⟨360⟩, sel]
      memEndStore (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4859 C4859 := by
    simpa [oldPacked, packedSlot, solcSlotWord, addWord] using rd4859raw
  have rd4866 := rd4859.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4892pre := evm_run rd4866 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k4893, C4893, rd4893raw⟩ := rd4892pre.sstore hperm
    (by native_decide) (by evm_ov)
  have rd360 := rd4893raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd361 := rd360.jumpdest (by native_decide) (by evm_ov)
  simpa [tickRuntimeSuccessAccountMap, oldPacked, packedSlot, addWord,
    tickRuntimeEndStoredRawWord, tickRuntimeEndShiftedWord, tickRuntimeEndClearMask, id]
    using RD.stop rd361 (by native_decide) (by evm_ov)

theorem tickRuntimeSuccessAccountMap_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
        (tickRuntimeTauWord σ_evm I).toNat < 2 ^ 48) :
    accountMapEquiv (tickRuntimeSuccessAccountMap I.codeOwner σ_evm I)
      (tickPostState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I).accountMap := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (tickIdWord I)
  let runtimeOld := solcSlotWord σ_evm I packedSlot
  let runtimeAdd := tickRuntimeAddWord σ_evm I
  have htau : tickRuntimeTauWord σ_evm I = tickTauWord evmSolm := by
    have h := flapperUint48Offset6Word_accountMapEquiv (I := I) hAccounts ⟨5⟩
    simpa [evmSolm, tickRuntimeTauWord, tickTauWord, initState] using h
  have haddFitSolm :
      (tickNow48Word evmSolm).toNat + (tickTauWord evmSolm).toNat < 2 ^ 48 := by
    simpa [evmSolm, tickNow48Word, tickTimestampWord, initState, htau] using haddFit
  have hmaskedRuntime :
      UInt256.land runtimeAdd flapperUint48Mask = tickEndPostWord evmSolm := by
    apply u256_inj
    change (UInt256.land (tickRuntimeAddWord σ_evm I) flapperUint48Mask).toNat =
      (tickEndPostWord evmSolm).toNat
    rw [tickRuntimeAddWord]
    rw [uint48Mask_add_no_wrap_toNat (UInt256.ofNat I.header.timestamp)
      (tickRuntimeTauWord σ_evm I) haddFit]
    rw [tickEndPostWord_toNat evmSolm haddFitSolm]
    simpa [evmSolm, tickNow48Word, tickTimestampWord, initState, htau]
  have hsourceClean :
      UInt256.land (tickEndPostWord evmSolm) flapperUint48Mask =
        tickEndPostWord evmSolm := by
    apply flapperUint48Mask_clean_of_canonical
    have hendNat := tickEndPostWord_toNat evmSolm haddFitSolm
    rw [hendNat]
    simpa [EVM.twoPow] using haddFitSolm
  have hold :
      runtimeOld =
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner packedSlot := by
    have hslot := flapperSlotWord_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [runtimeOld, packedSlot, flapperSlotWord, solcSlotWord, evmSolm, initState]
      using hslot
  have hstored :
      tickRuntimeEndStoredRawWord runtimeOld runtimeAdd = tickEndStoredWord evmSolm I := by
    rw [tickRuntimeEndStoredRawWord_eq_setUint48Offset26Word]
    unfold tickEndStoredWord
    apply u256_inj
    rw [setUint48Offset26Word_toNat, setUint48Offset26Word_toNat]
    rw [hold, hmaskedRuntime, hsourceClean]
  simpa [evmSolm, initState, storageStore_accountMap, packedSlot, runtimeOld, runtimeAdd,
    tickRuntimeSuccessAccountMap, tickPostState, hstored] using
    accountMapEquiv_sstoreAccountMap I.codeOwner packedSlot (tickEndStoredWord evmSolm I)
      hAccounts

theorem flapperTickBodyCoreEndNotExpired
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hendGe :
      (UInt256.ofNat I.header.timestamp).toNat ≤
        (flapperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ_evm I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some tickTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tickTransition.params.map Param.name)
        (transitionSignature tickTransition).paramTypes I.calldata = some (tickLocals I))
    (rd4586 : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4586⟩
      [tickIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hendGeSolm :
      (tickTimestampWord evmSolm).toNat ≤ (tickEndWord evmSolm I).toNat := by
    have hword := flapperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    simpa [evmSolm, tickTimestampWord, tickEndWord, initState, hword] using hendGe
  have hbody :
      ExecTransitionBody config contract evmSolm (tickLocals I) tickTransition.body
        .reverted := by
    exact flapperTickBodyReverts_endNotExpired evmSolm I
      (by simpa [evmSolm, initState] using hwv) hendGeSolm
  exact (flapperTickX_endNotExpired (g := Sat256.ofUInt256 g) hendGe rd4586)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperTickBodyCoreTicNonzero
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hendLt :
      (flapperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some tickTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tickTransition.params.map Param.name)
        (transitionSignature tickTransition).paramTypes I.calldata = some (tickLocals I))
    (rd4586 : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4586⟩
      [tickIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hendLtSolm :
      (tickEndWord evmSolm I).toNat < (tickTimestampWord evmSolm).toNat := by
    have hword := flapperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    simpa [evmSolm, tickEndWord, tickTimestampWord, initState, hword] using hendLt
  have hticSolm : tickTicWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply htic
    have hword := flapperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    rw [hword]
    simpa [evmSolm, tickTicWord, initState] using hzero
  have hbody :
      ExecTransitionBody config contract evmSolm (tickLocals I) tickTransition.body
        .reverted := by
    exact flapperTickBodyReverts_ticNonzero evmSolm I
      (by simpa [evmSolm, initState] using hwv) hendLtSolm hticSolm
  exact (flapperTickX_ticNonzero (g := Sat256.ofUInt256 g) hendLt htic rd4586)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperTickBodyCoreAddOverflow
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hendLt :
      (flapperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ_evm I = ⟨0⟩)
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
        (tickRuntimeTauWord σ_evm I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some tickTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tickTransition.params.map Param.name)
        (transitionSignature tickTransition).paramTypes I.calldata = some (tickLocals I))
    (rd4586 : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4586⟩
      [tickIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hendLtSolm :
      (tickEndWord evmSolm I).toNat < (tickTimestampWord evmSolm).toNat := by
    have hword := flapperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    simpa [evmSolm, tickEndWord, tickTimestampWord, initState, hword] using hendLt
  have hticSolm : tickTicWord evmSolm I = ⟨0⟩ := by
    have hword := flapperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    simpa [evmSolm, tickTicWord, initState, hword] using htic
  have htau : tickRuntimeTauWord σ_evm I = tickTauWord evmSolm := by
    have h := flapperUint48Offset6Word_accountMapEquiv (I := I) hAccounts ⟨5⟩
    simpa [evmSolm, tickRuntimeTauWord, tickTauWord, initState] using h
  have haddOverflowSolm :
      2 ^ 48 ≤ (tickNow48Word evmSolm).toNat + (tickTauWord evmSolm).toNat := by
    simpa [evmSolm, tickNow48Word, tickTimestampWord, initState, htau]
      using haddOverflow
  have hbody :
      ExecTransitionBody config contract evmSolm (tickLocals I) tickTransition.body
        .reverted := by
    exact flapperTickBodyReverts_addOverflow evmSolm I
      (by simpa [evmSolm, initState] using hwv) hendLtSolm hticSolm
      haddOverflowSolm
  exact (flapperTickX_addOverflow (g := Sat256.ofUInt256 g) hendLt htic
      haddOverflow rd4586)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperTickBodyCoreSuccess
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hendLt :
      (flapperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ_evm I = ⟨0⟩)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
        (tickRuntimeTauWord σ_evm I).toNat < 2 ^ 48)
    (hdispatch : dispatchMsg contract I.calldata = some tickTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tickTransition.params.map Param.name)
        (transitionSignature tickTransition).paramTypes I.calldata = some (tickLocals I))
    (rd4586 : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4586⟩
      [tickIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hendLtSolm :
      (tickEndWord evmSolm I).toNat < (tickTimestampWord evmSolm).toNat := by
    have hword := flapperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    simpa [evmSolm, tickEndWord, tickTimestampWord, initState, hword] using hendLt
  have hticSolm : tickTicWord evmSolm I = ⟨0⟩ := by
    have hword := flapperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    simpa [evmSolm, tickTicWord, initState, hword] using htic
  have htau : tickRuntimeTauWord σ_evm I = tickTauWord evmSolm := by
    have h := flapperUint48Offset6Word_accountMapEquiv (I := I) hAccounts ⟨5⟩
    simpa [evmSolm, tickRuntimeTauWord, tickTauWord, initState] using h
  have haddFitSolm :
      (tickNow48Word evmSolm).toNat + (tickTauWord evmSolm).toNat < 2 ^ 48 := by
    simpa [evmSolm, tickNow48Word, tickTimestampWord, initState, htau] using haddFit
  have hbody :
      ExecTransitionBody config contract evmSolm (tickLocals I) tickTransition.body
        (.returned { contract := contract, locals := tickEndLocals evmSolm I }
          (tickPostState evmSolm I) none) := by
    exact flapperTickBodyReturns_success evmSolm I
      (by simpa [evmSolm, initState] using hwv) hendLtSolm hticSolm haddFitSolm
  have hret := flapperTickX_success (g := Sat256.ofUInt256 g) hperm hendLt htic
    haddFit rd4586
  have hpostAccounts :=
    tickRuntimeSuccessAccountMap_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts haddFit
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by
      simp [evmSolm, tickPostState, initState, storageStore_createdAccounts])
    (by simpa [evmSolm] using hpostAccounts)
    (by
      simpa [tickTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flapperTickBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some tickTransition)
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨855⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (flapperTickX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch
      (flapperDecode_tick_none_short hsz4 hshort)

theorem flapperTickBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 15))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flapperSelBytes 15) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some tickTransition :=
    flapperDispatchTick hsel
  have hreach := flapperReachTickBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have rd4586 := flapperTickX_decoded (g := Sat256.ofUInt256 g)
      hsz36 hsize hreach
    let id := tickIdWord I
    let packedSlot := auctionPackedSlot id
    by_cases hendLt :
        (flapperUint48Offset26Word packedSlot σ_evm I).toNat <
          (UInt256.ofNat I.header.timestamp).toNat
    · by_cases htic : flapperUint48Offset20Word packedSlot σ_evm I = ⟨0⟩
      · by_cases haddFit :
          (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
            (tickRuntimeTauWord σ_evm I).toNat < 2 ^ 48
        · exact flapperTickBodyCoreSuccess hcode hperm hwv
            (by simpa [id, packedSlot] using hendLt)
            (by simpa [id, packedSlot] using htic)
            haddFit hdispatch (flapperDecode_tick_ok hsz36) rd4586 hAccounts
        · exact flapperTickBodyCoreAddOverflow hcode hwv
            (by simpa [id, packedSlot] using hendLt)
            (by simpa [id, packedSlot] using htic)
            (Nat.le_of_not_gt haddFit) hdispatch
            (flapperDecode_tick_ok hsz36) rd4586 hAccounts
      · exact flapperTickBodyCoreTicNonzero hcode hwv
          (by simpa [id, packedSlot] using hendLt)
          (by simpa [id, packedSlot] using htic) hdispatch
          (flapperDecode_tick_ok hsz36) rd4586 hAccounts
    · exact flapperTickBodyCoreEndNotExpired hcode hwv
        (by simpa [id, packedSlot] using Nat.le_of_not_gt hendLt) hdispatch
        (flapperDecode_tick_ok hsz36) rd4586 hAccounts
  · exact flapperTickBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Flapper
