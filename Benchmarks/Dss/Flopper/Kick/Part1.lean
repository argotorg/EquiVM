import Benchmarks.Dss.Flopper.Rely
import Benchmarks.Dss.Flopper.Tick

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper

/-! ## `kick(address,uint256,uint256)` -/

abbrev kickGalWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev kickGalMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (kickGalWord I)

abbrev kickLotWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev kickBidWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev kickGalValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (kickGalWord I).toNat)

abbrev kickLotValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (kickLotWord I).toNat)

abbrev kickBidValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (kickBidWord I).toNat)

abbrev kickLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "gal" (kickGalValue I)).insert "lot" (kickLotValue I)).insert "bid"
    (kickBidValue I)

abbrev kickKicksWord (evm : EVM.State) : UInt256 :=
  flopperSlotWord ⟨7⟩ evm.accountMap evm.executionEnv

abbrev kickLiveWord (evm : EVM.State) : UInt256 :=
  flopperSlotWord ⟨8⟩ evm.accountMap evm.executionEnv

abbrev kickIdWord (evm : EVM.State) : UInt256 :=
  kickKicksWord evm + ⟨1⟩

abbrev kickIdValue (evm : EVM.State) : Value :=
  .int (Int.ofNat (kickIdWord evm).toNat)

abbrev kickIdLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (kickLocals I).insert "id" (kickIdValue evm)

abbrev kickTauWord (evm : EVM.State) : UInt256 :=
  flopperUint48Offset6Word ⟨6⟩ evm.accountMap evm.executionEnv

abbrev kickTimestampWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp

abbrev kickNow48Word (evm : EVM.State) : UInt256 :=
  UInt256.land (kickTimestampWord evm) flopperUint48Mask

def kickAfterKicksState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨7⟩ (kickIdWord evm)

def kickAfterBidState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (kickAfterKicksState evm)
    (kickAfterKicksState evm).executionEnv.codeOwner (auctionBidSlot (kickIdWord evm))
    (kickBidWord I)

def kickAfterLotState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (kickAfterBidState evm I)
    (kickAfterBidState evm I).executionEnv.codeOwner (auctionLotSlot (kickIdWord evm))
    (kickLotWord I)

def kickGuyStoredWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  setAddressOffset0Word
    (Solm.EVM.storageLoad (kickAfterLotState evm I)
      (kickAfterLotState evm I).executionEnv.codeOwner (auctionPackedSlot (kickIdWord evm)))
    (kickGalMaskedWord I)

def kickAfterGuyState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (kickAfterLotState evm I)
    (kickAfterLotState evm I).executionEnv.codeOwner (auctionPackedSlot (kickIdWord evm))
    (kickGuyStoredWord evm I)

abbrev kickEndPostWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat)

abbrev kickEndLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (kickIdLocals evm I).insert "end_" (.int (Int.ofNat (kickEndPostWord evm I).toNat))

abbrev kickEndWrappedNat (evm : EVM.State) (I : ExecutionEnv) : Nat :=
  ((kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat) % 2 ^ 48

abbrev kickEndWrappedLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (kickIdLocals evm I).insert "end_" (.int (Int.ofNat (kickEndWrappedNat evm I)))

def kickEndStoredWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  setUint48Offset26Word
    (Solm.EVM.storageLoad (kickAfterGuyState evm I)
      (kickAfterGuyState evm I).executionEnv.codeOwner (auctionPackedSlot (kickIdWord evm)))
    (kickEndPostWord evm I)

def kickPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (kickAfterGuyState evm I)
    (kickAfterGuyState evm I).executionEnv.codeOwner (auctionPackedSlot (kickIdWord evm))
    (kickEndStoredWord evm I)

abbrev kickRuntimeIdWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flopperSlotWord ⟨7⟩ σ I + ⟨1⟩

def kickRuntimeAfterKicksMap (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap owner σ ⟨7⟩ (kickRuntimeIdWord σ I)

def kickRuntimeAfterBidMap (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap owner (kickRuntimeAfterKicksMap owner σ I)
    (auctionBidSlot (kickRuntimeIdWord σ I)) (kickBidWord I)

def kickRuntimeAfterLotMap (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap owner (kickRuntimeAfterBidMap owner σ I)
    (auctionLotSlot (kickRuntimeIdWord σ I)) (kickLotWord I)

def kickRuntimeGuyStoredWord (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : UInt256 :=
  setAddressOffset0Word
    (solcSlotWord (kickRuntimeAfterLotMap owner σ I) I
      (auctionPackedSlot (kickRuntimeIdWord σ I)))
    (kickGalMaskedWord I)

def kickRuntimeAfterGuyMap (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap owner (kickRuntimeAfterLotMap owner σ I)
    (auctionPackedSlot (kickRuntimeIdWord σ I)) (kickRuntimeGuyStoredWord owner σ I)

abbrev kickRuntimeTauWord (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : UInt256 :=
  flopperUint48Offset6Word ⟨6⟩ (kickRuntimeAfterGuyMap owner σ I) I

abbrev kickRuntimeAddWord (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp + kickRuntimeTauWord owner σ I

def kickRuntimeEndStoredWord (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : UInt256 :=
  setUint48Offset26Word
    (solcSlotWord (kickRuntimeAfterGuyMap owner σ I) I
      (auctionPackedSlot (kickRuntimeIdWord σ I)))
    (kickRuntimeAddWord owner σ I)

def kickRuntimeSuccessAccountMap (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap owner (kickRuntimeAfterGuyMap owner σ I)
    (auctionPackedSlot (kickRuntimeIdWord σ I)) (kickRuntimeEndStoredWord owner σ I)

theorem kickLocals_get_gal (I : ExecutionEnv) :
    (kickLocals I).get? "gal" = some (kickGalValue I) := by
  unfold kickLocals
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem kickLocals_get_lot (I : ExecutionEnv) :
    (kickLocals I).get? "lot" = some (kickLotValue I) := by
  unfold kickLocals
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem kickLocals_get_bid (I : ExecutionEnv) :
    (kickLocals I).get? "bid" = some (kickBidValue I) := by
  simp [kickLocals]

theorem kickLocals_get_wards (I : ExecutionEnv) :
    (kickLocals I).get? "wards" = none := by
  simp [kickLocals]

theorem kickIdLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (kickIdLocals evm I).get? "id" = some (kickIdValue evm) := by
  simp [kickIdLocals]

theorem kickIdLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) :
    (kickIdLocals evm I).get? "bids" = none := by
  simp [kickIdLocals, kickLocals]

theorem kickEndLocals_get_end (evm : EVM.State) (I : ExecutionEnv) :
    (kickEndLocals evm I).get? "end_" =
      some (.int (Int.ofNat (kickEndPostWord evm I).toNat)) := by
  simp [kickEndLocals]

theorem kickEndLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (kickEndLocals evm I).get? "id" = some (kickIdValue evm) := by
  unfold kickEndLocals
  rw [store_get_ne _ _ (by native_decide)]
  exact kickIdLocals_get_id evm I

theorem kickEndLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) :
    (kickEndLocals evm I).get? "bids" = none := by
  unfold kickEndLocals
  rw [store_get_ne _ _ (by native_decide)]
  exact kickIdLocals_get_bids evm I

theorem kickEndWrappedLocals_get_end (evm : EVM.State) (I : ExecutionEnv) :
    (kickEndWrappedLocals evm I).get? "end_" =
      some (.int (Int.ofNat (kickEndWrappedNat evm I))) := by
  simp [kickEndWrappedLocals]

theorem kickAfterKicksState_executionEnv (evm : EVM.State) :
    (kickAfterKicksState evm).executionEnv = evm.executionEnv := by
  simpa [kickAfterKicksState] using
    storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨7⟩ (kickIdWord evm)

theorem kickAfterBidState_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (kickAfterBidState evm I).executionEnv = evm.executionEnv := by
  calc
    (kickAfterBidState evm I).executionEnv = (kickAfterKicksState evm).executionEnv := by
      simpa [kickAfterBidState] using
        storageStore_executionEnv (kickAfterKicksState evm)
          (kickAfterKicksState evm).executionEnv.codeOwner
          (auctionBidSlot (kickIdWord evm)) (kickBidWord I)
    _ = evm.executionEnv := kickAfterKicksState_executionEnv evm

theorem kickAfterLotState_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (kickAfterLotState evm I).executionEnv = evm.executionEnv := by
  calc
    (kickAfterLotState evm I).executionEnv = (kickAfterBidState evm I).executionEnv := by
      simpa [kickAfterLotState] using
        storageStore_executionEnv (kickAfterBidState evm I)
          (kickAfterBidState evm I).executionEnv.codeOwner
          (auctionLotSlot (kickIdWord evm)) (kickLotWord I)
    _ = evm.executionEnv := kickAfterBidState_executionEnv evm I

theorem kickAfterGuyState_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (kickAfterGuyState evm I).executionEnv = evm.executionEnv := by
  calc
    (kickAfterGuyState evm I).executionEnv = (kickAfterLotState evm I).executionEnv := by
      simpa [kickAfterGuyState] using
        storageStore_executionEnv (kickAfterLotState evm I)
          (kickAfterLotState evm I).executionEnv.codeOwner
          (auctionPackedSlot (kickIdWord evm)) (kickGuyStoredWord evm I)
    _ = evm.executionEnv := kickAfterLotState_executionEnv evm I

theorem kickTauWord_lt (evm : EVM.State) :
    (kickTauWord evm).toNat < 2 ^ 48 := by
  rw [kickTauWord, flopperUint48Offset6Word]
  rw [u256_land_comm flopperUint48Mask
    (UInt256.div (flopperSlotWord ⟨6⟩ evm.accountMap evm.executionEnv)
      (UInt256.ofNat (256 ^ 6)))]
  simpa [EVM.twoPow] using
    flopperUint48Masked_lt
      (UInt256.div (flopperSlotWord ⟨6⟩ evm.accountMap evm.executionEnv)
        (UInt256.ofNat (256 ^ 6)))

theorem kickIdWord_toNat (evm : EVM.State)
    (hkicksLt : (kickKicksWord evm).toNat < UInt256.size - 1) :
    (kickIdWord evm).toNat = (kickKicksWord evm).toNat + 1 := by
  unfold kickIdWord
  rw [uadd_toNat]
  have hsum : (kickKicksWord evm).toNat + 1 < UInt256.size := by omega
  simpa using Nat.mod_eq_of_lt hsum

theorem kickEndPostWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat <
        2 ^ 48) :
    (kickEndPostWord evm I).toNat =
      (kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat := by
  unfold kickEndPostWord
  exact UInt256.toNat_ofNat_of_lt (lt_trans hfit (by norm_num [UInt256.size]))

theorem evalExpr_kick_live_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickLocals I } evm (.storage liveRef) =
      .ok (.int (Int.ofNat (kickLiveWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := kickLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := liveRef) (er := ({ base := "live", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨8⟩)
    (value := .int (Int.ofNat (kickLiveWord evm).toNat))
    (by simp [frame, liveRef, kickLocals])
    (by simp [frame, evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [kickLiveWord, flopperSlotWord] using flopperStorageLocLoad_uint256 evm ⟨8⟩)

theorem evalExpr_kick_live_one_true (evm : EVM.State) (I : ExecutionEnv)
    (hlive : kickLiveWord evm = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := kickLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := kickLocals I } evm (.storage liveRef) =
        .ok (.int 1) := by
    simpa [hlive] using evalExpr_kick_live_storage evm I
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_kick_live_one_false (evm : EVM.State) (I : ExecutionEnv)
    (hlive : kickLiveWord evm ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := kickLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  have hstorage := evalExpr_kick_live_storage evm I
  have hne :
      Value.int (Int.ofNat (kickLiveWord evm).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    exact hlive (uint256_toNat_eq_one (Int.ofNat.inj hbad))
  have hbeq :
      (Value.int (Int.ofNat (kickLiveWord evm).toNat) == Value.int 1) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_kick_kicks_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickLocals I } evm (.storage kicksRef) =
      .ok (.int (Int.ofNat (kickKicksWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := kickLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := kicksRef) (er := ({ base := "kicks", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨7⟩)
    (value := .int (Int.ofNat (kickKicksWord evm).toNat))
    (by simp [frame, kicksRef, kickLocals])
    (by simp [frame, evalStorageRef, evalStorageRefSteps, kicksRef, EvalResult.bind, pure, bind])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [kickKicksWord, flopperSlotWord] using flopperStorageLocLoad_uint256 evm ⟨7⟩)

theorem evalExpr_kick_kicks_lt_max_true (evm : EVM.State) (I : ExecutionEnv)
    (hkicksLt : (kickKicksWord evm).toNat < UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := kickLocals I } evm
      (.binary .lt (.storage kicksRef) (.intLit maxUint256)) = .ok (.bool true) := by
  have hkicks := evalExpr_kick_kicks_storage evm I
  simp only [evalExpr?, hkicks, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hlt :
      Int.ofNat (kickKicksWord evm).toNat < maxUint256 := by
    have hmax : maxUint256 = Int.ofNat (UInt256.size - 1) := by native_decide
    rw [hmax]
    exact Int.ofNat_lt.mpr hkicksLt
  simpa using hlt

theorem evalExpr_kick_kicks_lt_max_false (evm : EVM.State) (I : ExecutionEnv)
    (hkicksGe : UInt256.size - 1 ≤ (kickKicksWord evm).toNat) :
    evalExpr? config { contract := contract, locals := kickLocals I } evm
      (.binary .lt (.storage kicksRef) (.intLit maxUint256)) = .ok (.bool false) := by
  have hkicks := evalExpr_kick_kicks_storage evm I
  simp only [evalExpr?, hkicks, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hnlt :
      ¬ Int.ofNat (kickKicksWord evm).toNat < maxUint256 := by
    have hmax : maxUint256 = Int.ofNat (UInt256.size - 1) := by native_decide
    rw [hmax]
    exact not_lt.mpr (Int.ofNat_le.mpr hkicksGe)
  have hdec :
      decide (Int.ofNat (kickKicksWord evm).toNat < maxUint256) = false := by
    rw [decide_eq_false_iff_not]
    exact hnlt
  rw [hdec]

theorem evalExpr_kick_id_add (evm : EVM.State) (I : ExecutionEnv)
    (hkicksLt : (kickKicksWord evm).toNat < UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := kickLocals I } evm
      (.binary .add (.storage kicksRef) (.intLit 1)) =
        .ok (.int (Int.ofNat (kickIdWord evm).toNat)) := by
  have hkicks := evalExpr_kick_kicks_storage evm I
  have hidNat := kickIdWord_toNat evm hkicksLt
  simp only [evalExpr?, hkicks, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hidNat]
  norm_num

theorem evalExpr_kick_bid_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm I } evm (.var "bid") =
      .ok (.int (Int.ofNat (kickBidWord I).toNat)) := by
  rw [evalExpr?]
  unfold kickIdLocals
  rw [store_get_ne _ _ (by native_decide)]
  rw [kickLocals_get_bid]
  rfl

theorem evalExpr_kick_lot_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm I } evm (.var "lot") =
      .ok (.int (Int.ofNat (kickLotWord I).toNat)) := by
  rw [evalExpr?]
  unfold kickIdLocals
  rw [store_get_ne _ _ (by native_decide)]
  rw [kickLocals_get_lot]
  rfl

theorem evalExpr_kick_gal_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm I } evm (.var "gal") =
      .ok (kickGalValue I) := by
  rw [evalExpr?]
  unfold kickIdLocals
  rw [store_get_ne _ _ (by native_decide)]
  rw [kickLocals_get_gal]
  rfl

theorem evalExpr_kick_id_var_idLocals_at (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm0 I } evm (.var "id") =
      .ok (.int (Int.ofNat (kickIdWord evm0).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((kickIdLocals evm0 I).get? "id") =
    .ok (.int (Int.ofNat (kickIdWord evm0).toNat))
  rw [kickIdLocals_get_id]
  rfl

theorem evalExpr_kick_bid_var_at (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm0 I } evm (.var "bid") =
      .ok (.int (Int.ofNat (kickBidWord I).toNat)) := by
  rw [evalExpr?]
  unfold kickIdLocals
  rw [store_get_ne _ _ (by native_decide)]
  rw [kickLocals_get_bid]
  rfl

theorem evalExpr_kick_lot_var_at (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm0 I } evm (.var "lot") =
      .ok (.int (Int.ofNat (kickLotWord I).toNat)) := by
  rw [evalExpr?]
  unfold kickIdLocals
  rw [store_get_ne _ _ (by native_decide)]
  rw [kickLocals_get_lot]
  rfl

theorem evalExpr_kick_gal_var_at (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm0 I } evm (.var "gal") =
      .ok (kickGalValue I) := by
  rw [evalExpr?]
  unfold kickIdLocals
  rw [store_get_ne _ _ (by native_decide)]
  rw [kickLocals_get_gal]
  rfl

theorem evalExpr_kick_id_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickEndLocals evm I } evm (.var "id") =
      .ok (.int (Int.ofNat (kickIdWord evm).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((kickEndLocals evm I).get? "id") =
    .ok (.int (Int.ofNat (kickIdWord evm).toNat))
  rw [kickEndLocals_get_id]
  rfl

theorem evalExpr_kick_id_var_at (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickEndLocals evm0 I } evm (.var "id") =
      .ok (.int (Int.ofNat (kickIdWord evm0).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((kickEndLocals evm0 I).get? "id") =
    .ok (.int (Int.ofNat (kickIdWord evm0).toNat))
  rw [kickEndLocals_get_id]
  rfl

theorem assign_kickKicksStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := kickIdLocals evm I } evm
      .storage kicksRef (.int (Int.ofNat (kickIdWord evm).toNat)) =
        .ok ({ contract := contract, locals := kickIdLocals evm I },
          kickAfterKicksState evm) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "kicks", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨7⟩)
      (hbase := by simp [kickIdLocals, kickLocals, kicksRef])
      (her := by simp [evalStorageRef, evalStorageRefSteps, kicksRef, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [kickAfterKicksState] using storageLocStore_uint256 evm ⟨7⟩ (kickIdWord evm)

theorem assign_kickBidStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := kickIdLocals evm I }
      (kickAfterKicksState evm)
      .storage (bidsF (.var "id") "bid") (.int (Int.ofNat (kickBidWord I).toNat)) =
        .ok ({ contract := contract, locals := kickIdLocals evm I },
          kickAfterBidState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := { base := "bids", steps := [.mindex (auctionIdKey (kickIdWord evm)), .field "bid"] })
      (loc := wordLoc (auctionBidSlot (kickIdWord evm)))
      (hbase := by
        change (kickIdLocals evm I).get? "bids" = none
        exact kickIdLocals_get_bids evm I)
      (her := by
        simpa [kickIdValue] using
          evalStorageRef_auction_field (kickAfterKicksState evm) (kickIdLocals evm I)
            (kickIdWord evm) "bid" (by simpa [kickIdValue] using kickIdLocals_get_id evm I))
      (hty := by simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
      (hloc := by rfl)
  simpa [kickAfterBidState] using
    storageLocStore_uint256 (kickAfterKicksState evm) (auctionBidSlot (kickIdWord evm))
      (kickBidWord I)

theorem assign_kickLotStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := kickIdLocals evm I }
      (kickAfterBidState evm I)
      .storage (bidsF (.var "id") "lot") (.int (Int.ofNat (kickLotWord I).toNat)) =
        .ok ({ contract := contract, locals := kickIdLocals evm I },
          kickAfterLotState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := { base := "bids", steps := [.mindex (auctionIdKey (kickIdWord evm)), .field "lot"] })
      (loc := wordLoc (auctionLotSlot (kickIdWord evm)))
      (hbase := by
        change (kickIdLocals evm I).get? "bids" = none
        exact kickIdLocals_get_bids evm I)
      (her := by
        simpa [kickIdValue] using
          evalStorageRef_auction_field (kickAfterBidState evm I) (kickIdLocals evm I)
            (kickIdWord evm) "lot" (by simpa [kickIdValue] using kickIdLocals_get_id evm I))
      (hty := by simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
      (hloc := by rfl)
  simpa [kickAfterLotState] using
    storageLocStore_uint256 (kickAfterBidState evm I) (auctionLotSlot (kickIdWord evm))
      (kickLotWord I)

theorem assign_kickGuyStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := kickIdLocals evm I }
      (kickAfterLotState evm I)
      .storage (bidsF (.var "id") "guy") (kickGalValue I) =
        .ok ({ contract := contract, locals := kickIdLocals evm I },
          kickAfterGuyState evm I) := by
  have hgalValue :
      kickGalValue I =
        .address (AccountAddress.ofNat (kickGalMaskedWord I).toNat) := by
    simpa [kickGalValue, kickGalMaskedWord, u256_land_comm] using
      solcAddressValue_masked (kickGalWord I)
  rw [hgalValue]
  apply assignStorageRef_storage_scalar_value
      (ty := addrSt)
      (er := { base := "bids", steps := [.mindex (auctionIdKey (kickIdWord evm)), .field "guy"] })
      (loc := addrLoc (auctionPackedSlot (kickIdWord evm)))
      (hbase := by
        change (kickIdLocals evm I).get? "bids" = none
        exact kickIdLocals_get_bids evm I)
      (her := by
        simpa [kickIdValue] using
          evalStorageRef_auction_field (kickAfterLotState evm I) (kickIdLocals evm I)
            (kickIdWord evm) "guy" (by simpa [kickIdValue] using kickIdLocals_get_id evm I))
      (hty := by simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, addrSt])
      (hloc := by rfl)
      (hscalar := by trivial)
  simpa [kickAfterGuyState, kickGuyStoredWord, addrLoc, kickGalMaskedWord] using
    storageLocStore_address_offset0 (kickAfterLotState evm I)
      (auctionPackedSlot (kickIdWord evm)) (kickGalMaskedWord I)
      (by
        rw [kickGalMaskedWord, u256_land_comm]
        exact solcAddrMask_result_canonical (kickGalWord I))

theorem evalExpr_kick_tau_storage (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm0 I } evm
        (.storage tauRef) =
      .ok (.int (Int.ofNat (kickTauWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := kickIdLocals evm0 I }
  have hload :
      storageLocLoad evm (uint48Loc ⟨6⟩ ⟨6, by decide⟩ (by decide)) =
        .int (Int.ofNat (kickTauWord evm).toNat) := by
    rw [flopperStorageLocLoad_uint48_offset6]
    rw [u256_land_comm
      (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩)
        (UInt256.ofNat (256 ^ 6))) flopperUint48Mask]
    rfl
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := tauRef) (er := ({ base := "tau", steps := [] } : EvaledStorageRef))
    (t := .int uint48Int) (loc := uint48Loc ⟨6⟩ ⟨6, by decide⟩ (by decide))
    (value := .int (Int.ofNat (kickTauWord evm).toNat))
    (by simp [frame, tauRef, kickIdLocals, kickLocals])
    (by simp [frame, evalStorageRef, evalStorageRefSteps, tauRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint48St])
    (by rfl)
    hload

theorem evalExpr_kick_now48 (locals : Store) (evm0 evm : EVM.State)
    (henv : evm.executionEnv.header.timestamp = evm0.executionEnv.header.timestamp) :
    evalExpr? config { contract := contract, locals := locals } evm now48 =
      .ok (.int (Int.ofNat (kickNow48Word evm0).toNat)) := by
  unfold now48 wrap48
  simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hmod :
      Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat % uint48Modulus =
        Int.ofNat (kickNow48Word evm0).toNat := by
    have henvWord :
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat =
          (kickTimestampWord evm0).toNat := by
      simp [kickTimestampWord, henv]
    rw [henvWord]
    have hnow : (kickNow48Word evm0).toNat =
        (kickTimestampWord evm0).toNat % 2 ^ 48 := by
      unfold kickNow48Word
      rw [u256_land_toNat]
      change Nat.land (kickTimestampWord evm0).toNat (2 ^ 48 - 1) % UInt256.size =
        (kickTimestampWord evm0).toNat % 2 ^ 48
      rw [nat_land_mask_eq_mod]
      exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num [UInt256.size]))
    rw [hnow]
    norm_num [uint48Modulus, Int.natCast_mod]
  simpa [uint48Modulus] using hmod

theorem evalExpr_kick_endAdd_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat <
        2 ^ 48) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm I }
        (kickAfterGuyState evm I)
        (wrap48 (.binary .add now48 (.storage tauRef))) =
      .ok (.int (Int.ofNat (kickEndPostWord evm I).toNat)) := by
  have hnow := evalExpr_kick_now48 (kickIdLocals evm I) evm (kickAfterGuyState evm I)
    (by simp [kickAfterGuyState_executionEnv])
  have htau := evalExpr_kick_tau_storage evm (kickAfterGuyState evm I) I
  have hendNat := kickEndPostWord_toNat evm I hfit
  unfold wrap48
  simp only [evalExpr?, hnow, htau, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hsumMod :
      (Int.ofNat (kickNow48Word evm).toNat +
          Int.ofNat (kickTauWord (kickAfterGuyState evm I)).toNat) %
          uint48Modulus =
        Int.ofNat (kickEndPostWord evm I).toNat := by
    rw [hendNat]
    have hsumCast :
        Int.ofNat ((kickNow48Word evm).toNat +
            (kickTauWord (kickAfterGuyState evm I)).toNat) =
          Int.ofNat (kickNow48Word evm).toNat +
            Int.ofNat (kickTauWord (kickAfterGuyState evm I)).toNat := by
      norm_num
    rw [← hsumCast]
    have hfitInt :
        Int.ofNat ((kickNow48Word evm).toNat +
            (kickTauWord (kickAfterGuyState evm I)).toNat) < uint48Modulus := by
      change Int.ofNat ((kickNow48Word evm).toNat +
          (kickTauWord (kickAfterGuyState evm I)).toNat) < Int.ofNat (2 ^ 48)
      exact Int.ofNat_lt.mpr hfit
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) hfitInt
  simpa [uint48Modulus] using hsumMod

theorem evalExpr_kick_endAdd_wrapped (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm I }
        (kickAfterGuyState evm I)
        (wrap48 (.binary .add now48 (.storage tauRef))) =
      .ok (.int (Int.ofNat (kickEndWrappedNat evm I))) := by
  have hnow := evalExpr_kick_now48 (kickIdLocals evm I) evm (kickAfterGuyState evm I)
    (by simp [kickAfterGuyState_executionEnv])
  have htau := evalExpr_kick_tau_storage evm (kickAfterGuyState evm I) I
  unfold wrap48
  simp only [evalExpr?, hnow, htau, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hsumMod :
      (Int.ofNat (kickNow48Word evm).toNat +
          Int.ofNat (kickTauWord (kickAfterGuyState evm I)).toNat) %
          uint48Modulus =
        Int.ofNat (kickEndWrappedNat evm I) := by
    have hsumCast :
        Int.ofNat ((kickNow48Word evm).toNat +
            (kickTauWord (kickAfterGuyState evm I)).toNat) =
          Int.ofNat (kickNow48Word evm).toNat +
            Int.ofNat (kickTauWord (kickAfterGuyState evm I)).toNat := by
      norm_num
    rw [← hsumCast]
    norm_num [kickEndWrappedNat, uint48Modulus, Int.natCast_mod]
  simpa [uint48Modulus] using hsumMod

theorem evalExpr_kick_end_guard_true (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat <
        2 ^ 48) :
    evalExpr? config { contract := contract, locals := kickEndLocals evm I }
        (kickAfterGuyState evm I)
      (.binary .ge (.var "end_") now48) = .ok (.bool true) := by
  have hend :
      evalExpr? config { contract := contract, locals := kickEndLocals evm I }
          (kickAfterGuyState evm I) (.var "end_") =
        .ok (.int (Int.ofNat (kickEndPostWord evm I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((kickEndLocals evm I).get? "end_") =
      .ok (.int (Int.ofNat (kickEndPostWord evm I).toNat))
    rw [kickEndLocals_get_end]
    rfl
  have hnow :
      evalExpr? config { contract := contract, locals := kickEndLocals evm I }
          (kickAfterGuyState evm I) now48 =
        .ok (.int (Int.ofNat (kickNow48Word evm).toNat)) := by
    exact evalExpr_kick_now48 (kickEndLocals evm I) evm (kickAfterGuyState evm I)
      (by simp [kickAfterGuyState_executionEnv])
  have hendNat := kickEndPostWord_toNat evm I hfit
  have hge :
      Int.ofNat (kickNow48Word evm).toNat ≤
        Int.ofNat (kickEndPostWord evm I).toNat := by
    rw [hendNat]
    change Int.ofNat (kickNow48Word evm).toNat ≤
      Int.ofNat ((kickNow48Word evm).toNat +
        (kickTauWord (kickAfterGuyState evm I)).toNat)
    exact Int.ofNat_le.mpr (Nat.le_add_right _ _)
  simp only [evalExpr?, hend, hnow, EvalResult.bind, bind, evalBinaryOp?]
  simpa using hge

theorem evalExpr_kick_end_guard_false_wrapped (evm : EVM.State) (I : ExecutionEnv)
    (hoverflow :
      2 ^ 48 ≤
        (kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat) :
    evalExpr? config { contract := contract, locals := kickEndWrappedLocals evm I }
        (kickAfterGuyState evm I)
      (.binary .ge (.var "end_") now48) = .ok (.bool false) := by
  have hend :
      evalExpr? config { contract := contract, locals := kickEndWrappedLocals evm I }
          (kickAfterGuyState evm I) (.var "end_") =
        .ok (.int (Int.ofNat (kickEndWrappedNat evm I))) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((kickEndWrappedLocals evm I).get? "end_") =
      .ok (.int (Int.ofNat (kickEndWrappedNat evm I)))
    rw [kickEndWrappedLocals_get_end]
    rfl
  have hnow :
      evalExpr? config { contract := contract, locals := kickEndWrappedLocals evm I }
          (kickAfterGuyState evm I) now48 =
        .ok (.int (Int.ofNat (kickNow48Word evm).toNat)) := by
    exact evalExpr_kick_now48 (kickEndWrappedLocals evm I) evm (kickAfterGuyState evm I)
      (by simp [kickAfterGuyState_executionEnv])
  have hnowLt : (kickNow48Word evm).toNat < 2 ^ 48 := by
    unfold kickNow48Word
    simpa [flopperUint48Mask, EVM.twoPow] using flopperUint48Masked_lt (kickTimestampWord evm)
  have htauLt : (kickTauWord (kickAfterGuyState evm I)).toNat < 2 ^ 48 := by
    exact kickTauWord_lt (kickAfterGuyState evm I)
  have hwrappedLt :
      kickEndWrappedNat evm I < (kickNow48Word evm).toNat := by
    unfold kickEndWrappedNat
    have hsumLt :
        (kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat <
          2 ^ 49 := by
      omega
    rw [Nat.mod_eq_sub_mod hoverflow]
    have hsubLt :
        (kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat -
            2 ^ 48 < 2 ^ 48 := by
      omega
    rw [Nat.mod_eq_of_lt hsubLt]
    omega
  have hdec :
      decide
          (Int.ofNat (kickNow48Word evm).toNat ≤
            Int.ofNat (kickEndWrappedNat evm I)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    exact (Nat.not_lt.mpr (Int.ofNat_le.mp hle)) hwrappedLt
  simp only [evalExpr?, hend, hnow, EvalResult.bind, bind, evalBinaryOp?]
  rw [hdec]

theorem assign_kickEndStorage_value (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat <
        2 ^ 48) :
    assignStorageRef? config { contract := contract, locals := kickEndLocals evm I }
      (kickAfterGuyState evm I)
      .storage (bidsF (.var "id") "end")
      (.int (Int.ofNat (kickEndPostWord evm I).toNat)) =
        .ok ({ contract := contract, locals := kickEndLocals evm I },
          kickPostState evm I) := by
  have hmod :
      Int.ofNat (kickEndPostWord evm I).toNat % uint48Modulus =
        Int.ofNat (kickEndPostWord evm I).toNat := by
    have hendNat := kickEndPostWord_toNat evm I hfit
    have hendLt : (kickEndPostWord evm I).toNat < 2 ^ 48 := by omega
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
      (by
        change Int.ofNat (kickEndPostWord evm I).toNat < Int.ofNat (2 ^ 48)
        exact Int.ofNat_lt.mpr hendLt)
  apply assignStorageRef_storage_scalar
      (ty := uint48St)
      (er := { base := "bids", steps := [.mindex (auctionIdKey (kickIdWord evm)), .field "end"] })
      (loc := uint48Loc (auctionPackedSlot (kickIdWord evm)) ⟨26, by decide⟩ (by decide))
      (hbase := by
        change (kickEndLocals evm I).get? "bids" = none
        exact kickEndLocals_get_bids evm I)
      (her := by
        simpa [kickIdValue] using
          evalStorageRef_auction_field (kickAfterGuyState evm I) (kickEndLocals evm I)
            (kickIdWord evm) "end" (by simpa [kickIdValue] using kickEndLocals_get_id evm I))
      (hty := by simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint48St])
      (hloc := by rfl)
  rw [← hmod]
  simpa [kickPostState, kickEndStoredWord] using
    storageLocStore_uint48_offset26_word (kickAfterGuyState evm I)
      (auctionPackedSlot (kickIdWord evm)) (kickEndPostWord evm I)

theorem evalExpr_kick_end_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickEndLocals evm I }
        (kickAfterGuyState evm I) (.var "end_") =
      .ok (.int (Int.ofNat (kickEndPostWord evm I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((kickEndLocals evm I).get? "end_") =
    .ok (.int (Int.ofNat (kickEndPostWord evm I).toNat))
  rw [kickEndLocals_get_end]
  rfl

theorem flopperKickBodyReverts_unauthorized (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (kickLocals I) kickTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [kickTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := kickLocals I })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest :=
        [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)),
          .letDecl "id" (some uint256) (.binary .add (.storage kicksRef) (.intLit 1)),
          .assign .storage kicksRef (.var "id"),
          .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
          .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
          .assign .storage (bidsF (.var "id") "guy") (.var "gal") ] ++
        checkedAdd48Into "end_" now48 (.storage tauRef) ++
        [ .assign .storage (bidsF (.var "id") "end") (.var "end_"),
          .return [.var "id"] ])
      hwv
      (evalExpr_auth_false_of_wards_none evm I (kickLocals I) (kickLocals_get_wards I)
        hsrc hauth)

theorem flopperKickBodyReverts_notLive (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hlive : kickLiveWord evm ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (kickLocals I) kickTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [kickTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (evalExpr_auth_true_of_wards_none evm I (kickLocals I) (kickLocals_get_wards I)
            hsrc hauth)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_kick_live_one_false evm I hlive)))

theorem flopperKickBodyReverts_kicksOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hlive : kickLiveWord evm = ⟨1⟩)
    (hkicksGe : UInt256.size - 1 ≤ (kickKicksWord evm).toNat) :
    ExecTransitionBody config contract evm (kickLocals I) kickTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [kickTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (evalExpr_auth_true_of_wards_none evm I (kickLocals I) (kickLocals_get_wards I)
            hsrc hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_live_one_true evm I hlive)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_kick_kicks_lt_max_false evm I hkicksGe)))

theorem flopperKickBodyReverts_addOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hlive : kickLiveWord evm = ⟨1⟩)
    (hkicksLt : (kickKicksWord evm).toNat < UInt256.size - 1)
    (haddOverflow :
      2 ^ 48 ≤
        (kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat) :
    ExecTransitionBody config contract evm (kickLocals I) kickTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [kickTransition, nonpayable, auth, checkedAdd48Into, List.cons_append, List.nil_append]
    using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (evalExpr_auth_true_of_wards_none evm I (kickLocals I) (kickLocals_get_wards I)
            hsrc hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_kicks_lt_max_true evm I hkicksLt)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_kick_id_add evm I hkicksLt)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_id_var_idLocals_at evm evm I)
          (assign_kickKicksStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_bid_var_at evm (kickAfterKicksState evm) I)
          (assign_kickBidStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_lot_var_at evm (kickAfterBidState evm I) I)
          (assign_kickLotStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_gal_var_at evm (kickAfterLotState evm I) I)
          (assign_kickGuyStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_kick_endAdd_wrapped evm I)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse
          (evalExpr_kick_end_guard_false_wrapped evm I haddOverflow)))

theorem flopperKickBodyReturns_success (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hlive : kickLiveWord evm = ⟨1⟩)
    (hkicksLt : (kickKicksWord evm).toNat < UInt256.size - 1)
    (haddFit :
      (kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat <
        2 ^ 48) :
    ExecTransitionBody config contract evm (kickLocals I) kickTransition.body
      (.returned { contract := contract, locals := kickEndLocals evm I }
        (kickPostState evm I) (some [.int (Int.ofNat (kickIdWord evm).toNat)])) := by
  have hreturns :
      evalExprs? config { contract := contract, locals := kickEndLocals evm I }
          (kickPostState evm I) [.var "id"] =
        .ok [.int (Int.ofNat (kickIdWord evm).toNat)] := by
    simp [evalExprs?, evalExpr_kick_id_var_at evm (kickPostState evm I) I,
      EvalResult.bind, bind, pure]
  refine ExecFuncBody.execBlockRet ?_
  simpa [kickTransition, nonpayable, auth, checkedAdd48Into, List.cons_append, List.nil_append]
    using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (evalExpr_auth_true_of_wards_none evm I (kickLocals I) (kickLocals_get_wards I)
            hsrc hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_kicks_lt_max_true evm I hkicksLt)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_kick_id_add evm I hkicksLt)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_id_var_idLocals_at evm evm I)
          (assign_kickKicksStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_bid_var_at evm (kickAfterKicksState evm) I)
          (assign_kickBidStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_lot_var_at evm (kickAfterBidState evm I) I)
          (assign_kickLotStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_gal_var_at evm (kickAfterLotState evm I) I)
          (assign_kickGuyStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_kick_endAdd_ok evm I haddFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_end_guard_true evm I haddFit)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_end_var evm I)
          (assign_kickEndStorage_value evm I haddFit)) <|
      ExecBlock.consReturn (ExecStmt.return hreturns))

theorem flopperDecode_kick_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (kickTransition.params.map Param.name)
      (transitionSignature kickTransition).paramTypes I.calldata = some (kickLocals I) := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["gal", "lot", "bid"]
      [abiAddress, abiUInt256, abiUInt256] I.calldata =
    some ((((∅ : Store).insert "gal" (kickGalValue I)).insert "lot" (kickLotValue I)).insert
      "bid" (kickBidValue I))
  exact decodeCalldata_legacyAddress_uint256_uint256_ok (cd := I.calldata)
    (x := "gal") (y := "lot") (z := "bid") hsz100

theorem flopperDecode_kick_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (kickTransition.params.map Param.name)
      (transitionSignature kickTransition).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["gal", "lot", "bid"]
      [abiAddress, abiUInt256, abiUInt256] I.calldata = none
  exact decodeCalldata_legacyAddress_uint256_uint256_none_short (cd := I.calldata)
    (x := "gal") (y := "lot") (z := "bid") hsz4 hshort

theorem flopperReachKickBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flopperSelBytes 8)) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨716⟩ [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flopperSelWord I = ⟨0xb7e9cd24⟩ := by
    simpa [flopperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0xb7 0xe9 0xcd 0x24 ⟨0xb7e9cd24⟩
        (by native_decide) (by simpa [flopperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flopperBytecode flopperHighSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flopperReachHighLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have heq0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighLowFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighLowFirstArmPc 4))
        (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨716⟩ 4 hfirst
    (fun j hj => flopperHighLowArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flopperKickX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨716⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3401⟩
      [kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flopperBytecode) (sel := sel) (entry := ⟨716⟩) (ret := ⟨644⟩)
    (decoded := ⟨738⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize)
  have rd739 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd740 := rd739.pop (by native_decide) (by evm_ov)
  have rd742 := rd740.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd744 := rd742.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd746 := rd744.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd747 := rd746.shl (by native_decide) (by evm_ov)
  have rd748 := rd747.sub (by native_decide) (by evm_ov)
  have rd749 := rd748.dup2 (by native_decide) (by evm_ov)
  have rd750 := rd749.calldataload (by native_decide) (by evm_ov)
  have rd751 := rd750.and (by native_decide) (by evm_ov)
  have rd752 := rd751.swap1 (by native_decide) (by evm_ov)
  have rd754 := rd752.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd755 := rd754.dup2 (by native_decide) (by evm_ov)
  have rd756 := rd755.add (by native_decide) (by evm_ov)
  have rd757 := rd756.calldataload (by native_decide) (by evm_ov)
  have rd758 := rd757.swap1 (by native_decide) (by evm_ov)
  have rd760 := rd758.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd761 := rd760.add (by native_decide) (by evm_ov)
  have rd762 := rd761.calldataload (by native_decide) (by evm_ov)
  have rd765 := rd762.push2 ⟨3401⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [kickGalMaskedWord, kickGalWord, kickLotWord, kickBidWord, calldataWord,
      solcAddrMask, u256_land_comm,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨64⟩).toNat = 68 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd765.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flopperKickX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨716⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flopperBytecode) (sel := sel) (entry := ⟨716⟩) (ret := ⟨644⟩)
    (decoded := ⟨738⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem flopperKickX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD flopperBytecode I g s0 ⟨3401⟩
      [kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flopperBytecode I g s0 ⟨3494⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd3407pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3408 := rd3407pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3412pre := evm_run rd3408 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3413 := rd3412pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3416pre := evm_run rd3413 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3417 := rd3416pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k3418, C3418, rd3418raw⟩ := rd3417.sload (by native_decide) (by evm_ov)
  have rd3418 : RD flopperBytecode I g s0 ⟨3418⟩
      (relyAuthWord σ I :: ⟨0⟩ :: kickBidWord I :: kickLotWord I ::
        kickGalMaskedWord I :: ⟨644⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3418 C3418 := by
    simpa [relyAuthWord, flopperSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using
      rd3418raw
  have rd3421pre := evm_run rd3418 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd3421pre
  have rd3424 := rd3421pre.pushConst (⟨3494⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd3424.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flopperKickX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD flopperBytecode I g s0 ⟨3401⟩
      [kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd3407pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3408 := rd3407pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3412pre := evm_run rd3408 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3413 := rd3412pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3416pre := evm_run rd3413 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3417 := rd3416pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k3418, C3418, rd3418raw⟩ := rd3417.sload (by native_decide) (by evm_ov)
  have rd3418 : RD flopperBytecode I g s0 ⟨3418⟩
      (relyAuthWord σ I :: ⟨0⟩ :: kickBidWord I :: kickLotWord I ::
        kickGalMaskedWord I :: ⟨644⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3418 C3418 := by
    simpa [relyAuthWord, flopperSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using
      rd3418raw
  have rd3421pre := evm_run rd3418 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd3421pre
  have rd3424 := rd3421pre.pushConst (⟨3494⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd3425 := rd3424.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3425⟩)
    (len := ⟨22⟩)
    (rawWord := ⟨0x119b1bdc1c195c8bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨82⟩)
    (word := ⟨0x466c6f707065722f6e6f742d617574686f72697a656400000000000000000000⟩)
    (op := .PUSH22)
    (width := 22)
    rd3425
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem flopperKickX_liveOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (h : RD flopperBytecode I g s0 ⟨3494⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flopperBytecode I g s0 ⟨3568⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3497 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3498, C3498, rd3498raw⟩ := rd3497.sload (by native_decide) (by evm_ov)
  have rd3498 : RD flopperBytecode I g s0 ⟨3498⟩
      (flopperSlotWord ⟨8⟩ σ I :: ⟨0⟩ :: kickBidWord I :: kickLotWord I ::
        kickGalMaskedWord I :: ⟨644⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3498 C3498 := by
    simpa [flopperSlotWord] using rd3498raw
  have rd3501pre := evm_run rd3498 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hlive, u256_eq_refl] at rd3501pre
  have rd3504 := rd3501pre.pushConst (⟨3568⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd3504.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

theorem flopperKickX_notLive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : flopperSlotWord ⟨8⟩ σ I ≠ ⟨1⟩)
    (h : RD flopperBytecode I g s0 ⟨3494⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g s0 := by
  have rd3497 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3498, C3498, rd3498raw⟩ := rd3497.sload (by native_decide) (by evm_ov)
  have rd3498 : RD flopperBytecode I g s0 ⟨3498⟩
      (flopperSlotWord ⟨8⟩ σ I :: ⟨0⟩ :: kickBidWord I :: kickLotWord I ::
        kickGalMaskedWord I :: ⟨644⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3498 C3498 := by
    simpa [flopperSlotWord] using rd3498raw
  have rd3501pre := evm_run rd3498 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (flopperSlotWord ⟨8⟩ σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hlive hbad.symm)
  rw [heq] at rd3501pre
  have rd3504 := rd3501pre.pushConst (⟨3568⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd3505 := rd3504.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3505⟩)
    (len := ⟨16⟩)
    (rawWord := ⟨93608988021471041252676107097747322469⟩)
    (shift := ⟨128⟩)
    (word := ⟨0x466c6f707065722f6e6f742d6c69766500000000000000000000000000000000⟩)
    (op := .PUSH16)
    (width := 16)
    rd3505
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem flopperKickX_kicksOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hkicksLt : (flopperSlotWord ⟨7⟩ σ I).toNat < UInt256.size - 1)
    (h : RD flopperBytecode I g s0 ⟨3568⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flopperBytecode I g s0 ⟨3643⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3574pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3575, C3575, rd3575raw⟩ := rd3574pre.sload (by native_decide) (by evm_ov)
  have rd3575 : RD flopperBytecode I g s0 ⟨3575⟩
      (flopperSlotWord ⟨7⟩ σ I :: UInt256.lnot ⟨0⟩ :: ⟨0⟩ :: kickBidWord I ::
        kickLotWord I :: kickGalMaskedWord I :: ⟨644⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3575 C3575 := by
    simpa [flopperSlotWord] using rd3575raw
  have rd3576 := rd3575.lt (by native_decide) (by evm_ov)
  have hlt :
      UInt256.lt (flopperSlotWord ⟨7⟩ σ I) (UInt256.lnot ⟨0⟩) = ⟨1⟩ := by
    apply ult_one
    rw [show (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 from by native_decide]
    exact hkicksLt
  rw [hlt] at rd3576
  have rd3579 := rd3576.pushConst (⟨3643⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd3579.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

theorem flopperKickX_kicksOverflow {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hkicksGe : UInt256.size - 1 ≤ (flopperSlotWord ⟨7⟩ σ I).toNat)
    (h : RD flopperBytecode I g s0 ⟨3568⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g s0 := by
  have rd3574pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3575, C3575, rd3575raw⟩ := rd3574pre.sload (by native_decide) (by evm_ov)
  have rd3575 : RD flopperBytecode I g s0 ⟨3575⟩
      (flopperSlotWord ⟨7⟩ σ I :: UInt256.lnot ⟨0⟩ :: ⟨0⟩ :: kickBidWord I ::
        kickLotWord I :: kickGalMaskedWord I :: ⟨644⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3575 C3575 := by
    simpa [flopperSlotWord] using rd3575raw
  have rd3576 := rd3575.lt (by native_decide) (by evm_ov)
  have hlt :
      UInt256.lt (flopperSlotWord ⟨7⟩ σ I) (UInt256.lnot ⟨0⟩) = ⟨0⟩ := by
    apply ult_zero
    rw [show (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 from by native_decide]
    exact hkicksGe
  rw [hlt] at rd3576
  have rd3579 := rd3576.pushConst (⟨3643⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd3580 := rd3579.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3580⟩)
    (len := ⟨16⟩)
    (rawWord := ⟨93608988021471041252750118820200083319⟩)
    (shift := ⟨128⟩)
    (word := ⟨0x466c6f707065722f6f766572666c6f7700000000000000000000000000000000⟩)
    (op := .PUSH16)
    (width := 16)
    rd3580
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem flopperKickX_toCheckedAddStart {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD flopperBytecode I g s0 ⟨3643⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := kickRuntimeIdWord σ I
    let memStore := twoWordHashMem id ⟨1⟩ (relyAuthHashMem I)
    let σGuy := kickRuntimeAfterGuyMap I.codeOwner σ I
    ∃ k' C', RD flopperBytecode I g s0 ⟨4740⟩
      [kickRuntimeTauWord I.codeOwner σ I, UInt256.ofNat I.header.timestamp, ⟨3737⟩,
        id, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty (cA, σGuy) k' C' := by
  intro id memStore σGuy
  let σKicks := kickRuntimeAfterKicksMap I.codeOwner σ I
  let σBid := kickRuntimeAfterBidMap I.codeOwner σ I
  let σLot := kickRuntimeAfterLotMap I.codeOwner σ I
  let base := solcMappingSlot ⟨1⟩ id
  let packedSlot := auctionPackedSlot id
  let oldPacked := solcSlotWord σLot I packedSlot
  let guyStored := kickRuntimeGuyStoredWord I.codeOwner σ I
  have rd3648pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k3649, C3649, rd3649raw⟩ := rd3648pre.sload (by native_decide) (by evm_ov)
  have rd3649 : RD flopperBytecode I g s0 ⟨3649⟩
      [flopperSlotWord ⟨7⟩ σ I, ⟨7⟩, kickBidWord I, kickLotWord I,
        kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3649 C3649 := by
    simpa [flopperSlotWord] using rd3649raw
  have rd3657pre := evm_run rd3649 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k3658, C3658, rd3658raw⟩ := rd3657pre.sstore hperm
    (by native_decide) (by evm_ov)
  have hidRaw : ⟨1⟩ + flopperSlotWord ⟨7⟩ σ I = id := by
    rw [u256_add_comm]
  have hidRawSolc : ⟨1⟩ + solcSlotWord σ I ⟨7⟩ = id := by
    simpa [flopperSlotWord] using hidRaw
  have rd3658 : RD flopperBytecode I g s0 ⟨3658⟩
      [⟨1⟩, id, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σKicks) k3658 C3658 := by
    simpa [id, σKicks, kickRuntimeAfterKicksMap, kickRuntimeIdWord, flopperSlotWord,
      hidRawSolc]
      using rd3658raw
  let memKey := wordAt0Mem id (relyAuthHashMem I)
  have rd3661pre := evm_run rd3658 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3662 := rd3661pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd3667pre := evm_run rd3662 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3668 := rd3667pre.mstore 0 memStore (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memStore, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd3671pre := evm_run rd3668 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memStore.readWithPadding 0 64))) = base := by
    simpa [base, memStore, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id (relyAuthHashMem I)
  have rd3672 := rd3671pre.keccak256 0 base (UInt256.ofNat 3)
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
  have hbidSlot : base = auctionBidSlot id := by
    simp [base, auctionBidSlot, auctionBaseSlot_eq, id]
  rw [hbidSlot] at rd3672
  have rd3674pre := evm_run rd3672 with [
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  obtain ⟨k3675, C3675, rd3675raw⟩ := rd3674pre.sstore hperm
    (by native_decide) (by evm_ov)
  have rd3675 : RD flopperBytecode I g s0 ⟨3675⟩
      [auctionBidSlot id, ⟨1⟩, id, kickBidWord I, kickLotWord I, kickGalMaskedWord I,
        ⟨644⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty (cA, σBid) k3675 C3675 := by
    simpa [σBid, kickRuntimeAfterBidMap, σKicks, kickRuntimeAfterKicksMap, id]
      using rd3675raw
  have rd3680pre := evm_run rd3675 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hlotSlot : auctionBidSlot id + ⟨1⟩ = auctionLotSlot id := by
    simp [auctionLotSlot, auctionBidSlot]
  rw [hlotSlot] at rd3680pre
  obtain ⟨k3681, C3681, rd3681raw⟩ := rd3680pre.sstore hperm
    (by native_decide) (by evm_ov)
  have rd3681 : RD flopperBytecode I g s0 ⟨3681⟩
      [auctionBidSlot id, id, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty (cA, σLot) k3681 C3681 := by
    simpa [σLot, kickRuntimeAfterLotMap, σBid, kickRuntimeAfterBidMap, id]
      using rd3681raw
  have rd3684pre := evm_run rd3681 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpackedSlot : ⟨2⟩ + auctionBidSlot id = packedSlot := by
    rw [u256_add_comm]
  rw [hpackedSlot] at rd3684pre
  have rd3685 := rd3684pre.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k3686, C3686, rd3686raw⟩ := rd3685.sload (by native_decide) (by evm_ov)
  have rd3686 : RD flopperBytecode I g s0 ⟨3686⟩
      [oldPacked, packedSlot, id, kickBidWord I, kickLotWord I, kickGalMaskedWord I,
        ⟨644⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty (cA, σLot) k3686 C3686 := by
    simpa [oldPacked, solcSlotWord, packedSlot] using rd3686raw
  have rd3708pre := evm_run rd3686 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k3709, C3709, rd3709raw⟩ := rd3708pre.sstore hperm
    (by native_decide) (by evm_ov)
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    native_decide
  have hword :
      UInt256.lor (UInt256.land (kickGalMaskedWord I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) oldPacked) =
        guyStored := by
    calc
      UInt256.lor (UInt256.land (kickGalMaskedWord I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) oldPacked) =
          UInt256.lor (UInt256.land (kickGalMaskedWord I) solcAddrMask)
            (UInt256.land oldPacked (UInt256.lnot solcAddrMask)) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) oldPacked]
      _ = UInt256.lor (UInt256.land oldPacked (UInt256.lnot solcAddrMask))
            (UInt256.land (kickGalMaskedWord I) solcAddrMask) := by
            exact u256_lor_comm _ _
      _ = guyStored := by
            rfl
  have rd3709 : RD flopperBytecode I g s0 ⟨3709⟩
      [id, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty (cA, σGuy) k3709 C3709 := by
    simpa [σGuy, kickRuntimeAfterGuyMap, guyStored, kickRuntimeGuyStoredWord,
      oldPacked, packedSlot, σLot, hmask, hword, setAddressOffset0Word] using
      rd3709raw
  have rd3711 := rd3709.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨k3712, C3712, rd3712raw⟩ := rd3711.sload (by native_decide) (by evm_ov)
  have rd3712 : RD flopperBytecode I g s0 ⟨3712⟩
      [flopperSlotWord ⟨6⟩ σGuy I, id, kickBidWord I, kickLotWord I, kickGalMaskedWord I,
        ⟨644⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty (cA, σGuy) k3712 C3712 := by
    simpa [flopperSlotWord] using rd3712raw
  have rd3724 := evm_run rd3712 with [
    raw push2 ⟨3737⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw timestamp (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨48⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd3732 := rd3724.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd3733 := rd3732.and (by native_decide) (by evm_ov)
  have rd3736 := rd3733.push2 ⟨4740⟩ (by native_decide) (by evm_ov)
  have rd4740 := rd3736.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, memStore, σGuy, kickRuntimeTauWord, flopperUint48Offset6Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨48⟩ = UInt256.ofNat (256 ^ 6)
        from by native_decide]
      using rd4740⟩

theorem kickRuntimeTauWord_lt (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) :
    (kickRuntimeTauWord owner σ I).toNat < 2 ^ 48 := by
  rw [kickRuntimeTauWord, flopperUint48Offset6Word]
  rw [u256_land_comm flopperUint48Mask
    (UInt256.div (flopperSlotWord ⟨6⟩ (kickRuntimeAfterGuyMap owner σ I) I)
      (UInt256.ofNat (256 ^ 6)))]
  simpa [EVM.twoPow] using
    flopperUint48Masked_lt
      (UInt256.div (flopperSlotWord ⟨6⟩ (kickRuntimeAfterGuyMap owner σ I) I)
        (UInt256.ofNat (256 ^ 6)))

def stLog2 (s : State) (a b c d : UInt256) (t : List UInt256) : State :=
  {s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG2)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

theorem log2_xstep {s : State} {code : ByteArray} {pcv a b c d : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG2, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat
            < memoryExpansionCost s .LOG2
              + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
                + 2 * GasConstants.Glogtopic)
         then .error .OutOfGass else .ok (stLog2 s a b c d t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG2, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_log2 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: t).length - 4 + 0 > 1024) := by
    simp only [List.length_cons]
    omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, stLog2]

theorem RD.log2 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG2, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: t →
        memoryExpansionCost s .LOG2 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 2 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc,
      hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG2 = mcost := hmc s haw hstk
    have hperms : s.executionEnv.perm = true := by
      rw [hee]
      exact hperm
    have st := log2_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stLog2 s a b c d t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stLog2]
        exact hcode
      · simp only [stLog2]
        rw [hpc]
      · simp only [stLog2]
      · simp only [stLog2, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stLog2]
        exact hmem
      · simp only [stLog2]
        rw [haw, hawout]
      · simp only [stLog2]
        exact hrdata
      · simp only [stLog2]
        exact hacc
      · simp only [stLog2]
        exact hee
      · simp only [stLog2]
        exact hworld

noncomputable abbrev kickEventMem (mem : ByteArray) (id lot bid : UInt256) : ByteArray :=
  writeCascade mem [(128, id), (160, lot), (192, bid)]

theorem kickEventMem_size {mem : ByteArray} (id lot bid : UInt256) (hmem : mem.size = 96) :
    (kickEventMem mem id lot bid).size = 224 := by
  exact writeCascade_size_of_base mem [(128, id), (160, lot), (192, bid)]
    hmem (by simp [WriteGapsOk]; all_goals exact lt_usize _ (by norm_num)) (by rfl)

theorem kickEventMem_read64 {mem : ByteArray} (id lot bid : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (kickEventMem mem id lot bid).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold kickEventMem
  rw [writeCascade_read_preserved_of_base mem _ hmem
    (by simp [WindowDisjointFromWrites]; all_goals exact lt_usize _ (by norm_num))]
  exact hread64

theorem kickEventMem_mload64 {mem : ByteArray} (id lot bid : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (kickEventMem mem id lot bid).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((kickEventMem mem id lot bid).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [kickEventMem_size id lot bid hmem]; decide) (by decide)
    (kickEventMem_read64 id lot bid hmem hread64)

theorem kickEventReturnMem_mload64 {mem : ByteArray} (id lot bid : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥
          ((UInt256.toByteArray id).write 0 (kickEventMem mem id lot bid) 128 32).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        (((UInt256.toByteArray id).write 0 (kickEventMem mem id lot bid) 128 32).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  apply mloadFreePtrValue
  · rw [toByteArray_write32_size_of_le (kickEventMem mem id lot bid) id 128 224 224
      (kickEventMem_size id lot bid hmem)]
    · decide
    · rw [kickEventMem_size id lot bid hmem]
      omega
    · rfl
  · decide
  · rw [toByteArray_write_read_below_of_gap id (kickEventMem mem id lot bid) 128 64
      (by rw [kickEventMem_size id lot bid hmem]; omega)
      (by omega)
      (by rw [kickEventMem_size id lot bid hmem]; exact lt_usize _ (by norm_num))]
    exact kickEventMem_read64 id lot bid hmem hread64

theorem kickEventReturnMem_read128 {mem : ByteArray} (id lot bid : UInt256)
    (hmem : mem.size = 96) :
    ((UInt256.toByteArray id).write 0 (kickEventMem mem id lot bid) 128 32).readWithPadding
        128 32 =
      UInt256.toByteArray id := by
  exact toByteArray_write32_read_back (kickEventMem mem id lot bid) id 128
    (by rw [kickEventMem_size id lot bid hmem]; omega)

end Benchmarks.Dss.Flopper
