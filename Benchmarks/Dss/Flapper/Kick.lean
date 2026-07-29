import Benchmarks.Dss.Flapper.Tick
import Benchmarks.Dss.Flopper.Kick.Part1

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace Benchmarks.Dss.Flapper

/-! ## `kick(uint256,uint256)` -/

abbrev kickLotWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev kickBidWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev kickLotValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (kickLotWord I).toNat)

abbrev kickBidValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (kickBidWord I).toNat)

abbrev kickLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "lot" (kickLotValue I)).insert "bid" (kickBidValue I)

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
  unfold kickLocals
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  simp

abbrev kickKicksWord (evm : EVM.State) : UInt256 :=
  flapperSlotWord ⟨6⟩ evm.accountMap evm.executionEnv

abbrev kickLiveWord (evm : EVM.State) : UInt256 :=
  flapperSlotWord ⟨7⟩ evm.accountMap evm.executionEnv

abbrev kickLidWord (evm : EVM.State) : UInt256 :=
  flapperSlotWord ⟨8⟩ evm.accountMap evm.executionEnv

abbrev kickFillWord (evm : EVM.State) : UInt256 :=
  flapperSlotWord ⟨9⟩ evm.accountMap evm.executionEnv

abbrev kickFillNewWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  kickFillWord evm + kickLotWord I

abbrev kickIdWord (evm : EVM.State) : UInt256 :=
  kickKicksWord evm + ⟨1⟩

abbrev kickIdValue (evm : EVM.State) : Value :=
  .int (Int.ofNat (kickIdWord evm).toNat)

abbrev kickFillNewValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (kickFillNewWord evm I).toNat)

abbrev kickFillLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (kickLocals I).insert "fillNew" (kickFillNewValue evm I)

abbrev kickIdLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (kickFillLocals evm I).insert "id" (kickIdValue evm)

abbrev kickSenderWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev kickThisWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.codeOwner.val

def kickAfterFillState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨9⟩ (kickFillNewWord evm I)

def kickAfterKicksState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (kickAfterFillState evm I)
    (kickAfterFillState evm I).executionEnv.codeOwner ⟨6⟩ (kickIdWord evm)

def kickAfterBidState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (kickAfterKicksState evm I)
    (kickAfterKicksState evm I).executionEnv.codeOwner (auctionBidSlot (kickIdWord evm))
    (kickBidWord I)

def kickAfterLotState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (kickAfterBidState evm I)
    (kickAfterBidState evm I).executionEnv.codeOwner (auctionLotSlot (kickIdWord evm))
    (kickLotWord I)

def kickGuyStoredWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  setAddressOffset0Word
    (Solm.EVM.storageLoad (kickAfterLotState evm I)
      (kickAfterLotState evm I).executionEnv.codeOwner (auctionPackedSlot (kickIdWord evm)))
    (kickSenderWord I)

def kickAfterGuyState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (kickAfterLotState evm I)
    (kickAfterLotState evm I).executionEnv.codeOwner (auctionPackedSlot (kickIdWord evm))
    (kickGuyStoredWord evm I)

abbrev kickTauWord (evm : EVM.State) : UInt256 :=
  flapperUint48Offset6Word ⟨5⟩ evm.accountMap evm.executionEnv

abbrev kickTimestampWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp

abbrev kickNow48Word (evm : EVM.State) : UInt256 :=
  UInt256.land (kickTimestampWord evm) flapperUint48Mask

abbrev kickEndPostWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat)

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

def kickAfterEndState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (kickAfterGuyState evm I)
    (kickAfterGuyState evm I).executionEnv.codeOwner (auctionPackedSlot (kickIdWord evm))
    (kickEndStoredWord evm I)

abbrev kickMoveLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (kickEndLocals evm I).insert "_moveRet" (collapseReturns [])

abbrev kickVatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperAddressReturnWord ⟨2⟩ σ I

def kickRuntimeAfterFillMap (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap owner σ ⟨9⟩ (flapperSlotWord ⟨9⟩ σ I + kickLotWord I)

abbrev kickRuntimeIdWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperSlotWord ⟨6⟩ σ I + ⟨1⟩

def kickRuntimeAfterKicksMap (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap owner (kickRuntimeAfterFillMap owner σ I) ⟨6⟩
    (kickRuntimeIdWord σ I)

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
    (kickSenderWord I)

def kickRuntimeAfterGuyMap (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap owner (kickRuntimeAfterLotMap owner σ I)
    (auctionPackedSlot (kickRuntimeIdWord σ I)) (kickRuntimeGuyStoredWord owner σ I)

abbrev kickRuntimeTauWord (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : UInt256 :=
  flapperUint48Offset6Word ⟨5⟩ (kickRuntimeAfterGuyMap owner σ I) I

abbrev kickRuntimeAddWord (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp + kickRuntimeTauWord owner σ I

def kickRuntimeEndStoredWord (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : UInt256 :=
  setUint48Offset26Word
    (solcSlotWord (kickRuntimeAfterGuyMap owner σ I)
      I (auctionPackedSlot (kickRuntimeIdWord σ I)))
    (kickRuntimeAddWord owner σ I)

def kickRuntimeBeforeMoveMap (owner : AccountAddress) (σ : AccountMap)
    (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap owner (kickRuntimeAfterGuyMap owner σ I)
    (auctionPackedSlot (kickRuntimeIdWord σ I)) (kickRuntimeEndStoredWord owner σ I)

theorem kickFillLocals_get_fillNew (evm : EVM.State) (I : ExecutionEnv) :
    (kickFillLocals evm I).get? "fillNew" = some (kickFillNewValue evm I) := by
  simp [kickFillLocals]

theorem kickFillLocals_get_lot (evm : EVM.State) (I : ExecutionEnv) :
    (kickFillLocals evm I).get? "lot" = some (kickLotValue I) := by
  rw [kickFillLocals, store_get_ne _ _ (by native_decide)]
  exact kickLocals_get_lot I

theorem kickFillLocals_get_bid (evm : EVM.State) (I : ExecutionEnv) :
    (kickFillLocals evm I).get? "bid" = some (kickBidValue I) := by
  rw [kickFillLocals, store_get_ne _ _ (by native_decide)]
  exact kickLocals_get_bid I

theorem kickFillLocals_get_wards (evm : EVM.State) (I : ExecutionEnv) :
    (kickFillLocals evm I).get? "wards" = none := by
  rw [kickFillLocals, store_get_ne _ _ (by native_decide)]
  exact kickLocals_get_wards I

theorem kickFillLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) :
    (kickFillLocals evm I).get? "bids" = none := by
  rw [kickFillLocals, store_get_ne _ _ (by native_decide)]
  unfold kickLocals
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem kickIdLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (kickIdLocals evm I).get? "id" = some (kickIdValue evm) := by
  simp [kickIdLocals]

theorem kickIdLocals_get_fillNew (evm : EVM.State) (I : ExecutionEnv) :
    (kickIdLocals evm I).get? "fillNew" = some (kickFillNewValue evm I) := by
  rw [kickIdLocals, store_get_ne _ _ (by native_decide)]
  exact kickFillLocals_get_fillNew evm I

theorem kickIdLocals_get_lot (evm : EVM.State) (I : ExecutionEnv) :
    (kickIdLocals evm I).get? "lot" = some (kickLotValue I) := by
  rw [kickIdLocals, store_get_ne _ _ (by native_decide)]
  exact kickFillLocals_get_lot evm I

theorem kickIdLocals_get_bid (evm : EVM.State) (I : ExecutionEnv) :
    (kickIdLocals evm I).get? "bid" = some (kickBidValue I) := by
  rw [kickIdLocals, store_get_ne _ _ (by native_decide)]
  exact kickFillLocals_get_bid evm I

theorem kickIdLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) :
    (kickIdLocals evm I).get? "bids" = none := by
  rw [kickIdLocals, store_get_ne _ _ (by native_decide)]
  exact kickFillLocals_get_bids evm I

theorem kickEndLocals_get_end (evm : EVM.State) (I : ExecutionEnv) :
    (kickEndLocals evm I).get? "end_" =
      some (.int (Int.ofNat (kickEndPostWord evm I).toNat)) := by
  simp [kickEndLocals]

theorem kickEndLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (kickEndLocals evm I).get? "id" = some (kickIdValue evm) := by
  rw [kickEndLocals, store_get_ne _ _ (by native_decide)]
  exact kickIdLocals_get_id evm I

theorem kickEndLocals_get_lot (evm : EVM.State) (I : ExecutionEnv) :
    (kickEndLocals evm I).get? "lot" = some (kickLotValue I) := by
  rw [kickEndLocals, store_get_ne _ _ (by native_decide)]
  exact kickIdLocals_get_lot evm I

theorem kickEndLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) :
    (kickEndLocals evm I).get? "bids" = none := by
  rw [kickEndLocals, store_get_ne _ _ (by native_decide)]
  exact kickIdLocals_get_bids evm I

theorem kickEndWrappedLocals_get_end (evm : EVM.State) (I : ExecutionEnv) :
    (kickEndWrappedLocals evm I).get? "end_" =
      some (.int (Int.ofNat (kickEndWrappedNat evm I))) := by
  simp [kickEndWrappedLocals]

theorem kickMoveLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (kickMoveLocals evm I).get? "id" = some (kickIdValue evm) := by
  rw [kickMoveLocals, store_get_ne _ _ (by native_decide)]
  exact kickEndLocals_get_id evm I

theorem evalExpr_add256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b sum : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hsum : sum = a + b)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm (add256 x y) =
      .ok (.int (Int.ofNat sum.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat + b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : sum.toNat = a.toNat + b.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem evalExpr_add256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (add256 x y) =
      .revert := by
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem kickAfterFillState_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (kickAfterFillState evm I).executionEnv = evm.executionEnv := by
  simpa [kickAfterFillState] using
    storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨9⟩ (kickFillNewWord evm I)

theorem kickAfterKicksState_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (kickAfterKicksState evm I).executionEnv = evm.executionEnv := by
  calc
    (kickAfterKicksState evm I).executionEnv = (kickAfterFillState evm I).executionEnv := by
      simpa [kickAfterKicksState] using
        storageStore_executionEnv (kickAfterFillState evm I)
          (kickAfterFillState evm I).executionEnv.codeOwner ⟨6⟩ (kickIdWord evm)
    _ = evm.executionEnv := kickAfterFillState_executionEnv evm I

theorem kickAfterBidState_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (kickAfterBidState evm I).executionEnv = evm.executionEnv := by
  calc
    (kickAfterBidState evm I).executionEnv = (kickAfterKicksState evm I).executionEnv := by
      simpa [kickAfterBidState] using
        storageStore_executionEnv (kickAfterKicksState evm I)
          (kickAfterKicksState evm I).executionEnv.codeOwner
          (auctionBidSlot (kickIdWord evm)) (kickBidWord I)
    _ = evm.executionEnv := kickAfterKicksState_executionEnv evm I

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

theorem kickAfterEndState_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (kickAfterEndState evm I).executionEnv = evm.executionEnv := by
  calc
    (kickAfterEndState evm I).executionEnv = (kickAfterGuyState evm I).executionEnv := by
      simpa [kickAfterEndState] using
        storageStore_executionEnv (kickAfterGuyState evm I)
          (kickAfterGuyState evm I).executionEnv.codeOwner
          (auctionPackedSlot (kickIdWord evm)) (kickEndStoredWord evm I)
    _ = evm.executionEnv := kickAfterGuyState_executionEnv evm I

theorem evalExpr_kick_sender_afterLot (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm I }
        (kickAfterLotState evm I) sender =
      .ok (.address I.source) := by
  simpa [kickAfterLotState_executionEnv, hsrc] using
    evalExpr_cage_sender (kickAfterLotState evm I) (kickIdLocals evm I)

theorem kickTauWord_lt (evm : EVM.State) :
    (kickTauWord evm).toNat < 2 ^ 48 := by
  rw [kickTauWord, flapperUint48Offset6Word]
  rw [u256_land_comm flapperUint48Mask
    (UInt256.div (flapperSlotWord ⟨5⟩ evm.accountMap evm.executionEnv)
      (UInt256.ofNat (256 ^ 6)))]
  simpa [EVM.twoPow] using
    flapperUint48Masked_lt
      (UInt256.div (flapperSlotWord ⟨5⟩ evm.accountMap evm.executionEnv)
        (UInt256.ofNat (256 ^ 6)))

theorem kickNow48Word_lt (evm : EVM.State) :
    (kickNow48Word evm).toNat < 2 ^ 48 := by
  unfold kickNow48Word
  simpa [flapperUint48Mask, EVM.twoPow] using
    flapperUint48Masked_lt (kickTimestampWord evm)

theorem kickIdWord_toNat (evm : EVM.State)
    (hkicksLt : (kickKicksWord evm).toNat < UInt256.size - 1) :
    (kickIdWord evm).toNat = (kickKicksWord evm).toNat + 1 := by
  unfold kickIdWord
  rw [uadd_toNat]
  have hsum : (kickKicksWord evm).toNat + 1 < UInt256.size := by omega
  simpa using Nat.mod_eq_of_lt hsum

theorem kickFillNewWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (kickFillWord evm).toNat + (kickLotWord I).toNat < UInt256.size) :
    (kickFillNewWord evm I).toNat =
      (kickFillWord evm).toNat + (kickLotWord I).toNat := by
  unfold kickFillNewWord
  rw [uadd_toNat]
  exact Nat.mod_eq_of_lt hfit

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
    (t := .int uint256Int) (loc := wordLoc ⟨7⟩)
    (value := .int (Int.ofNat (kickLiveWord evm).toNat))
    (by simp [frame, liveRef, kickLocals])
    (by simp [frame, evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [kickLiveWord, flapperSlotWord] using flapperStorageLocLoad_uint256 evm ⟨7⟩)

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
    (t := .int uint256Int) (loc := wordLoc ⟨6⟩)
    (value := .int (Int.ofNat (kickKicksWord evm).toNat))
    (by simp [frame, kicksRef, kickLocals])
    (by simp [frame, evalStorageRef, evalStorageRefSteps, kicksRef, EvalResult.bind, pure, bind])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [kickKicksWord, flapperSlotWord] using flapperStorageLocLoad_uint256 evm ⟨6⟩)

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

theorem evalExpr_kick_fill_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickLocals I } evm (.storage fillRef) =
      .ok (.int (Int.ofNat (kickFillWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := kickLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := fillRef) (er := ({ base := "fill", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨9⟩)
    (value := .int (Int.ofNat (kickFillWord evm).toNat))
    (by simp [frame, fillRef, kickLocals])
    (by simp [frame, evalStorageRef, evalStorageRefSteps, fillRef, EvalResult.bind, pure, bind])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [kickFillWord, flapperSlotWord] using flapperStorageLocLoad_uint256 evm ⟨9⟩)

theorem evalExpr_kick_lot_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickLocals I } evm (.var "lot") =
      .ok (.int (Int.ofNat (kickLotWord I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((kickLocals I).get? "lot") =
    .ok (.int (Int.ofNat (kickLotWord I).toNat))
  rw [kickLocals_get_lot]
  rfl

theorem evalExpr_kick_bid_var_at (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm0 I } evm (.var "bid") =
      .ok (.int (Int.ofNat (kickBidWord I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((kickIdLocals evm0 I).get? "bid") =
    .ok (.int (Int.ofNat (kickBidWord I).toNat))
  rw [kickIdLocals_get_bid]
  rfl

theorem evalExpr_kick_lot_var_at (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm0 I } evm (.var "lot") =
      .ok (.int (Int.ofNat (kickLotWord I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((kickIdLocals evm0 I).get? "lot") =
    .ok (.int (Int.ofNat (kickLotWord I).toNat))
  rw [kickIdLocals_get_lot]
  rfl

theorem evalExpr_kick_fill_add_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (kickFillWord evm).toNat + (kickLotWord I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := kickLocals I } evm
        (add256 (.storage fillRef) (.var "lot")) =
      .ok (.int (Int.ofNat (kickFillNewWord evm I).toNat)) := by
  exact evalExpr_add256_ok
    (evalExpr_kick_fill_storage evm I)
    (evalExpr_kick_lot_var evm I)
    rfl hfit

theorem evalExpr_kick_fill_add_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ (kickFillWord evm).toNat + (kickLotWord I).toNat) :
    evalExpr? config { contract := contract, locals := kickLocals I } evm
        (add256 (.storage fillRef) (.var "lot")) =
      .revert := by
  exact evalExpr_add256_revert
    (evalExpr_kick_fill_storage evm I)
    (evalExpr_kick_lot_var evm I)
    hover

theorem evalExpr_kick_fillNew_var (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickFillLocals evm0 I } evm
        (.var "fillNew") =
      .ok (.int (Int.ofNat (kickFillNewWord evm0 I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((kickFillLocals evm0 I).get? "fillNew") =
    .ok (.int (Int.ofNat (kickFillNewWord evm0 I).toNat))
  rw [kickFillLocals_get_fillNew]
  rfl

theorem evalExpr_kick_fill_guard_true (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (kickFillWord evm).toNat + (kickLotWord I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := kickFillLocals evm I } evm
      (.binary .ge (.var "fillNew") (.storage fillRef)) = .ok (.bool true) := by
  let frame : Frame := { contract := contract, locals := kickFillLocals evm I }
  have hfillNew :
      evalExpr? config frame evm (.var "fillNew") =
        .ok (.int (Int.ofNat (kickFillNewWord evm I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (frame.locals.get? "fillNew") =
      .ok (.int (Int.ofNat (kickFillNewWord evm I).toNat))
    simp [frame, kickFillNewValue, EvalResult.ofOption]
  have hfill :
      evalExpr? config frame evm (.storage fillRef) =
        .ok (.int (Int.ofNat (kickFillWord evm).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := fillRef) (er := ({ base := "fill", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int) (loc := wordLoc ⟨9⟩)
      (value := .int (Int.ofNat (kickFillWord evm).toNat))
      (by simp [frame, fillRef, kickFillLocals, kickLocals])
      (by simp [frame, evalStorageRef, evalStorageRefSteps, fillRef, EvalResult.bind, pure, bind])
      (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
      (by rfl)
      (by simpa [kickFillWord, flapperSlotWord] using flapperStorageLocLoad_uint256 evm ⟨9⟩)
  have hnewNat := kickFillNewWord_toNat evm I hfit
  have hge :
      Int.ofNat (kickFillWord evm).toNat ≤
        Int.ofNat (kickFillNewWord evm I).toNat := by
    rw [hnewNat]
    exact Int.ofNat_le.mpr (Nat.le_add_right _ _)
  change evalExpr? config frame evm
      (.binary .ge (.var "fillNew") (.storage fillRef)) = .ok (.bool true)
  simp only [evalExpr?, hfillNew, hfill, EvalResult.bind, bind, evalBinaryOp?]
  simpa using hge

theorem assign_kickFillStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := kickFillLocals evm I } evm
      .storage fillRef (.int (Int.ofNat (kickFillNewWord evm I).toNat)) =
        .ok ({ contract := contract, locals := kickFillLocals evm I },
          kickAfterFillState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "fill", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨9⟩)
      (hbase := by simp [kickFillLocals, kickLocals, fillRef])
      (her := by simp [evalStorageRef, evalStorageRefSteps, fillRef, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [kickAfterFillState] using storageLocStore_uint256 evm ⟨9⟩ (kickFillNewWord evm I)

theorem evalExpr_kick_lid_storage_at_fill (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickFillLocals evm I }
        (kickAfterFillState evm I) (.storage lidRef) =
      .ok (.int (Int.ofNat (kickLidWord (kickAfterFillState evm I)).toNat)) := by
  let frame : Frame := { contract := contract, locals := kickFillLocals evm I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := kickAfterFillState evm I)
    (slot := lidRef) (er := ({ base := "lid", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨8⟩)
    (value := .int (Int.ofNat (kickLidWord (kickAfterFillState evm I)).toNat))
    (by simp [frame, lidRef, kickFillLocals, kickLocals])
    (by simp [frame, evalStorageRef, evalStorageRefSteps, lidRef, EvalResult.bind, pure, bind])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by
      simpa [kickLidWord, flapperSlotWord] using
        flapperStorageLocLoad_uint256 (kickAfterFillState evm I) ⟨8⟩)

theorem evalExpr_kick_fill_le_lid_true (evm : EVM.State) (I : ExecutionEnv)
    (hle :
      (kickFillWord (kickAfterFillState evm I)).toNat ≤
        (kickLidWord (kickAfterFillState evm I)).toNat) :
    evalExpr? config { contract := contract, locals := kickFillLocals evm I }
        (kickAfterFillState evm I)
      (.binary .le (.storage fillRef) (.storage lidRef)) = .ok (.bool true) := by
  let frame : Frame := { contract := contract, locals := kickFillLocals evm I }
  have hfill :
      evalExpr? config frame (kickAfterFillState evm I) (.storage fillRef) =
        .ok (.int (Int.ofNat (kickFillWord (kickAfterFillState evm I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := kickAfterFillState evm I)
      (slot := fillRef) (er := ({ base := "fill", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int) (loc := wordLoc ⟨9⟩)
      (value := .int (Int.ofNat (kickFillWord (kickAfterFillState evm I)).toNat))
      (by simp [frame, fillRef, kickFillLocals, kickLocals])
      (by simp [frame, evalStorageRef, evalStorageRefSteps, fillRef, EvalResult.bind, pure, bind])
      (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
      (by rfl)
      (by
        simpa [kickFillWord, flapperSlotWord] using
          flapperStorageLocLoad_uint256 (kickAfterFillState evm I) ⟨9⟩)
  have hlid0 := evalExpr_kick_lid_storage_at_fill evm I
  have hlid :
      evalExpr? config frame (kickAfterFillState evm I) (.storage lidRef) =
        .ok (.int (Int.ofNat (kickLidWord (kickAfterFillState evm I)).toNat)) := by
    simpa [frame] using hlid0
  change evalExpr? config frame (kickAfterFillState evm I)
      (.binary .le (.storage fillRef) (.storage lidRef)) = .ok (.bool true)
  rw [evalExpr?]
  simp only [hfill, hlid, EvalResult.bind, bind, evalBinaryOp?]
  simpa using (Int.ofNat_le.mpr hle)
  all_goals decide

theorem evalExpr_kick_fill_le_lid_false (evm : EVM.State) (I : ExecutionEnv)
    (hgt :
      (kickLidWord (kickAfterFillState evm I)).toNat <
        (kickFillWord (kickAfterFillState evm I)).toNat) :
    evalExpr? config { contract := contract, locals := kickFillLocals evm I }
        (kickAfterFillState evm I)
      (.binary .le (.storage fillRef) (.storage lidRef)) = .ok (.bool false) := by
  let frame : Frame := { contract := contract, locals := kickFillLocals evm I }
  have hfill :
      evalExpr? config frame (kickAfterFillState evm I) (.storage fillRef) =
        .ok (.int (Int.ofNat (kickFillWord (kickAfterFillState evm I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := kickAfterFillState evm I)
      (slot := fillRef) (er := ({ base := "fill", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int) (loc := wordLoc ⟨9⟩)
      (value := .int (Int.ofNat (kickFillWord (kickAfterFillState evm I)).toNat))
      (by simp [frame, fillRef, kickFillLocals, kickLocals])
      (by simp [frame, evalStorageRef, evalStorageRefSteps, fillRef, EvalResult.bind, pure, bind])
      (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
      (by rfl)
      (by
        simpa [kickFillWord, flapperSlotWord] using
          flapperStorageLocLoad_uint256 (kickAfterFillState evm I) ⟨9⟩)
  have hlid0 := evalExpr_kick_lid_storage_at_fill evm I
  have hlid :
      evalExpr? config frame (kickAfterFillState evm I) (.storage lidRef) =
        .ok (.int (Int.ofNat (kickLidWord (kickAfterFillState evm I)).toNat)) := by
    simpa [frame] using hlid0
  have hnle :
      ¬ Int.ofNat (kickFillWord (kickAfterFillState evm I)).toNat ≤
          Int.ofNat (kickLidWord (kickAfterFillState evm I)).toNat := by
    exact not_le.mpr (Int.ofNat_lt.mpr hgt)
  have hdec :
      decide
          (Int.ofNat (kickFillWord (kickAfterFillState evm I)).toNat ≤
            Int.ofNat (kickLidWord (kickAfterFillState evm I)).toNat) = false := by
    rw [decide_eq_false_iff_not]
    exact hnle
  change evalExpr? config frame (kickAfterFillState evm I)
      (.binary .le (.storage fillRef) (.storage lidRef)) = .ok (.bool false)
  rw [evalExpr?]
  simp only [hfill, hlid, EvalResult.bind, bind, evalBinaryOp?]
  rw [hdec]
  all_goals decide

theorem evalExpr_kick_kicks_storage_afterFill (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickFillLocals evm I }
        (kickAfterFillState evm I) (.storage kicksRef) =
      .ok (.int (Int.ofNat (kickKicksWord (kickAfterFillState evm I)).toNat)) := by
  let frame : Frame := { contract := contract, locals := kickFillLocals evm I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := kickAfterFillState evm I)
    (slot := kicksRef) (er := ({ base := "kicks", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨6⟩)
    (value := .int (Int.ofNat (kickKicksWord (kickAfterFillState evm I)).toNat))
    (by simp [frame, kicksRef, kickFillLocals, kickLocals])
    (by simp [frame, evalStorageRef, evalStorageRefSteps, kicksRef, EvalResult.bind, pure, bind])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by
      simpa [kickKicksWord, flapperSlotWord] using
        flapperStorageLocLoad_uint256 (kickAfterFillState evm I) ⟨6⟩)

theorem evalExpr_kick_id_add (evm : EVM.State) (I : ExecutionEnv)
    (hkicksLt : (kickKicksWord (kickAfterFillState evm I)).toNat < UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := kickFillLocals evm I }
        (kickAfterFillState evm I)
        (add256 (.storage kicksRef) (.intLit 1)) =
      .ok (.int (Int.ofNat (kickIdWord (kickAfterFillState evm I)).toNat)) := by
  have hkicks := evalExpr_kick_kicks_storage_afterFill evm I
  have hone :
      evalExpr? config { contract := contract, locals := kickFillLocals evm I }
        (kickAfterFillState evm I) (.intLit 1) =
      .ok (.int (Int.ofNat (⟨1⟩ : UInt256).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ok (Value.int 1) =
      .ok (Value.int (Int.ofNat (⟨1⟩ : UInt256).toNat))
    rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide]
    rfl
  exact evalExpr_add256_ok
    (a := kickKicksWord (kickAfterFillState evm I)) (b := (⟨1⟩ : UInt256))
    (sum := kickIdWord (kickAfterFillState evm I))
    hkicks hone rfl (by
      change (kickKicksWord (kickAfterFillState evm I)).toNat + 1 < UInt256.size
      omega)

theorem evalExpr_kick_id_guard_true (evm : EVM.State) (I : ExecutionEnv)
    (hkicksLt : (kickKicksWord (kickAfterFillState evm I)).toNat < UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := kickIdLocals (kickAfterFillState evm I) I }
        (kickAfterFillState evm I)
      (.binary .ge (.var "id") (.storage kicksRef)) = .ok (.bool true) := by
  have hid :
      evalExpr? config
          { contract := contract, locals := kickIdLocals (kickAfterFillState evm I) I }
          (kickAfterFillState evm I) (.var "id") =
        .ok (.int (Int.ofNat (kickIdWord (kickAfterFillState evm I)).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((kickIdLocals (kickAfterFillState evm I) I).get? "id") =
      .ok (.int (Int.ofNat (kickIdWord (kickAfterFillState evm I)).toNat))
    rw [kickIdLocals_get_id]
    rfl
  have hkicks :
      evalExpr? config
          { contract := contract, locals := kickIdLocals (kickAfterFillState evm I) I }
          (kickAfterFillState evm I) (.storage kicksRef) =
        .ok (.int (Int.ofNat (kickKicksWord (kickAfterFillState evm I)).toNat)) := by
    let frame : Frame :=
      { contract := contract, locals := kickIdLocals (kickAfterFillState evm I) I }
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := kickAfterFillState evm I)
      (slot := kicksRef) (er := ({ base := "kicks", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int) (loc := wordLoc ⟨6⟩)
      (value := .int (Int.ofNat (kickKicksWord (kickAfterFillState evm I)).toNat))
      (by simp [frame, kicksRef, kickIdLocals, kickFillLocals, kickLocals])
      (by simp [frame, evalStorageRef, evalStorageRefSteps, kicksRef, EvalResult.bind, pure, bind])
      (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
      (by rfl)
      (by
        simpa [kickKicksWord, flapperSlotWord] using
          flapperStorageLocLoad_uint256 (kickAfterFillState evm I) ⟨6⟩)
  have hidNat := kickIdWord_toNat (kickAfterFillState evm I) hkicksLt
  have hge :
      Int.ofNat (kickKicksWord (kickAfterFillState evm I)).toNat ≤
        Int.ofNat (kickIdWord (kickAfterFillState evm I)).toNat := by
    rw [hidNat]
    exact Int.ofNat_le.mpr (Nat.le_add_right _ _)
  simp only [evalExpr?, hid, hkicks, EvalResult.bind, bind, evalBinaryOp?]
  simpa using hge

theorem assign_kickKicksStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config
      { contract := contract, locals := kickIdLocals (kickAfterFillState evm I) I }
      (kickAfterFillState evm I)
      .storage kicksRef (.int (Int.ofNat (kickIdWord (kickAfterFillState evm I)).toNat)) =
        .ok ({ contract := contract, locals := kickIdLocals (kickAfterFillState evm I) I },
          Solm.EVM.storageStore (kickAfterFillState evm I)
            (kickAfterFillState evm I).executionEnv.codeOwner ⟨6⟩
            (kickIdWord (kickAfterFillState evm I))) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "kicks", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨6⟩)
      (hbase := by simp [kickIdLocals, kickFillLocals, kickLocals, kicksRef])
      (her := by simp [evalStorageRef, evalStorageRefSteps, kicksRef, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa using
    storageLocStore_uint256 (kickAfterFillState evm I) ⟨6⟩
      (kickIdWord (kickAfterFillState evm I))

theorem kickKicksWord_afterFill_eq (evm : EVM.State) (I : ExecutionEnv) :
    kickKicksWord (kickAfterFillState evm I) = kickKicksWord evm := by
  simpa [kickKicksWord, kickAfterFillState, flapperSlotWord, solcSlotWord,
    storageStore_accountMap, storageStore_executionEnv] using
    sstoreAccountMap_storage_findD_ne evm.accountMap evm.executionEnv.codeOwner
      ⟨6⟩ ⟨9⟩ (kickFillNewWord evm I) (by native_decide)

theorem kickIdWord_afterFill_eq (evm : EVM.State) (I : ExecutionEnv) :
    kickIdWord (kickAfterFillState evm I) = kickIdWord evm := by
  simp [kickIdWord, kickKicksWord_afterFill_eq]

theorem evalExpr_kick_id_add_orig (evm : EVM.State) (I : ExecutionEnv)
    (hkicksLt : (kickKicksWord evm).toNat < UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := kickFillLocals evm I }
        (kickAfterFillState evm I)
        (add256 (.storage kicksRef) (.intLit 1)) =
      .ok (.int (Int.ofNat (kickIdWord evm).toNat)) := by
  have hlt :
      (kickKicksWord (kickAfterFillState evm I)).toNat < UInt256.size - 1 := by
    simpa [kickKicksWord_afterFill_eq] using hkicksLt
  simpa [kickIdWord_afterFill_eq] using evalExpr_kick_id_add evm I hlt

theorem evalExpr_kick_id_guard_true_orig (evm : EVM.State) (I : ExecutionEnv)
    (hkicksLt : (kickKicksWord evm).toNat < UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm I }
        (kickAfterFillState evm I)
      (.binary .ge (.var "id") (.storage kicksRef)) = .ok (.bool true) := by
  have hid :
      evalExpr? config { contract := contract, locals := kickIdLocals evm I }
          (kickAfterFillState evm I) (.var "id") =
        .ok (.int (Int.ofNat (kickIdWord evm).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((kickIdLocals evm I).get? "id") =
      .ok (.int (Int.ofNat (kickIdWord evm).toNat))
    rw [kickIdLocals_get_id]
    rfl
  have hkicks :
      evalExpr? config { contract := contract, locals := kickIdLocals evm I }
          (kickAfterFillState evm I) (.storage kicksRef) =
        .ok (.int (Int.ofNat (kickKicksWord (kickAfterFillState evm I)).toNat)) := by
    let frame : Frame := { contract := contract, locals := kickIdLocals evm I }
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := kickAfterFillState evm I)
      (slot := kicksRef) (er := ({ base := "kicks", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int) (loc := wordLoc ⟨6⟩)
      (value := .int (Int.ofNat (kickKicksWord (kickAfterFillState evm I)).toNat))
      (by simp [frame, kicksRef, kickIdLocals, kickFillLocals, kickLocals])
      (by simp [frame, evalStorageRef, evalStorageRefSteps, kicksRef, EvalResult.bind, pure, bind])
      (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
      (by rfl)
      (by
        simpa [kickKicksWord, flapperSlotWord] using
          flapperStorageLocLoad_uint256 (kickAfterFillState evm I) ⟨6⟩)
  have hidNat := kickIdWord_toNat evm hkicksLt
  have hkEq :
      (kickKicksWord (kickAfterFillState evm I)).toNat = (kickKicksWord evm).toNat := by
    rw [kickKicksWord_afterFill_eq]
  have hge :
      Int.ofNat (kickKicksWord (kickAfterFillState evm I)).toNat ≤
        Int.ofNat (kickIdWord evm).toNat := by
    rw [hkEq, hidNat]
    exact Int.ofNat_le.mpr (Nat.le_add_right _ _)
  simp only [evalExpr?, hid, hkicks, EvalResult.bind, bind, evalBinaryOp?]
  simpa using hge

theorem assign_kickKicksStorage_orig (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := kickIdLocals evm I }
      (kickAfterFillState evm I)
      .storage kicksRef (.int (Int.ofNat (kickIdWord evm).toNat)) =
        .ok ({ contract := contract, locals := kickIdLocals evm I },
          kickAfterKicksState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "kicks", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨6⟩)
      (hbase := by simp [kickIdLocals, kickFillLocals, kickLocals, kicksRef])
      (her := by simp [evalStorageRef, evalStorageRefSteps, kicksRef, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [kickAfterKicksState] using
    storageLocStore_uint256 (kickAfterFillState evm I) ⟨6⟩ (kickIdWord evm)

theorem evalExpr_kick_id_var_idLocals_at (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm0 I } evm (.var "id") =
      .ok (.int (Int.ofNat (kickIdWord evm0).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((kickIdLocals evm0 I).get? "id") =
    .ok (.int (Int.ofNat (kickIdWord evm0).toNat))
  rw [kickIdLocals_get_id]
  rfl

theorem assign_kickBidStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := kickIdLocals evm I }
      (kickAfterKicksState evm I)
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
          evalStorageRef_auction_field (kickAfterKicksState evm I) (kickIdLocals evm I)
            (kickIdWord evm) "bid" (by simpa [kickIdValue] using kickIdLocals_get_id evm I))
      (hty := by simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
      (hloc := by rfl)
  simpa [kickAfterBidState] using
    storageLocStore_uint256 (kickAfterKicksState evm I) (auctionBidSlot (kickIdWord evm))
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
      .storage (bidsF (.var "id") "guy") (.address I.source) =
        .ok ({ contract := contract, locals := kickIdLocals evm I },
          kickAfterGuyState evm I) := by
  have hsenderValue :
      (.address I.source : Value) =
        .address (AccountAddress.ofNat (kickSenderWord I).toNat) := by
    rw [show AccountAddress.ofNat (kickSenderWord I).toNat = I.source by
      simpa [kickSenderWord, solcSourceWord] using solcSource_ofNat I]
  rw [hsenderValue]
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
  simpa [kickAfterGuyState, kickGuyStoredWord, addrLoc, kickSenderWord] using
    storageLocStore_address_offset0 (kickAfterLotState evm I)
      (auctionPackedSlot (kickIdWord evm)) (kickSenderWord I)
      (by simpa [kickSenderWord, solcSourceWord] using solcSourceWord_canonical I)

theorem evalExpr_kick_tau_storage (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickIdLocals evm0 I } evm
        (.storage tauRef) =
      .ok (.int (Int.ofNat (kickTauWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := kickIdLocals evm0 I }
  have hload :
      storageLocLoad evm (uint48Loc ⟨5⟩ ⟨6, by decide⟩ (by decide)) =
        .int (Int.ofNat (kickTauWord evm).toNat) := by
    rw [flapperStorageLocLoad_uint48_offset6]
    rw [u256_land_comm
      (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
        (UInt256.ofNat (256 ^ 6))) flapperUint48Mask]
    rfl
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := tauRef) (er := ({ base := "tau", steps := [] } : EvaledStorageRef))
    (t := .int uint48Int) (loc := uint48Loc ⟨5⟩ ⟨6, by decide⟩ (by decide))
    (value := .int (Int.ofNat (kickTauWord evm).toNat))
    (by simp [frame, tauRef, kickIdLocals, kickFillLocals, kickLocals])
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
  have hnowLt : (kickNow48Word evm).toNat < 2 ^ 48 := kickNow48Word_lt evm
  have htauLt : (kickTauWord (kickAfterGuyState evm I)).toNat < 2 ^ 48 :=
    kickTauWord_lt (kickAfterGuyState evm I)
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
          kickAfterEndState evm I) := by
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
  simpa [kickAfterEndState, kickEndStoredWord] using
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

theorem evalExpr_kick_lot_var_end (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickEndLocals evm I }
        evm' (.var "lot") = .ok (kickLotValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((kickEndLocals evm I).get? "lot") =
    .ok (kickLotValue I)
  rw [kickEndLocals_get_lot]
  rfl

theorem evalExpr_kick_vat_storage_of_locals
    (evm : EVM.State) (locals : Store) (hvat : "vat" ∉ locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (kickVatWord evm.accountMap evm.executionEnv).toNat)) := by
  simpa [kickVatWord] using
    evalExpr_cage_vat_storage_of_locals evm locals hvat

theorem evalExprs_kick_move_args (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := kickEndLocals evm I } evm'
        [sender, thisAddr, .var "lot"] =
      .ok [.address evm'.executionEnv.source, .address evm'.executionEnv.codeOwner,
        kickLotValue I] := by
  simp [evalExprs?, evalExpr_cage_sender, evalExpr_cage_this,
    evalExpr_kick_lot_var_end]
  rfl

theorem evalExpr_kick_id_var_move (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := kickMoveLocals evm I }
        evm' (.var "id") = .ok (kickIdValue evm) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((kickMoveLocals evm I).get? "id") =
    .ok (kickIdValue evm)
  rw [kickMoveLocals_get_id]
  rfl

theorem flapperKickBodyReverts_unauthorized (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (kickLocals I) kickTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
    checkedExternalCallStmts, List.cons_append, List.nil_append] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := kickLocals I })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest :=
        [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)) ] ++
        checkedAddUintInto "fillNew" (.storage fillRef) (.var "lot") ++
        [ .assign .storage fillRef (.var "fillNew"),
          .require (.binary .le (.storage fillRef) (.storage lidRef)) ] ++
        checkedAddUintInto "id" (.storage kicksRef) (.intLit 1) ++
        [ .assign .storage kicksRef (.var "id"),
          .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
          .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
          .assign .storage (bidsF (.var "id") "guy") sender ] ++
        checkedAdd48Into "end_" now48 (.storage tauRef) ++
        [ .assign .storage (bidsF (.var "id") "end") (.var "end_") ] ++
        checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, thisAddr, .var "lot"] "_moveRet" ++
        [ .return [.var "id"] ])
      hwv
      (evalExpr_auth_false_of_wards_none evm I (kickLocals I) (kickLocals_get_wards I)
        hsrc hauth)

theorem flapperKickBodyReverts_notLive (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hlive : kickLiveWord evm ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (kickLocals I) kickTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
    checkedExternalCallStmts, List.cons_append, List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (evalExpr_auth_true_of_wards_none evm I (kickLocals I) (kickLocals_get_wards I)
            hsrc hauth)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_kick_live_one_false evm I hlive)))

theorem flapperKickBodyReverts_kicksOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hlive : kickLiveWord evm = ⟨1⟩)
    (hkicksGe : UInt256.size - 1 ≤ (kickKicksWord evm).toNat) :
    ExecTransitionBody config contract evm (kickLocals I) kickTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
    checkedExternalCallStmts, List.cons_append, List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (evalExpr_auth_true_of_wards_none evm I (kickLocals I) (kickLocals_get_wards I)
            hsrc hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_live_one_true evm I hlive)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_kick_kicks_lt_max_false evm I hkicksGe)))

theorem flapperKickBodyReverts_fillAddOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hlive : kickLiveWord evm = ⟨1⟩)
    (hkicksLt : (kickKicksWord evm).toNat < UInt256.size - 1)
    (hfillOverflow : UInt256.size ≤ (kickFillWord evm).toNat + (kickLotWord I).toNat) :
    ExecTransitionBody config contract evm (kickLocals I) kickTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
    checkedExternalCallStmts, List.cons_append, List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (evalExpr_auth_true_of_wards_none evm I (kickLocals I) (kickLocals_get_wards I)
            hsrc hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_kicks_lt_max_true evm I hkicksLt)) <|
      ExecBlock.consRevert
        (ExecStmt.letDeclRevert (evalExpr_kick_fill_add_revert evm I hfillOverflow)))

theorem flapperKickBodyReverts_overLid (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hlive : kickLiveWord evm = ⟨1⟩)
    (hkicksLt : (kickKicksWord evm).toNat < UInt256.size - 1)
    (hfillFit : (kickFillWord evm).toNat + (kickLotWord I).toNat < UInt256.size)
    (hgt :
      (kickLidWord (kickAfterFillState evm I)).toNat <
        (kickFillWord (kickAfterFillState evm I)).toNat) :
    ExecTransitionBody config contract evm (kickLocals I) kickTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
    checkedExternalCallStmts, List.cons_append, List.nil_append] using
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
        (ExecStmt.letDecl (evalExpr_kick_fill_add_ok evm I hfillFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_fill_guard_true evm I hfillFit)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_fillNew_var evm evm I)
          (assign_kickFillStorage evm I)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_kick_fill_le_lid_false evm I hgt)))

theorem flapperKickBodyReverts_endAddOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hlive : kickLiveWord evm = ⟨1⟩)
    (hkicksLt : (kickKicksWord evm).toNat < UInt256.size - 1)
    (hfillFit : (kickFillWord evm).toNat + (kickLotWord I).toNat < UInt256.size)
    (hfillLe :
      (kickFillWord (kickAfterFillState evm I)).toNat ≤
        (kickLidWord (kickAfterFillState evm I)).toNat)
    (hendOverflow :
      2 ^ 48 ≤
        (kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat) :
    ExecTransitionBody config contract evm (kickLocals I) kickTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
    checkedExternalCallStmts, List.cons_append, List.nil_append] using
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
        (ExecStmt.letDecl (evalExpr_kick_fill_add_ok evm I hfillFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_fill_guard_true evm I hfillFit)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_fillNew_var evm evm I)
          (assign_kickFillStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_fill_le_lid_true evm I hfillLe)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_kick_id_add_orig evm I hkicksLt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_id_guard_true_orig evm I hkicksLt)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_id_var_idLocals_at evm (kickAfterFillState evm I) I)
          (assign_kickKicksStorage_orig evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_bid_var_at evm (kickAfterKicksState evm I) I)
          (assign_kickBidStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_lot_var_at evm (kickAfterBidState evm I) I)
          (assign_kickLotStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_sender_afterLot evm I hsrc)
          (assign_kickGuyStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_kick_endAdd_wrapped evm I)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse
          (evalExpr_kick_end_guard_false_wrapped evm I hendOverflow)))

theorem flapperKickBodyReverts_moveNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hlive : kickLiveWord evm = ⟨1⟩)
    (hkicksLt : (kickKicksWord evm).toNat < UInt256.size - 1)
    (hfillFit : (kickFillWord evm).toNat + (kickLotWord I).toNat < UInt256.size)
    (hfillLe :
      (kickFillWord (kickAfterFillState evm I)).toNat ≤
        (kickLidWord (kickAfterFillState evm I)).toNat)
    (hendFit :
      (kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat < 2 ^ 48)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord (kickAfterEndState evm I).accountMap
        (kickVatWord (kickAfterEndState evm I).accountMap
          (kickAfterEndState evm I).executionEnv) = ⟨0⟩) :
    ExecTransitionBody config contract evm (kickLocals I) kickTransition.body .reverted := by
  let evmMove := kickAfterEndState evm I
  have hvat :
      evalExpr? config { contract := contract, locals := kickEndLocals evm I }
          evmMove (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat
          (kickVatWord evmMove.accountMap evmMove.executionEnv).toNat)) :=
    evalExpr_kick_vat_storage_of_locals evmMove (kickEndLocals evm I)
      (by simp [kickEndLocals, kickIdLocals, kickFillLocals, kickLocals])
  have hnoCodeLookup :
      (UInt256.ofNat
        ((evmMove.lookupAccount
          (AccountAddress.ofNat
            (kickVatWord evmMove.accountMap evmMove.executionEnv).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount, evmMove] using
      flapperExtCodeSizeWord_zero_lookup_code_zero
        (σ := evmMove.accountMap)
        (target := kickVatWord evmMove.accountMap evmMove.executionEnv)
        (addr := AccountAddress.ofNat
          (kickVatWord evmMove.accountMap evmMove.executionEnv).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        (by simpa [evmMove] using hnoCode)
  have hguard :
      evalExpr? config { contract := contract, locals := kickEndLocals evm I } evmMove
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_cage_extCodeGuard_false hvat hnoCodeLookup
  have hchecked :
      ExecBlock config { contract := contract, locals := kickEndLocals evm I } evmMove
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, thisAddr, .var "lot"] "_moveRet")
        .reverted := by
    exact checkedExternalCallNoCode hguard
  have htail :
      ExecBlock config { contract := contract, locals := kickEndLocals evm I } evmMove
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, thisAddr, .var "lot"] "_moveRet" ++
          [.return [.var "id"]])
        .reverted :=
   execBlock_append_term hchecked (by intro f e h; cases h)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
    checkedExternalCallStmts, List.cons_append, List.nil_append, evmMove] using
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
        (ExecStmt.letDecl (evalExpr_kick_fill_add_ok evm I hfillFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_fill_guard_true evm I hfillFit)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_fillNew_var evm evm I)
          (assign_kickFillStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_fill_le_lid_true evm I hfillLe)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_kick_id_add_orig evm I hkicksLt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_id_guard_true_orig evm I hkicksLt)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_id_var_idLocals_at evm (kickAfterFillState evm I) I)
          (assign_kickKicksStorage_orig evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_bid_var_at evm (kickAfterKicksState evm I) I)
          (assign_kickBidStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_lot_var_at evm (kickAfterBidState evm I) I)
          (assign_kickLotStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_sender_afterLot evm I hsrc)
          (assign_kickGuyStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_kick_endAdd_ok evm I hendFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_end_guard_true evm I hendFit)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_end_var evm I)
          (assign_kickEndStorage_value evm I hendFit)) <|
      htail)

theorem flapperKickBodyReverts_moveCallFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hlive : kickLiveWord evm = ⟨1⟩)
    (hkicksLt : (kickKicksWord evm).toNat < UInt256.size - 1)
    (hfillFit : (kickFillWord evm).toNat + (kickLotWord I).toNat < UInt256.size)
    (hfillLe :
      (kickFillWord (kickAfterFillState evm I)).toNat ≤
        (kickLidWord (kickAfterFillState evm I)).toNat)
    (hendFit :
      (kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat < 2 ^ 48)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord (kickAfterEndState evm I).accountMap
        (kickVatWord (kickAfterEndState evm I).accountMap
          (kickAfterEndState evm I).executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (kickAfterEndState evm I)
        (EVM.address (AccountAddress.ofNat
          (kickVatWord (kickAfterEndState evm I).accountMap
            (kickAfterEndState evm I).executionEnv).toNat))
        "move" 0
        [.address (kickAfterEndState evm I).executionEnv.source,
          .address (kickAfterEndState evm I).executionEnv.codeOwner, kickLotValue I]
        (false, evm', out) true) :
    ExecTransitionBody config contract evm (kickLocals I) kickTransition.body .reverted := by
  let evmMove := kickAfterEndState evm I
  have hvat :
      evalExpr? config { contract := contract, locals := kickEndLocals evm I }
          evmMove (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat
          (kickVatWord evmMove.accountMap evmMove.executionEnv).toNat)) :=
    evalExpr_kick_vat_storage_of_locals evmMove (kickEndLocals evm I)
      (by simp [kickEndLocals, kickIdLocals, kickFillLocals, kickLocals])
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evmMove.lookupAccount
          (AccountAddress.ofNat
            (kickVatWord evmMove.accountMap evmMove.executionEnv).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount, evmMove] using
      flapperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmMove.accountMap)
        (target := kickVatWord evmMove.accountMap evmMove.executionEnv)
        (addr := AccountAddress.ofNat
          (kickVatWord evmMove.accountMap evmMove.executionEnv).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        (by simpa [evmMove] using hcodeSize)
  have hguard :
      evalExpr? config { contract := contract, locals := kickEndLocals evm I } evmMove
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cage_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_kick_move_args evm evmMove I
  have hchecked :
      ExecBlock config { contract := contract, locals := kickEndLocals evm I } evmMove
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, thisAddr, .var "lot"] "_moveRet")
        .reverted := by
    exact checkedExternalCallFailure hguard hvat hargs (by simpa [evmMove] using hcall)
  have htail :
      ExecBlock config { contract := contract, locals := kickEndLocals evm I } evmMove
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, thisAddr, .var "lot"] "_moveRet" ++
          [.return [.var "id"]])
        .reverted :=
   execBlock_append_term hchecked (by intro f e h; cases h)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
    checkedExternalCallStmts, List.cons_append, List.nil_append, evmMove] using
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
        (ExecStmt.letDecl (evalExpr_kick_fill_add_ok evm I hfillFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_fill_guard_true evm I hfillFit)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_fillNew_var evm evm I)
          (assign_kickFillStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_fill_le_lid_true evm I hfillLe)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_kick_id_add_orig evm I hkicksLt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_id_guard_true_orig evm I hkicksLt)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_id_var_idLocals_at evm (kickAfterFillState evm I) I)
          (assign_kickKicksStorage_orig evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_bid_var_at evm (kickAfterKicksState evm I) I)
          (assign_kickBidStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_lot_var_at evm (kickAfterBidState evm I) I)
          (assign_kickLotStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_sender_afterLot evm I hsrc)
          (assign_kickGuyStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_kick_endAdd_ok evm I hendFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_end_guard_true evm I hendFit)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_end_var evm I)
          (assign_kickEndStorage_value evm I hendFit)) <|
      htail)

theorem flapperKickBodyReturns_moveCallSuccess
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hlive : kickLiveWord evm = ⟨1⟩)
    (hkicksLt : (kickKicksWord evm).toNat < UInt256.size - 1)
    (hfillFit : (kickFillWord evm).toNat + (kickLotWord I).toNat < UInt256.size)
    (hfillLe :
      (kickFillWord (kickAfterFillState evm I)).toNat ≤
        (kickLidWord (kickAfterFillState evm I)).toNat)
    (hendFit :
      (kickNow48Word evm).toNat + (kickTauWord (kickAfterGuyState evm I)).toNat < 2 ^ 48)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord (kickAfterEndState evm I).accountMap
        (kickVatWord (kickAfterEndState evm I).accountMap
          (kickAfterEndState evm I).executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (kickAfterEndState evm I)
        (EVM.address (AccountAddress.ofNat
          (kickVatWord (kickAfterEndState evm I).accountMap
            (kickAfterEndState evm I).executionEnv).toNat))
        "move" 0
        [.address (kickAfterEndState evm I).executionEnv.source,
          .address (kickAfterEndState evm I).executionEnv.codeOwner, kickLotValue I]
        (true, evm', out) true) :
    ExecTransitionBody config contract evm (kickLocals I) kickTransition.body
      (.returned { contract := contract, locals := kickMoveLocals evm I }
        evm' (some [.int (Int.ofNat (kickIdWord evm).toNat)])) := by
  let evmMove := kickAfterEndState evm I
  have hvat :
      evalExpr? config { contract := contract, locals := kickEndLocals evm I }
          evmMove (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat
          (kickVatWord evmMove.accountMap evmMove.executionEnv).toNat)) :=
    evalExpr_kick_vat_storage_of_locals evmMove (kickEndLocals evm I)
      (by simp [kickEndLocals, kickIdLocals, kickFillLocals, kickLocals])
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evmMove.lookupAccount
          (AccountAddress.ofNat
            (kickVatWord evmMove.accountMap evmMove.executionEnv).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount, evmMove] using
      flapperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmMove.accountMap)
        (target := kickVatWord evmMove.accountMap evmMove.executionEnv)
        (addr := AccountAddress.ofNat
          (kickVatWord evmMove.accountMap evmMove.executionEnv).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        (by simpa [evmMove] using hcodeSize)
  have hguard :
      evalExpr? config { contract := contract, locals := kickEndLocals evm I } evmMove
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cage_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_kick_move_args evm evmMove I
  have hdec : config.externalABI.decode? "move" out = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hchecked :
      ExecBlock config { contract := contract, locals := kickEndLocals evm I } evmMove
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, thisAddr, .var "lot"] "_moveRet")
        (.ok { contract := contract, locals := kickMoveLocals evm I } evm') := by
    simpa [checkedExternalCallStmts, kickMoveLocals] using
      checkedExternalCallSuccess hguard hvat hargs (by simpa [evmMove] using hcall) hdec
  have hreturns :
      evalExprs? config { contract := contract, locals := kickMoveLocals evm I }
          evm' [.var "id"] =
        .ok [.int (Int.ofNat (kickIdWord evm).toNat)] := by
    simp [evalExprs?, evalExpr_kick_id_var_move, kickIdValue, EvalResult.bind, bind, pure]
  have hreturn :
      ExecBlock config { contract := contract, locals := kickMoveLocals evm I } evm'
        [.return [.var "id"]]
        (.returned { contract := contract, locals := kickMoveLocals evm I }
          evm' (some [.int (Int.ofNat (kickIdWord evm).toNat)])) := by
    exact ExecBlock.consReturn (ExecStmt.return hreturns)
  have htail :
      ExecBlock config { contract := contract, locals := kickEndLocals evm I } evmMove
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, thisAddr, .var "lot"] "_moveRet" ++
          [.return [.var "id"]])
        (.returned { contract := contract, locals := kickMoveLocals evm I }
          evm' (some [.int (Int.ofNat (kickIdWord evm).toNat)])) :=
   execBlock_append hchecked hreturn
  refine ExecFuncBody.execBlockRet ?_
  simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
    checkedExternalCallStmts, List.cons_append, List.nil_append, evmMove] using
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
        (ExecStmt.letDecl (evalExpr_kick_fill_add_ok evm I hfillFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_fill_guard_true evm I hfillFit)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_fillNew_var evm evm I)
          (assign_kickFillStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_fill_le_lid_true evm I hfillLe)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_kick_id_add_orig evm I hkicksLt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_id_guard_true_orig evm I hkicksLt)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_id_var_idLocals_at evm (kickAfterFillState evm I) I)
          (assign_kickKicksStorage_orig evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_bid_var_at evm (kickAfterKicksState evm I) I)
          (assign_kickBidStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_lot_var_at evm (kickAfterBidState evm I) I)
          (assign_kickLotStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_sender_afterLot evm I hsrc)
          (assign_kickGuyStorage evm I)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_kick_endAdd_ok evm I hendFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_kick_end_guard_true evm I hendFit)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_kick_end_var evm I)
          (assign_kickEndStorage_value evm I hendFit)) <|
      htail)

theorem decodeCalldata_legacyUint256_uint256_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiUInt256, abiUInt256] cd =
      some (((∅ : Solm.Store).insert x
        (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 36 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x, y])
    (types := [abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 32) htake36]
  change decodeCalldata.insertValues [x, y]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat)] ∅ =
    some (((∅ : Solm.Store).insert x
      (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
      (.int (Int.ofNat (calldataWord cd 36).toNat)))
  rw [hword4, hword36]
  simp [decodeCalldata.insertValues]

theorem decodeCalldata_legacyUint256_uint256_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiUInt256, abiUInt256] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x, y])
    (types := [abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hlen0 : 32 ≤ (cd.toList.drop 4).length
  · have htake0 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
      (bytes := cd.toList.drop 4) (start := 0) htake0]
    have htake32n : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]
      omega
    rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (start := 32) (by simpa using htake32n)]
    simp only [Option.bind, bind]
  · have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]

theorem flapperDecode_kick_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (kickTransition.params.map Param.name)
      (transitionSignature kickTransition).paramTypes I.calldata = some (kickLocals I) := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["lot", "bid"]
      [abiUInt256, abiUInt256] I.calldata =
    some (((∅ : Store).insert "lot" (kickLotValue I)).insert "bid" (kickBidValue I))
  exact decodeCalldata_legacyUint256_uint256_ok (cd := I.calldata)
    (x := "lot") (y := "bid") hsz68

theorem flapperDecode_kick_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (kickTransition.params.map Param.name)
      (transitionSignature kickTransition).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["lot", "bid"]
      [abiUInt256, abiUInt256] I.calldata = none
  exact decodeCalldata_legacyUint256_uint256_none_short (cd := I.calldata)
    (x := "lot") (y := "bid") hsz4 hshort

theorem flapperReachKickBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flapperSelBytes 8)) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨796⟩ [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flapperSelWord I = ⟨0xca40c419⟩ := by
    simpa [flapperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0xca 0x40 0xc4 0x19 ⟨0xca40c419⟩
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
  have heq0 : ∀ j, j < 0 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighHighFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighHighFirstArmPc 0))
        (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨796⟩ 0 hfirst
    (fun j hj => flapperHighHighArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flapperKickX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨796⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3901⟩
      [kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flapperBytecode) (sel := sel) (entry := ⟨796⟩) (ret := ⟨313⟩)
    (decoded := ⟨818⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize)
  have rd819 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd820 := rd819.pop (by native_decide) (by evm_ov)
  have rd821 := rd820.dup1 (by native_decide) (by evm_ov)
  have rd822 := rd821.calldataload (by native_decide) (by evm_ov)
  have rd826 := evm_run rd822 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw push2 ⟨3901⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [kickLotWord, kickBidWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨32⟩ : UInt256) + (⟨4⟩ : UInt256)).toNat = 36 from by decide]
      using rd826.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flapperKickX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨796⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flapperBytecode) (sel := sel) (entry := ⟨796⟩) (ret := ⟨313⟩)
    (decoded := ⟨818⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem flapperKickX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD flapperBytecode I g s0 ⟨3901⟩
      [kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨3994⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd3907pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3908 := rd3907pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3912pre := evm_run rd3908 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3913 := rd3912pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3916pre := evm_run rd3913 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3917 := rd3916pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k3918, C3918, rd3918raw⟩ := rd3917.sload (by native_decide) (by evm_ov)
  have rd3918 : RD flapperBytecode I g s0 ⟨3918⟩
      (relyAuthWord σ I :: ⟨0⟩ :: kickBidWord I :: kickLotWord I :: ⟨313⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3918 C3918 := by
    simpa [relyAuthWord, flapperSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using
      rd3918raw
  have rd3921pre := evm_run rd3918 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd3921pre
  have rd3924 := rd3921pre.pushConst (⟨3994⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd3924.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flapperKickX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD flapperBytecode I g s0 ⟨3901⟩
      [kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd3907pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3908 := rd3907pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3912pre := evm_run rd3908 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3913 := rd3912pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3916pre := evm_run rd3913 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3917 := rd3916pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k3918, C3918, rd3918raw⟩ := rd3917.sload (by native_decide) (by evm_ov)
  have rd3918 : RD flapperBytecode I g s0 ⟨3918⟩
      (relyAuthWord σ I :: ⟨0⟩ :: kickBidWord I :: kickLotWord I :: ⟨313⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3918 C3918 := by
    simpa [relyAuthWord, flapperSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using
      rd3918raw
  have rd3921pre := evm_run rd3918 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd3921pre
  have rd3924 := rd3921pre.pushConst (⟨3994⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd3925 := rd3924.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3925⟩)
    (len := ⟨22⟩)
    (rawWord := ⟨0x119b185c1c195c8bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨82⟩)
    (word := ⟨0x466c61707065722f6e6f742d617574686f72697a656400000000000000000000⟩)
    (op := .PUSH22)
    (width := 22)
    rd3925
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem flapperKickX_liveOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : flapperSlotWord ⟨7⟩ σ I = ⟨1⟩)
    (h : RD flapperBytecode I g s0 ⟨3994⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨4068⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3997 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3998, C3998, rd3998raw⟩ := rd3997.sload (by native_decide) (by evm_ov)
  have rd3998 : RD flapperBytecode I g s0 ⟨3998⟩
      (flapperSlotWord ⟨7⟩ σ I :: ⟨0⟩ :: kickBidWord I :: kickLotWord I :: ⟨313⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3998 C3998 := by
    simpa [flapperSlotWord] using rd3998raw
  have rd4001pre := evm_run rd3998 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hlive, u256_eq_refl] at rd4001pre
  have rd4004 := rd4001pre.pushConst (⟨4068⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd4004.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

theorem flapperKickX_notLive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : flapperSlotWord ⟨7⟩ σ I ≠ ⟨1⟩)
    (h : RD flapperBytecode I g s0 ⟨3994⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g s0 := by
  have rd3997 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3998, C3998, rd3998raw⟩ := rd3997.sload (by native_decide) (by evm_ov)
  have rd3998 : RD flapperBytecode I g s0 ⟨3998⟩
      (flapperSlotWord ⟨7⟩ σ I :: ⟨0⟩ :: kickBidWord I :: kickLotWord I :: ⟨313⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3998 C3998 := by
    simpa [flapperSlotWord] using rd3998raw
  have rd4001pre := evm_run rd3998 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (flapperSlotWord ⟨7⟩ σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hlive hbad.symm)
  rw [heq] at rd4001pre
  have rd4004 := rd4001pre.pushConst (⟨4068⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd4005 := rd4004.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨4005⟩)
    (len := ⟨16⟩)
    (rawWord := ⟨93608704067736590129290171836229318245⟩)
    (shift := ⟨128⟩)
    (word := ⟨0x466c61707065722f6e6f742d6c69766500000000000000000000000000000000⟩)
    (op := .PUSH16)
    (width := 16)
    rd4005
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem flapperKickX_kicksOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hkicksLt : (flapperSlotWord ⟨6⟩ σ I).toNat < UInt256.size - 1)
    (h : RD flapperBytecode I g s0 ⟨4068⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨4143⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4074pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k4075, C4075, rd4075raw⟩ := rd4074pre.sload (by native_decide) (by evm_ov)
  have rd4075 : RD flapperBytecode I g s0 ⟨4075⟩
      (flapperSlotWord ⟨6⟩ σ I :: UInt256.lnot ⟨0⟩ :: ⟨0⟩ :: kickBidWord I ::
        kickLotWord I :: ⟨313⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4075 C4075 := by
    simpa [flapperSlotWord] using rd4075raw
  have rd4076 := rd4075.lt (by native_decide) (by evm_ov)
  have hlt :
      UInt256.lt (flapperSlotWord ⟨6⟩ σ I) (UInt256.lnot ⟨0⟩) = ⟨1⟩ := by
    apply ult_one
    rw [show (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 from by native_decide]
    exact hkicksLt
  rw [hlt] at rd4076
  have rd4079 := rd4076.pushConst (⟨4143⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd4079.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

theorem flapperKickX_kicksOverflow {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hkicksGe : UInt256.size - 1 ≤ (flapperSlotWord ⟨6⟩ σ I).toNat)
    (h : RD flapperBytecode I g s0 ⟨4068⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g s0 := by
  have rd4074pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k4075, C4075, rd4075raw⟩ := rd4074pre.sload (by native_decide) (by evm_ov)
  have rd4075 : RD flapperBytecode I g s0 ⟨4075⟩
      (flapperSlotWord ⟨6⟩ σ I :: UInt256.lnot ⟨0⟩ :: ⟨0⟩ :: kickBidWord I ::
        kickLotWord I :: ⟨313⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4075 C4075 := by
    simpa [flapperSlotWord] using rd4075raw
  have rd4076 := rd4075.lt (by native_decide) (by evm_ov)
  have hlt :
      UInt256.lt (flapperSlotWord ⟨6⟩ σ I) (UInt256.lnot ⟨0⟩) = ⟨0⟩ := by
    apply ult_zero
    rw [show (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 from by native_decide]
    exact hkicksGe
  rw [hlt] at rd4076
  have rd4079 := rd4076.pushConst (⟨4143⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd4080 := rd4079.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨4080⟩)
    (len := ⟨16⟩)
    (rawWord := ⟨93608704067736590129364183558682079095⟩)
    (shift := ⟨128⟩)
    (word := ⟨0x466c61707065722f6f766572666c6f7700000000000000000000000000000000⟩)
    (op := .PUSH16)
    (width := 16)
    rd4080
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem flapperKickX_fillAddOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hfillFit : (flapperSlotWord ⟨9⟩ σ I).toNat + (kickLotWord I).toNat < UInt256.size)
    (h : RD flapperBytecode I g s0 ⟨4143⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨4155⟩
      [flapperSlotWord ⟨9⟩ σ I + kickLotWord I, ⟨0⟩, kickBidWord I,
        kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4149pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨4155⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨9⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k4150, C4150, rd4150raw⟩ := rd4149pre.sload (by native_decide) (by evm_ov)
  have rd4150 : RD flapperBytecode I g s0 ⟨4150⟩
      [flapperSlotWord ⟨9⟩ σ I, ⟨4155⟩, ⟨0⟩, kickBidWord I, kickLotWord I,
        ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4150 C4150 := by
    simpa [flapperSlotWord] using rd4150raw
  have rd4154pre := evm_run rd4150 with [
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨4979⟩ (by native_decide) (by evm_ov)]
  have rd4979 := rd4154pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4155⟩ := RD.solcCheckedAddSuccess
    (pc := ⟨4979⟩) (okPc := ⟨4930⟩)
    (a := flapperSlotWord ⟨9⟩ σ I) (b := kickLotWord I) (ret := ⟨4155⟩)
    (R := [⟨0⟩, kickBidWord I, kickLotWord I, ⟨313⟩, sel])
    rd4979
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    hfillFit (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd4155⟩

set_option maxHeartbeats 1000000 in
theorem flapperKickX_fillAddOverflow {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hfillOverflow :
      UInt256.size ≤ (flapperSlotWord ⟨9⟩ σ I).toNat + (kickLotWord I).toNat)
    (h : RD flapperBytecode I g s0 ⟨4143⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g s0 := by
  have rd4149pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨4155⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨9⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k4150, C4150, rd4150raw⟩ := rd4149pre.sload (by native_decide) (by evm_ov)
  have rd4150 : RD flapperBytecode I g s0 ⟨4150⟩
      [flapperSlotWord ⟨9⟩ σ I, ⟨4155⟩, ⟨0⟩, kickBidWord I, kickLotWord I,
        ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4150 C4150 := by
    simpa [flapperSlotWord] using rd4150raw
  have rd4154pre := evm_run rd4150 with [
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨4979⟩ (by native_decide) (by evm_ov)]
  have rd4979 := rd4154pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd4985pre := evm_run rd4979 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd4986 := rd4985pre.lt (by native_decide) (by evm_ov)
  have hsumLt2 :
      (flapperSlotWord ⟨9⟩ σ I).toNat + (kickLotWord I).toNat < 2 * UInt256.size := by
    have ha : (flapperSlotWord ⟨9⟩ σ I).toNat < UInt256.size :=
      (flapperSlotWord ⟨9⟩ σ I).val.isLt
    have hb : (kickLotWord I).toNat < UInt256.size :=
      (kickLotWord I).val.isLt
    omega
  have hmod :
      ((flapperSlotWord ⟨9⟩ σ I).toNat + (kickLotWord I).toNat) % UInt256.size =
        (flapperSlotWord ⟨9⟩ σ I).toNat + (kickLotWord I).toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hfillOverflow]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat :
      (flapperSlotWord ⟨9⟩ σ I + kickLotWord I).toNat =
        (flapperSlotWord ⟨9⟩ σ I).toNat + (kickLotWord I).toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt :
      UInt256.lt (flapperSlotWord ⟨9⟩ σ I + kickLotWord I)
        (flapperSlotWord ⟨9⟩ σ I) = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hb : (kickLotWord I).toNat < UInt256.size :=
      (kickLotWord I).val.isLt
    omega
  rw [hlt] at rd4986
  have rd4987 := rd4986.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd4987
  have rd4990 := rd4987.push2 ⟨4930⟩ (by native_decide) (by evm_ov)
  have rd4991 := rd4990.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd4991
    (by native_decide) (by native_decide) (by native_decide)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem flapperKickX_lidOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hfillLe :
      (flapperSlotWord ⟨9⟩ σ I + kickLotWord I).toNat ≤
        (flapperSlotWord ⟨8⟩ (kickRuntimeAfterFillMap I.codeOwner σ I) I).toNat)
    (h : RD flapperBytecode I g s0 ⟨4155⟩
      [flapperSlotWord ⟨9⟩ σ I + kickLotWord I, ⟨0⟩, kickBidWord I,
        kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨4233⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickRuntimeAfterFillMap I.codeOwner σ I) k' C' := by
  have rd4159pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨9⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k4161, C4161, rd4161raw⟩ := rd4159pre.sstore hperm
    (by native_decide) (by evm_ov)
  have rd4161 : RD flapperBytecode I g s0 ⟨4161⟩
      [flapperSlotWord ⟨9⟩ σ I + kickLotWord I, ⟨0⟩, kickBidWord I,
        kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickRuntimeAfterFillMap I.codeOwner σ I) k4161 C4161 := by
    simpa [kickRuntimeAfterFillMap] using rd4161raw
  have rd4163pre := rd4161.push1 ⟨8⟩ (by native_decide) (by evm_ov)
  obtain ⟨k4164, C4164, rd4164raw⟩ := rd4163pre.sload (by native_decide) (by evm_ov)
  have rd4164 : RD flapperBytecode I g s0 ⟨4164⟩
      [flapperSlotWord ⟨8⟩ (kickRuntimeAfterFillMap I.codeOwner σ I) I,
        flapperSlotWord ⟨9⟩ σ I + kickLotWord I, ⟨0⟩, kickBidWord I,
        kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickRuntimeAfterFillMap I.codeOwner σ I) k4164 C4164 := by
    simpa [flapperSlotWord] using rd4164raw
  have rd4165pre := rd4164.lt (by native_decide) (by evm_ov)
  have hlt :
      UInt256.lt (flapperSlotWord ⟨8⟩ (kickRuntimeAfterFillMap I.codeOwner σ I) I)
        (flapperSlotWord ⟨9⟩ σ I + kickLotWord I) = ⟨0⟩ :=
    ult_zero hfillLe
  rw [hlt] at rd4165pre
  have rd4166pre := rd4165pre.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4166pre
  have rd4169 := rd4166pre.push2 ⟨4233⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd4169.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flapperKickX_overLid {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hoverLid :
      (flapperSlotWord ⟨8⟩ (kickRuntimeAfterFillMap I.codeOwner σ I) I).toNat <
        (flapperSlotWord ⟨9⟩ σ I + kickLotWord I).toNat)
    (h : RD flapperBytecode I g s0 ⟨4155⟩
      [flapperSlotWord ⟨9⟩ σ I + kickLotWord I, ⟨0⟩, kickBidWord I,
        kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g s0 := by
  have rd4159pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨9⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k4161, C4161, rd4161raw⟩ := rd4159pre.sstore hperm
    (by native_decide) (by evm_ov)
  have rd4161 : RD flapperBytecode I g s0 ⟨4161⟩
      [flapperSlotWord ⟨9⟩ σ I + kickLotWord I, ⟨0⟩, kickBidWord I,
        kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickRuntimeAfterFillMap I.codeOwner σ I) k4161 C4161 := by
    simpa [kickRuntimeAfterFillMap] using rd4161raw
  have rd4163pre := rd4161.push1 ⟨8⟩ (by native_decide) (by evm_ov)
  obtain ⟨k4164, C4164, rd4164raw⟩ := rd4163pre.sload (by native_decide) (by evm_ov)
  have rd4164 : RD flapperBytecode I g s0 ⟨4164⟩
      [flapperSlotWord ⟨8⟩ (kickRuntimeAfterFillMap I.codeOwner σ I) I,
        flapperSlotWord ⟨9⟩ σ I + kickLotWord I, ⟨0⟩, kickBidWord I,
        kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickRuntimeAfterFillMap I.codeOwner σ I) k4164 C4164 := by
    simpa [flapperSlotWord] using rd4164raw
  have rd4165pre := rd4164.lt (by native_decide) (by evm_ov)
  have hlt :
      UInt256.lt (flapperSlotWord ⟨8⟩ (kickRuntimeAfterFillMap I.codeOwner σ I) I)
        (flapperSlotWord ⟨9⟩ σ I + kickLotWord I) = ⟨1⟩ :=
    ult_one hoverLid
  rw [hlt] at rd4165pre
  have rd4166pre := rd4165pre.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd4166pre
  have rd4169 := rd4166pre.push2 ⟨4233⟩ (by native_decide) (by evm_ov)
  have rd4170 := rd4169.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨4170⟩)
    (len := ⟨16⟩)
    (rawWord := ⟨23402176016934147532341045889431444057⟩)
    (shift := ⟨130⟩)
    (word := ⟨0x466c61707065722f6f7665722d6c696400000000000000000000000000000000⟩)
    (op := .PUSH16)
    (width := 16)
    rd4170
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem flapperKickX_toCheckedAddStart {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} (hperm : I.perm = true)
    (h : RD flapperBytecode I g s0 ⟨4233⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickRuntimeAfterFillMap I.codeOwner σ I) k C) :
    let id := kickRuntimeIdWord σ I
    let memStore := twoWordHashMem id ⟨1⟩ (relyAuthHashMem I)
    let σGuy := kickRuntimeAfterGuyMap I.codeOwner σ I
    ∃ k' C', RD flapperBytecode I g s0 ⟨4936⟩
      [kickRuntimeTauWord I.codeOwner σ I, UInt256.ofNat I.header.timestamp, ⟨4319⟩,
        id, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty (cA, σGuy) k' C' := by
  intro id memStore σGuy
  let σFill := kickRuntimeAfterFillMap I.codeOwner σ I
  let σKicks := kickRuntimeAfterKicksMap I.codeOwner σ I
  let σBid := kickRuntimeAfterBidMap I.codeOwner σ I
  let σLot := kickRuntimeAfterLotMap I.codeOwner σ I
  let base := solcMappingSlot ⟨1⟩ id
  let packedSlot := auctionPackedSlot id
  let oldPacked := solcSlotWord σLot I packedSlot
  let guyStored := kickRuntimeGuyStoredWord I.codeOwner σ I
  have hslot6 :
      flapperSlotWord ⟨6⟩ σFill I = flapperSlotWord ⟨6⟩ σ I := by
    simpa [σFill, kickRuntimeAfterFillMap, flapperSlotWord, solcSlotWord] using
      sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨6⟩ ⟨9⟩
        (flapperSlotWord ⟨9⟩ σ I + kickLotWord I) (by native_decide)
  have rd4238pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k4239, C4239, rd4239raw⟩ := rd4238pre.sload
    (by native_decide) (by evm_ov)
  have rd4239 : RD flapperBytecode I g s0 ⟨4239⟩
      [flapperSlotWord ⟨6⟩ σ I, ⟨6⟩, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σFill)
      k4239 C4239 := by
    have rd4239' : RD flapperBytecode I g s0 ⟨4239⟩
        [flapperSlotWord ⟨6⟩ σFill I, ⟨6⟩, kickBidWord I, kickLotWord I,
          ⟨313⟩, sel]
        (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σFill)
        k4239 C4239 := by
      simpa [σFill, flapperSlotWord] using rd4239raw
    simpa [hslot6] using rd4239'
  have rd4247pre := evm_run rd4239 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k4248, C4248, rd4248raw⟩ := rd4247pre.sstore hperm
    (by native_decide) (by evm_ov)
  have hidRaw : ⟨1⟩ + flapperSlotWord ⟨6⟩ σ I = id := by
    rw [u256_add_comm]
  have hidRawSolc : ⟨1⟩ + solcSlotWord σ I ⟨6⟩ = id := by
    simpa [flapperSlotWord] using hidRaw
  have rd4248 : RD flapperBytecode I g s0 ⟨4248⟩
      [⟨1⟩, id, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σKicks) k4248 C4248 := by
    simpa [id, σKicks, σFill, kickRuntimeAfterKicksMap, kickRuntimeAfterFillMap,
      kickRuntimeIdWord, flapperSlotWord, hidRawSolc]
      using rd4248raw
  let memKey := wordAt0Mem id (relyAuthHashMem I)
  have rd4251pre := evm_run rd4248 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd4253 := rd4251pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd4257pre := evm_run rd4253 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd4258 := rd4257pre.mstore 0 memStore (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memStore, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd4261pre := evm_run rd4258 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memStore.readWithPadding 0 64))) = base := by
    simpa [base, memStore, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id (relyAuthHashMem I)
  have rd4262 := rd4261pre.keccak256 0 base (UInt256.ofNat 3)
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
  rw [hbidSlot] at rd4262
  have rd4264pre := evm_run rd4262 with [
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  obtain ⟨k4265, C4265, rd4265raw⟩ := rd4264pre.sstore hperm
    (by native_decide) (by evm_ov)
  have rd4265 : RD flapperBytecode I g s0 ⟨4265⟩
      [auctionBidSlot id, ⟨1⟩, id, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty (cA, σBid) k4265 C4265 := by
    simpa [σBid, kickRuntimeAfterBidMap, σKicks, kickRuntimeAfterKicksMap, id]
      using rd4265raw
  have rd4270pre := evm_run rd4265 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hlotSlot : auctionBidSlot id + ⟨1⟩ = auctionLotSlot id := by
    simp [auctionLotSlot, auctionBidSlot]
  rw [hlotSlot] at rd4270pre
  obtain ⟨k4271, C4271, rd4271raw⟩ := rd4270pre.sstore hperm
    (by native_decide) (by evm_ov)
  have rd4271 : RD flapperBytecode I g s0 ⟨4271⟩
      [auctionBidSlot id, id, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty (cA, σLot) k4271 C4271 := by
    simpa [σLot, kickRuntimeAfterLotMap, σBid, kickRuntimeAfterBidMap, id]
      using rd4271raw
  have rd4273pre := evm_run rd4271 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpackedSlot : ⟨2⟩ + auctionBidSlot id = packedSlot := by
    rw [u256_add_comm]
  rw [hpackedSlot] at rd4273pre
  have rd4274 := rd4273pre.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k4276, C4276, rd4276raw⟩ := rd4274.sload
    (by native_decide) (by evm_ov)
  have rd4276 : RD flapperBytecode I g s0 ⟨4276⟩
      [oldPacked, packedSlot, id, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty (cA, σLot) k4276 C4276 := by
    simpa [oldPacked, solcSlotWord, packedSlot] using rd4276raw
  have rd4288pre := evm_run rd4276 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw or (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k4290, C4290, rd4290raw⟩ := rd4288pre.sstore hperm
    (by native_decide) (by evm_ov)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by
    native_decide
  have hsrcCanon : (kickSenderWord I).toNat < EVM.addressModulus := by
    simpa [kickSenderWord, solcSourceWord] using solcSourceWord_canonical I
  have hsrcClean : UInt256.land (kickSenderWord I) solcAddrMask = kickSenderWord I := by
    exact solcAddrMask_clean hsrcCanon
  have hstored :
      UInt256.lor (kickSenderWord I) (UInt256.land (UInt256.lnot solcAddrMask) oldPacked) =
        guyStored := by
    calc
      UInt256.lor (kickSenderWord I) (UInt256.land (UInt256.lnot solcAddrMask) oldPacked) =
          UInt256.lor (UInt256.land oldPacked (UInt256.lnot solcAddrMask)) (kickSenderWord I) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) oldPacked]
            exact u256_lor_comm _ _
      _ = UInt256.lor (UInt256.land oldPacked (UInt256.lnot solcAddrMask))
            (UInt256.land (kickSenderWord I) solcAddrMask) := by
            rw [hsrcClean]
      _ = guyStored := by
            rfl
  have rd4290 : RD flapperBytecode I g s0 ⟨4290⟩
      [id, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty (cA, σGuy) k4290 C4290 := by
    simpa [σGuy, kickRuntimeAfterGuyMap, guyStored, kickRuntimeGuyStoredWord,
      oldPacked, packedSlot, σLot, hmask, hstored, setAddressOffset0Word,
      kickSenderWord] using
      rd4290raw
  have rd4292 := rd4290.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨k4293, C4293, rd4293raw⟩ := rd4292.sload (by native_decide) (by evm_ov)
  have rd4293 : RD flapperBytecode I g s0 ⟨4293⟩
      [flapperSlotWord ⟨5⟩ σGuy I, id, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty (cA, σGuy) k4293 C4293 := by
    simpa [flapperSlotWord] using rd4293raw
  have rd4299 := evm_run rd4293 with [
    raw push2 ⟨4319⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw timestamp (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd4306 := rd4299.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4314 := evm_run rd4306 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨48⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd4315 := rd4314.and (by native_decide) (by evm_ov)
  have rd4318 := rd4315.push2 ⟨4936⟩ (by native_decide) (by evm_ov)
  have rd4936 := rd4318.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, memStore, σGuy, kickRuntimeTauWord, flapperUint48Offset6Word,
      u256_land_comm,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨48⟩ = UInt256.ofNat (256 ^ 6)
        from by native_decide]
      using rd4936⟩

theorem kickRuntimeTauWord_lt (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) :
    (kickRuntimeTauWord owner σ I).toNat < 2 ^ 48 := by
  rw [kickRuntimeTauWord, flapperUint48Offset6Word]
  rw [u256_land_comm flapperUint48Mask
    (UInt256.div (flapperSlotWord ⟨5⟩ (kickRuntimeAfterGuyMap owner σ I) I)
      (UInt256.ofNat (256 ^ 6)))]
  simpa [EVM.twoPow] using
    flapperUint48Masked_lt
      (UInt256.div (flapperSlotWord ⟨5⟩ (kickRuntimeAfterGuyMap owner σ I) I)
        (UInt256.ofNat (256 ^ 6)))

set_option maxHeartbeats 1000000 in
theorem flapperKickX_toEndStoreStart {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
        (kickRuntimeTauWord I.codeOwner σ I).toNat < 2 ^ 48)
    (h : RD flapperBytecode I g s0 ⟨4936⟩
      [kickRuntimeTauWord I.codeOwner σ I, UInt256.ofNat I.header.timestamp, ⟨4319⟩,
        kickRuntimeIdWord σ I, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩ (relyAuthHashMem I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, kickRuntimeAfterGuyMap I.codeOwner σ I) k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨4319⟩
      [kickRuntimeAddWord I.codeOwner σ I, kickRuntimeIdWord σ I, kickBidWord I,
        kickLotWord I, ⟨313⟩, sel]
      (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩ (relyAuthHashMem I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, kickRuntimeAfterGuyMap I.codeOwner σ I) k' C' := by
  let tau := kickRuntimeTauWord I.codeOwner σ I
  let timestamp := UInt256.ofNat I.header.timestamp
  let addWord := kickRuntimeAddWord I.codeOwner σ I
  let id := kickRuntimeIdWord σ I
  let memStore := twoWordHashMem id ⟨1⟩ (relyAuthHashMem I)
  let σGuy := kickRuntimeAfterGuyMap I.codeOwner σ I
  have rd4940 := evm_run h with [
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
  have rd4319 := rd4935.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa [timestamp, tau, addWord, kickRuntimeAddWord, id, memStore, σGuy] using
      rd4319⟩

set_option maxHeartbeats 1000000 in
theorem flapperKickX_endAddOverflow {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
        (kickRuntimeTauWord I.codeOwner σ I).toNat)
    (h : RD flapperBytecode I g s0 ⟨4936⟩
      [kickRuntimeTauWord I.codeOwner σ I, UInt256.ofNat I.header.timestamp, ⟨4319⟩,
        kickRuntimeIdWord σ I, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩ (relyAuthHashMem I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, kickRuntimeAfterGuyMap I.codeOwner σ I) k C) :
    RDrev flapperBytecode g s0 := by
  let tau := kickRuntimeTauWord I.codeOwner σ I
  let timestamp := UInt256.ofNat I.header.timestamp
  have rd4940 := evm_run h with [
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
    simpa [tau] using kickRuntimeTauWord_lt I.codeOwner σ I
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
theorem flapperKickX_toMoveSetupStart {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} (hperm : I.perm = true)
    (h : RD flapperBytecode I g s0 ⟨4319⟩
      [kickRuntimeAddWord I.codeOwner σ I, kickRuntimeIdWord σ I, kickBidWord I,
        kickLotWord I, ⟨313⟩, sel]
      (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩ (relyAuthHashMem I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, kickRuntimeAfterGuyMap I.codeOwner σ I) k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨4379⟩
      [flapperSlotWord ⟨2⟩ (kickRuntimeBeforeMoveMap I.codeOwner σ I) I,
        ⟨0⟩, ⟨64⟩, kickRuntimeIdWord σ I, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩
        (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩ (relyAuthHashMem I)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, kickRuntimeBeforeMoveMap I.codeOwner σ I) k' C' := by
  let id := kickRuntimeIdWord σ I
  let memStore := twoWordHashMem id ⟨1⟩ (relyAuthHashMem I)
  let memEndStore := twoWordHashMem id ⟨1⟩ memStore
  let σGuy := kickRuntimeAfterGuyMap I.codeOwner σ I
  let σBeforeMove := kickRuntimeBeforeMoveMap I.codeOwner σ I
  let addWord := kickRuntimeAddWord I.codeOwner σ I
  let base := solcMappingSlot ⟨1⟩ id
  let packedSlot := auctionPackedSlot id
  let oldPacked := solcSlotWord σGuy I packedSlot
  have rd4323pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd4325 := rd4323pre.mstore 0 (wordAt0Mem id memStore) (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memStore, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd4329pre := evm_run rd4325 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd4330 := rd4329pre.mstore 0 memEndStore (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memEndStore, memStore, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd4333pre := evm_run rd4330 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memEndStore.readWithPadding 0 64))) = base := by
    simpa [base, memEndStore, memStore, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStore
  have rd4335 := rd4333pre.keccak256 0 base (UInt256.ofNat 3)
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
  have rd4339pre := evm_run rd4335 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpackedSlot : ⟨2⟩ + base = packedSlot := by
    rw [u256_add_comm]
    simp [packedSlot, base, auctionPackedSlot_eq, id]
  rw [hpackedSlot] at rd4339pre
  have rd4340 := rd4339pre.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k4342, C4342, rd4342raw⟩ := rd4340.sload
    (by native_decide) (by evm_ov)
  have rd4342 : RD flapperBytecode I g s0 ⟨4342⟩
      [oldPacked, packedSlot, ⟨2⟩, ⟨64⟩, ⟨0⟩, addWord, id, kickBidWord I,
        kickLotWord I, ⟨313⟩, sel]
      memEndStore (UInt256.ofNat 3) ByteArray.empty (cA, σGuy) k4342 C4342 := by
    simpa [oldPacked, packedSlot, solcSlotWord, addWord] using rd4342raw
  have rd4349pre := rd4342.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4376pre := evm_run rd4349pre with [
    raw swap6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
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
    raw swap6 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw or (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov)]
  obtain ⟨k4377, C4377, rd4377raw⟩ := rd4376pre.sstore hperm
    (by native_decide) (by evm_ov)
  have hpc4377 :
      (⟨4342⟩ : UInt256) + UInt256.ofNat 7 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨4377⟩ := by
    native_decide
  rw [hpc4377] at rd4377raw
  have hstoredRaw :
      UInt256.lor
          (UInt256.land oldPacked
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩) ⟨1⟩))
          (UInt256.mul (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)
            (UInt256.land flapperUint48Mask addWord)) =
        setUint48Offset26Word oldPacked addWord := by
    simpa [tickRuntimeEndStoredRawWord, tickRuntimeEndShiftedWord,
      tickRuntimeEndClearMask, Sub.sub, HSub.hSub, Mul.mul, HMul.hMul]
      using tickRuntimeEndStoredRawWord_eq_setUint48Offset26Word oldPacked addWord
  rw [hstoredRaw] at rd4377raw
  have rd4377 : RD flapperBytecode I g s0 ⟨4377⟩
      [⟨64⟩, ⟨0⟩, ⟨2⟩, id, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      memEndStore (UInt256.ofNat 3) ByteArray.empty (cA, σBeforeMove) k4377 C4377 := by
    simpa [σBeforeMove, kickRuntimeBeforeMoveMap, kickRuntimeEndStoredWord,
      σGuy, oldPacked, packedSlot, addWord, hstoredRaw, tickRuntimeEndStoredRawWord,
      tickRuntimeEndShiftedWord, tickRuntimeEndClearMask, id] using rd4377raw
  have rd4378 := rd4377.swap2 (by native_decide) (by evm_ov)
  obtain ⟨k4379, C4379, rd4379raw⟩ := rd4378.sload (by native_decide) (by evm_ov)
  have rd4379 : RD flapperBytecode I g s0 ⟨4379⟩
      [flapperSlotWord ⟨2⟩ σBeforeMove I, ⟨0⟩, ⟨64⟩, id, kickBidWord I,
        kickLotWord I, ⟨313⟩, sel]
      memEndStore (UInt256.ofNat 3) ByteArray.empty (cA, σBeforeMove) k4379 C4379 := by
    simpa [flapperSlotWord] using rd4379raw
  exact ⟨_, _, by
    simpa [id, memStore, memEndStore, σBeforeMove] using rd4379⟩

set_option maxHeartbeats 1000000 in
theorem flapperKickX_toMoveExtcodesizeGuard {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (h : RD flapperBytecode I g s0 ⟨4379⟩
      [flapperSlotWord ⟨2⟩ (kickRuntimeBeforeMoveMap I.codeOwner σ I) I,
        ⟨0⟩, ⟨64⟩, kickRuntimeIdWord σ I, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩
        (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩ (relyAuthHashMem I)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, kickRuntimeBeforeMoveMap I.codeOwner σ I) k C) :
    let id := kickRuntimeIdWord σ I
    let memStore := twoWordHashMem id ⟨1⟩ (relyAuthHashMem I)
    let memEndStore := twoWordHashMem id ⟨1⟩ memStore
    let σBeforeMove := kickRuntimeBeforeMoveMap I.codeOwner σ I
    let vat := kickVatWord σBeforeMove I
    ∃ k' C', RD flapperBytecode I g s0 ⟨4446⟩
      (vat :: vat :: cageMoveOutSize :: cageMoveOutPtr :: cageMoveInSize ::
        cageMoveOutPtr :: cageMoveOutSize :: cageMoveEndPtr :: cageMoveSelectorWord ::
        vat :: id :: kickBidWord I :: kickLotWord I :: ⟨313⟩ :: sel :: [])
      (cageMoveCalldataMem (kickSenderWord I) (kickThisWord I) (kickLotWord I)
        memEndStore)
      (UInt256.ofNat 8) ByteArray.empty (cA, σBeforeMove) k' C' := by
  intro id memStore memEndStore σBeforeMove vat
  let rawVat := flapperSlotWord ⟨2⟩ σBeforeMove I
  let src := kickSenderWord I
  let guy := kickThisWord I
  let rad := kickLotWord I
  have hmemStore : memStore.size = 96 := by
    simpa [memStore, id] using
      twoWordHashMem_size_96 (kickRuntimeIdWord σ I) ⟨1⟩ (relyAuthHashMem_size I)
  have hread64Store :
      memStore.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memStore, id] using
      twoWordHashMem_read64 (kickRuntimeIdWord σ I) ⟨1⟩
        (relyAuthHashMem_size I) (relyAuthHashMem_read64 I)
  have hmemEnd : memEndStore.size = 96 := by
    simpa [memEndStore, memStore, id] using
      twoWordHashMem_size_96 id ⟨1⟩ hmemStore
  have hread64End :
      memEndStore.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memEndStore, memStore, id] using
      twoWordHashMem_read64 id ⟨1⟩ hmemStore hread64Store
  have hmload64End :
      (if (⟨64⟩ : UInt256).toNat ≥ memEndStore.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (memEndStore.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemEnd]; decide) (by decide) hread64End
  have hcallMem :
      (cageMoveCalldataMem src guy rad memEndStore).size = 228 := by
    simpa [cageMoveCalldataMem, src, guy, rad, memEndStore] using
      Benchmarks.Dss.Flopper.dentMoveCalldataMem_size src guy rad hmemEnd
  have hcallRead64 :
      (cageMoveCalldataMem src guy rad memEndStore).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    simpa [cageMoveCalldataMem, src, guy, rad, memEndStore] using
      Benchmarks.Dss.Flopper.dentMoveCalldataMem_read64 src guy rad hmemEnd hread64End
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (cageMoveCalldataMem src guy rad memEndStore).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((cageMoveCalldataMem src guy rad memEndStore).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have rd4446 := evm_run h with [
    raw dup3 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64End (by decide) (by evm_ov),
    raw push4 cageMoveSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (Benchmarks.Dss.Flopper.dentMoveSelectorMem memEndStore)
      (UInt256.ofNat 5) (by native_decide) mem_cost
      (by rfl) (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (Benchmarks.Dss.Flopper.dentMoveSrcMem src memEndStore)
      (UInt256.ofNat 6) (by native_decide) mem_cost
      (by
        simp [Benchmarks.Dss.Flopper.dentMoveSrcMem, src, kickSenderWord,
          show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 from by native_decide])
      (by native_decide) (by evm_ov),
    raw address (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (Benchmarks.Dss.Flopper.dentMoveGuyMem src guy memEndStore)
      (UInt256.ofNat 7) (by native_decide) mem_cost
      (by
        simp [Benchmarks.Dss.Flopper.dentMoveGuyMem, src, guy, kickThisWord,
          show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 (cageMoveCalldataMem src guy rad memEndStore) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 cageMoveSelectorWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 cageMoveInSize (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hpc4446 :
      (⟨4379⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨4446⟩ := by
    native_decide
  rw [hpc4446] at rd4446
  exact ⟨_, _, by
    simpa [vat, rawVat, src, guy, rad, id, memStore, memEndStore, σBeforeMove,
      kickVatWord, kickSenderWord, kickThisWord, flapperAddressReturnWord,
      flapperSlotWord, cageMoveCalldataMem, cageMoveSelectorWord, cageMoveOutPtr,
      cageMoveOutSize, cageMoveInSize, cageMoveEndPtr,
      Benchmarks.Dss.Flopper.dentMoveSelectorMem,
      Benchmarks.Dss.Flopper.dentMoveSrcMem,
      Benchmarks.Dss.Flopper.dentMoveGuyMem,
      Benchmarks.Dss.Flopper.dentMoveCalldataMem,
      Benchmarks.Dss.Flopper.dentMoveSelectorShifted,
      Benchmarks.Dss.Flopper.dentMoveSelectorWord,
      Benchmarks.Dss.Flopper.dentMoveOutPtr,
      Benchmarks.Dss.Flopper.dentMoveOutSize,
      Benchmarks.Dss.Flopper.dentMoveInSize,
      Benchmarks.Dss.Flopper.dentMoveEndPtr,
      solcAddrMask, u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + cageMoveInSize =
        cageMoveInSize from by native_decide,
      show (⟨128⟩ : UInt256) + cageMoveInSize = cageMoveEndPtr from by native_decide,
      show cageMoveInSize + cageMoveOutPtr = cageMoveEndPtr from by native_decide]
      using rd4446⟩

theorem RD.flapperKickReturnWordFromMem8 {cA σ I} {g : Sat256} {s0 : State}
    {sel id : UInt256} {mem memout rdata : ByteArray} {k C : ℕ}
    (h : RD flapperBytecode I g s0 ⟨313⟩ [id, sel] mem (UInt256.ofNat 8) rdata
      (cA, σ) k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hmemout : (UInt256.toByteArray id).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray id) :
    RDret flapperBytecode g s0 (cA, σ) (UInt256.toByteArray id) := by
  exact evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mstore 0 memout (UInt256.ofNat 8) (by native_decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmemoutLoad64 (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw ret 0 (UInt256.toByteArray id) (by native_decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

theorem flapperKickX_moveNoCode
    {cA gh bl σStart σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord (kickRuntimeBeforeMoveMap I.codeOwner σ I)
        (kickVatWord (kickRuntimeBeforeMoveMap I.codeOwner σ I) I) = ⟨0⟩)
    (rd4379 : RD flapperBytecode I g (initState cA gh bl σStart σ₀ g A I) ⟨4379⟩
      [flapperSlotWord ⟨2⟩ (kickRuntimeBeforeMoveMap I.codeOwner σ I) I,
        ⟨0⟩, ⟨64⟩, kickRuntimeIdWord σ I, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩
        (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩ (relyAuthHashMem I)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, kickRuntimeBeforeMoveMap I.codeOwner σ I) k C) :
    RDrev flapperBytecode g (initState cA gh bl σStart σ₀ g A I) := by
  obtain ⟨_, _, rd4446⟩ := flapperKickX_toMoveExtcodesizeGuard rd4379
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4446⟩) (okPc := ⟨4458⟩)
    rd4446 hnoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem flapperKickX_moveCall
    {cA gh bl σStart σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord (kickRuntimeBeforeMoveMap I.codeOwner σ I)
        (kickVatWord (kickRuntimeBeforeMoveMap I.codeOwner σ I) I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd4379 : RD flapperBytecode I g (initState cA gh bl σStart σ₀ g A I) ⟨4379⟩
      [flapperSlotWord ⟨2⟩ (kickRuntimeBeforeMoveMap I.codeOwner σ I) I,
        ⟨0⟩, ⟨64⟩, kickRuntimeIdWord σ I, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩
        (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩ (relyAuthHashMem I)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, kickRuntimeBeforeMoveMap I.codeOwner σ I) k C) :
    let id := kickRuntimeIdWord σ I
    let memStore := twoWordHashMem id ⟨1⟩ (relyAuthHashMem I)
    let memEndStore := twoWordHashMem id ⟨1⟩ memStore
    let σBeforeMove := kickRuntimeBeforeMoveMap I.codeOwner σ I
    let src := kickSenderWord I
    let guy := kickThisWord I
    let rad := kickLotWord I
    let vat := kickVatWord σBeforeMove I
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flapperBytecode I g (initState cA gh bl σStart σ₀ g A I) ⟨4462⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: cageMoveEndPtr :: cageMoveSelectorWord ::
          vat :: id :: kickBidWord I :: kickLotWord I :: ⟨313⟩ :: sel :: [])
        (cageMoveCalldataMem src guy rad memEndStore) (UInt256.ofNat 8)
        out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        ({ initState cA gh bl σStart σ₀ g A I with accountMap := σBeforeMove })
        (EVM.address (AccountAddress.ofNat vat.toNat)) "move" 0
        [.address I.source, .address I.codeOwner, .int (Int.ofNat rad.toNat)]
        (z,
          { { initState cA gh bl σStart σ₀ g A I with accountMap := σBeforeMove } with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  intro id memStore memEndStore σBeforeMove src guy rad vat
  have hmemStore : memStore.size = 96 := by
    simpa [memStore, id] using
      twoWordHashMem_size_96 (kickRuntimeIdWord σ I) ⟨1⟩ (relyAuthHashMem_size I)
  have hread64Store :
      memStore.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memStore, id] using
      twoWordHashMem_read64 (kickRuntimeIdWord σ I) ⟨1⟩
        (relyAuthHashMem_size I) (relyAuthHashMem_read64 I)
  have hmemEnd : memEndStore.size = 96 := by
    simpa [memEndStore, memStore, id] using
      twoWordHashMem_size_96 id ⟨1⟩ hmemStore
  have hsrcCanon : src.toNat < EVM.addressModulus := by
    simpa [src, kickSenderWord, solcSourceWord] using solcSourceWord_canonical I
  have hguyCanon : guy.toNat < EVM.addressModulus := by
    have hsize : AccountAddress.size < UInt256.size := by decide
    have hval : (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val := by
      rw [UInt256.toNat_ofNat_of_lt (lt_trans I.codeOwner.isLt hsize)]
    rw [show guy = UInt256.ofNat I.codeOwner.val by rfl, hval]
    exact I.codeOwner.isLt
  have hsrcAddr : AccountAddress.ofNat src.toNat = I.source := by
    simpa [src, kickSenderWord, solcSourceWord] using solcSource_ofNat I
  have hguyAddr : AccountAddress.ofNat guy.toNat = I.codeOwner := by
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
    simpa [guy, kickThisWord] using accountAddress_roundtrip I.codeOwner
  obtain ⟨_, _, rd4446⟩ := flapperKickX_toMoveExtcodesizeGuard rd4379
  obtain ⟨gasWord, _, _, rd4461⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4446⟩) (okPc := ⟨4458⟩) rd4446
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA', σ', z, out, A_in, callGas, k4462, C4462, hΘpack, rd4462raw,
      houtsz⟩ :=
    RD.call rd4461 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k4462, C4462, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          cageMoveOutPtr.toNat cageMoveInSize.toNat)
          cageMoveOutPtr.toNat cageMoveOutSize.toNat) = UInt256.ofNat 8 := by
      unfold cageMoveOutPtr cageMoveInSize cageMoveOutSize
      native_decide
    have hmin : (min cageMoveOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold cageMoveOutSize
      rfl
    have rd4462 : RD flapperBytecode I g (initState cA gh bl σStart σ₀ g A I) ⟨4462⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: cageMoveEndPtr :: cageMoveSelectorWord ::
          vat :: id :: kickBidWord I :: kickLotWord I :: ⟨313⟩ :: sel :: [])
        (out.write 0 (cageMoveCalldataMem src guy rad memEndStore)
          cageMoveOutPtr.toNat (min cageMoveOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k4462 C4462 :=
      haw ▸ rd4462raw
    rw [hmin, byteArray_write_len_zero] at rd4462
    exact rd4462
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := vat)
      (mem := cageMoveCalldataMem src guy rad memEndStore)
      (inOff := cageMoveOutPtr) (inSize := cageMoveInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      Benchmarks.Dss.Flopper.flopperAddressWord_address_eq_target
      ?_ ?_
    · simpa [hsrcAddr, hguyAddr] using
        cageMoveEncode_eq src guy rad hmemEnd hsrcCanon hguyCanon
    · simpa [initState, hperm] using hΘ

theorem flapperKickX_moveCallDepthLimit
    {cA gh bl σStart σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord (kickRuntimeBeforeMoveMap I.codeOwner σ I)
        (kickVatWord (kickRuntimeBeforeMoveMap I.codeOwner σ I) I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (rd4379 : RD flapperBytecode I g (initState cA gh bl σStart σ₀ g A I) ⟨4379⟩
      [flapperSlotWord ⟨2⟩ (kickRuntimeBeforeMoveMap I.codeOwner σ I) I,
        ⟨0⟩, ⟨64⟩, kickRuntimeIdWord σ I, kickBidWord I, kickLotWord I, ⟨313⟩, sel]
      (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩
        (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩ (relyAuthHashMem I)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, kickRuntimeBeforeMoveMap I.codeOwner σ I) k C) :
    let id := kickRuntimeIdWord σ I
    let memStore := twoWordHashMem id ⟨1⟩ (relyAuthHashMem I)
    let memEndStore := twoWordHashMem id ⟨1⟩ memStore
    let σBeforeMove := kickRuntimeBeforeMoveMap I.codeOwner σ I
    let src := kickSenderWord I
    let guy := kickThisWord I
    let rad := kickLotWord I
    let vat := kickVatWord σBeforeMove I
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σStart σ₀ g A I) ⟨4462⟩
      (⟨0⟩ :: cageMoveEndPtr :: cageMoveSelectorWord ::
        vat :: id :: kickBidWord I :: kickLotWord I :: ⟨313⟩ :: sel :: [])
      (cageMoveCalldataMem src guy rad memEndStore) (UInt256.ofNat 8)
      ByteArray.empty (cA, σBeforeMove) k' C' := by
  intro id memStore memEndStore σBeforeMove src guy rad vat
  obtain ⟨_, _, rd4446⟩ := flapperKickX_toMoveExtcodesizeGuard rd4379
  obtain ⟨gasWord, _, _, rd4461⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4446⟩) (okPc := ⟨4458⟩) rd4446
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨k4462, C4462, rd4462raw⟩ :=
    RD.callDepthLimit rd4461 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k4462, C4462, ?_⟩
  have hmin : (min cageMoveOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold cageMoveOutSize
    rfl
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        cageMoveOutPtr.toNat cageMoveInSize.toNat)
        cageMoveOutPtr.toNat cageMoveOutSize.toNat) = UInt256.ofNat 8 := by
    unfold cageMoveOutPtr cageMoveInSize cageMoveOutSize
    native_decide
  simpa [cageMoveOutPtr, cageMoveInSize, cageMoveOutSize, hmin,
    byteArray_write_len_zero, haw] using rd4462raw

theorem flapperKickX_moveCallFailure
    {cA gh bl σStart σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd4462 : RD flapperBytecode I g (initState cA gh bl σStart σ₀ g A I) ⟨4462⟩
      (⟨0⟩ :: cageMoveEndPtr :: cageMoveSelectorWord ::
        kickVatWord (kickRuntimeBeforeMoveMap I.codeOwner σ I) I ::
        kickRuntimeIdWord σ I :: kickBidWord I :: kickLotWord I :: ⟨313⟩ :: sel :: [])
      mem aw out (cA', σ') k C)
    (houtSize : out.size < UInt256.size) :
    RDrev flapperBytecode g (initState cA gh bl σStart σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨4462⟩) (okPc := ⟨4478⟩) rd4462
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtSize (by simp)

set_option maxHeartbeats 1000000 in
theorem flapperKickX_moveCallSuccess
    {cA gh bl σStart σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (rd4462 : RD flapperBytecode I g (initState cA gh bl σStart σ₀ g A I) ⟨4462⟩
      (⟨1⟩ :: cageMoveEndPtr :: cageMoveSelectorWord ::
        kickVatWord (kickRuntimeBeforeMoveMap I.codeOwner σ I) I ::
        kickRuntimeIdWord σ I :: kickBidWord I :: kickLotWord I :: ⟨313⟩ :: sel :: [])
      (cageMoveCalldataMem (kickSenderWord I) (kickThisWord I) (kickLotWord I)
        (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩
          (twoWordHashMem (kickRuntimeIdWord σ I) ⟨1⟩ (relyAuthHashMem I))))
      (UInt256.ofNat 8) out (cA', σ') k C) :
    RDret flapperBytecode g (initState cA gh bl σStart σ₀ g A I)
      (cA', σ') (UInt256.toByteArray (kickRuntimeIdWord σ I)) := by
  let id := kickRuntimeIdWord σ I
  let memStore := twoWordHashMem id ⟨1⟩ (relyAuthHashMem I)
  let memEndStore := twoWordHashMem id ⟨1⟩ memStore
  let memCall := cageMoveCalldataMem (kickSenderWord I) (kickThisWord I) (kickLotWord I)
    memEndStore
  let memEvent0 := writeWord memCall 128 id
  let memEvent1 := writeWord memEvent0 160 (kickLotWord I)
  let memEvent := Benchmarks.Dss.Flopper.kickEventMem memCall id (kickLotWord I)
    (kickBidWord I)
  have hmemStore : memStore.size = 96 := by
    simpa [memStore, id] using
      twoWordHashMem_size_96 (kickRuntimeIdWord σ I) ⟨1⟩ (relyAuthHashMem_size I)
  have hread64Store :
      memStore.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memStore, id] using
      twoWordHashMem_read64 (kickRuntimeIdWord σ I) ⟨1⟩
        (relyAuthHashMem_size I) (relyAuthHashMem_read64 I)
  have hmemEnd : memEndStore.size = 96 := by
    simpa [memEndStore, memStore, id] using
      twoWordHashMem_size_96 id ⟨1⟩ hmemStore
  have hread64End :
      memEndStore.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memEndStore, memStore, id] using
      twoWordHashMem_read64 id ⟨1⟩ hmemStore hread64Store
  have hcallMem : memCall.size = 228 := by
    simpa [memCall, cageMoveCalldataMem, memEndStore] using
      Benchmarks.Dss.Flopper.dentMoveCalldataMem_size
        (kickSenderWord I) (kickThisWord I) (kickLotWord I) hmemEnd
  have hcallRead64 :
      memCall.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memCall, cageMoveCalldataMem, memEndStore] using
      Benchmarks.Dss.Flopper.dentMoveCalldataMem_read64
        (kickSenderWord I) (kickThisWord I) (kickLotWord I) hmemEnd hread64End
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ memCall.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memCall.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have hmemEventSize : memEvent.size = 228 := by
    simpa [memEvent, Benchmarks.Dss.Flopper.kickEventMem] using
      writeCascade_size_of_base memCall
        [(128, id), (160, kickLotWord I), (192, kickBidWord I)]
        (base := 228) (out := 228) hcallMem
        (by simp [WriteGapsOk]; all_goals exact lt_usize _ (by norm_num))
        (by simp)
  have hread64Event :
      memEvent.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    have hpres :
        memEvent.readWithPadding 64 32 = memCall.readWithPadding 64 32 := by
      simpa [memEvent, Benchmarks.Dss.Flopper.kickEventMem] using
        writeCascade_read_preserved_of_base memCall
          [(128, id), (160, kickLotWord I), (192, kickBidWord I)]
          (base := 228) (read := 64) hcallMem
          (by simp [WindowDisjointFromWrites]; all_goals exact lt_usize _ (by norm_num))
    rw [hpres]
    exact hcallRead64
  have hmload64Event :
      (if (⟨64⟩ : UInt256).toNat ≥ memEvent.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memEvent.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemEventSize]; decide) (by decide) hread64Event
  have hreturnMemSize :
      ((UInt256.toByteArray id).write 0 memEvent 128 32).size = 228 := by
    exact toByteArray_write32_size_of_le memEvent id 128 228 228 hmemEventSize
      (by rw [hmemEventSize]; omega) (by native_decide)
  have hreturnRead64 :
      ((UInt256.toByteArray id).write 0 memEvent 128 32).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    rw [toByteArray_write_read_below_of_gap id memEvent 128 64
      (by rw [hmemEventSize]; omega)
      (by omega)
      (by rw [hmemEventSize]; exact lt_usize _ (by norm_num))]
    exact hread64Event
  have hmload64Return :
      (if (⟨64⟩ : UInt256).toNat ≥
            ((UInt256.toByteArray id).write 0 memEvent 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (((UInt256.toByteArray id).write 0 memEvent 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hreturnMemSize]; decide) (by decide) hreturnRead64
  have hread128 :
      ((UInt256.toByteArray id).write 0 memEvent 128 32).readWithPadding 128 32 =
        UInt256.toByteArray id :=
    toByteArray_write32_read_back memEvent id 128 (by rw [hmemEventSize]; omega)
  obtain ⟨k4480, C4480, rd4480raw⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨4462⟩) (okPc := ⟨4478⟩) rd4462
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4480 : RD flapperBytecode I g (initState cA gh bl σStart σ₀ g A I) ⟨4480⟩
      (cageMoveEndPtr :: cageMoveSelectorWord ::
        kickVatWord (kickRuntimeBeforeMoveMap I.codeOwner σ I) I ::
        id :: kickBidWord I :: kickLotWord I :: ⟨313⟩ :: sel :: [])
      memCall (UInt256.ofNat 8) out (cA', σ') k4480 C4480 := by
    simpa [id, memStore, memEndStore, memCall,
      show ((⟨4478⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = ⟨4480⟩ from by native_decide]
      using rd4480raw
  have rd4486pre := evm_run rd4480 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd4488 := rd4486pre.mstore 0 memEvent0 (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by rfl)
    (by native_decide)
    (by evm_ov)
  have rd4493pre := evm_run rd4488 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd4495 := rd4493pre.mstore 0 memEvent1 (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by rfl)
    (by native_decide)
    (by evm_ov)
  have rd4499pre := evm_run rd4495 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd4501 := rd4499pre.mstore 0 memEvent (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by rfl)
    (by native_decide)
    (by evm_ov)
  have rd4503 := evm_run rd4501 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Event (by decide) (by evm_ov)]
  let kickTopic : UInt256 :=
    ⟨104424013100931708726487002035509548663885731725515407419183104423543863039497⟩
  have rd4536 := rd4503.pushConst kickTopic (width := 32) (op := .PUSH32)
    (by decide : Operation.POp.PUSH32 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4547 := evm_run rd4536 with [
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨96⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd4548 := RD.log1 0 (UInt256.ofNat 8) rd4547 (by native_decide) hperm
    mem_cost (by decide)
    (by
      simp only [List.length_cons, List.length_nil]
      omega)
  have rd313 := evm_run rd4548 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact RD.flapperKickReturnWordFromMem8 rd313 hmload64Event (by rfl) hmload64Return hread128

theorem kickRuntimeIdWord_source_eq
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    kickRuntimeIdWord σ_evm I =
      kickIdWord (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hslot := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨6⟩
  simpa [kickRuntimeIdWord, kickIdWord, kickKicksWord, evmSolm, initState, hslot]

theorem kickRuntimeAfterFillMap_source_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (kickRuntimeAfterFillMap I.codeOwner σ_evm I)
      (kickAfterFillState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hfill :
      flapperSlotWord ⟨9⟩ σ_evm I + kickLotWord I = kickFillNewWord evmSolm I := by
    have hslot := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨9⟩
    simpa [kickFillNewWord, kickFillWord, evmSolm, initState, hslot]
  simpa [evmSolm, initState, storageStore_accountMap, kickAfterFillState,
    kickRuntimeAfterFillMap, hfill] using
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨9⟩
      (flapperSlotWord ⟨9⟩ σ_evm I + kickLotWord I) hAccounts

theorem kickRuntimeAfterKicksMap_source_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (kickRuntimeAfterKicksMap I.codeOwner σ_evm I)
      (kickAfterKicksState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hAfter :=
    kickRuntimeAfterFillMap_source_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts
  have hid := kickRuntimeIdWord_source_eq
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hAccounts
  simpa [evmSolm, initState, storageStore_accountMap, kickAfterKicksState,
    kickAfterFillState_executionEnv, kickRuntimeAfterKicksMap, hid] using
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩
      (kickRuntimeIdWord σ_evm I) hAfter

theorem kickRuntimeAfterBidMap_source_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (kickRuntimeAfterBidMap I.codeOwner σ_evm I)
      (kickAfterBidState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hAfter :=
    kickRuntimeAfterKicksMap_source_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts
  have hid := kickRuntimeIdWord_source_eq
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hAccounts
  simpa [evmSolm, initState, storageStore_accountMap, kickAfterBidState,
    kickAfterKicksState_executionEnv, kickRuntimeAfterBidMap, hid] using
    accountMapEquiv_sstoreAccountMap I.codeOwner
      (auctionBidSlot (kickRuntimeIdWord σ_evm I)) (kickBidWord I) hAfter

theorem kickRuntimeAfterLotMap_source_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (kickRuntimeAfterLotMap I.codeOwner σ_evm I)
      (kickAfterLotState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hAfter :=
    kickRuntimeAfterBidMap_source_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts
  have hid := kickRuntimeIdWord_source_eq
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hAccounts
  simpa [evmSolm, initState, storageStore_accountMap, kickAfterLotState,
    kickAfterBidState_executionEnv, kickRuntimeAfterLotMap, hid] using
    accountMapEquiv_sstoreAccountMap I.codeOwner
      (auctionLotSlot (kickRuntimeIdWord σ_evm I)) (kickLotWord I) hAfter

theorem kickRuntimeAfterGuyMap_source_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (kickRuntimeAfterGuyMap I.codeOwner σ_evm I)
      (kickAfterGuyState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (kickRuntimeIdWord σ_evm I)
  have hAfter :=
    kickRuntimeAfterLotMap_source_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts
  have hid := kickRuntimeIdWord_source_eq
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hAccounts
  have hold :
      solcSlotWord (kickRuntimeAfterLotMap I.codeOwner σ_evm I) I packedSlot =
        Solm.EVM.storageLoad (kickAfterLotState evmSolm I)
          (kickAfterLotState evmSolm I).executionEnv.codeOwner
          (auctionPackedSlot (kickIdWord evmSolm)) := by
    have hslot := flapperSlotWord_accountMapEquiv (I := I) hAfter packedSlot
    simpa [packedSlot, flapperSlotWord, solcSlotWord, evmSolm, initState,
      kickAfterLotState_executionEnv, hid] using hslot
  have hstored :
      kickRuntimeGuyStoredWord I.codeOwner σ_evm I = kickGuyStoredWord evmSolm I := by
    unfold kickRuntimeGuyStoredWord kickGuyStoredWord
    change
      setAddressOffset0Word
          (solcSlotWord (kickRuntimeAfterLotMap I.codeOwner σ_evm I) I packedSlot)
          (kickSenderWord I) =
        setAddressOffset0Word
          (Solm.EVM.storageLoad (kickAfterLotState evmSolm I)
            (kickAfterLotState evmSolm I).executionEnv.codeOwner
            (auctionPackedSlot (kickIdWord evmSolm)))
          (kickSenderWord I)
    rw [hold]
  simpa [evmSolm, initState, storageStore_accountMap, kickAfterGuyState,
    kickAfterLotState_executionEnv, kickRuntimeAfterGuyMap, packedSlot, hid, hstored] using
    accountMapEquiv_sstoreAccountMap I.codeOwner packedSlot
      (kickRuntimeGuyStoredWord I.codeOwner σ_evm I) hAfter

theorem kickRuntimeTauWord_source_eq
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    kickRuntimeTauWord I.codeOwner σ_evm I =
      kickTauWord
        (kickAfterGuyState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I) := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hAfter :=
    kickRuntimeAfterGuyMap_source_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts
  have h := flapperUint48Offset6Word_accountMapEquiv (I := I) hAfter ⟨5⟩
  simpa [evmSolm, kickRuntimeTauWord, kickTauWord, kickAfterGuyState_executionEnv,
    initState] using h

theorem kickRuntimeBeforeMoveMap_source_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hendFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
        (kickRuntimeTauWord I.codeOwner σ_evm I).toNat < 2 ^ 48) :
    accountMapEquiv (kickRuntimeBeforeMoveMap I.codeOwner σ_evm I)
      (kickAfterEndState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (kickRuntimeIdWord σ_evm I)
  let runtimeOld := solcSlotWord (kickRuntimeAfterGuyMap I.codeOwner σ_evm I) I packedSlot
  let runtimeAdd := kickRuntimeAddWord I.codeOwner σ_evm I
  have hid := kickRuntimeIdWord_source_eq
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hAccounts
  have hAfter :=
    kickRuntimeAfterGuyMap_source_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts
  have htau :=
    kickRuntimeTauWord_source_eq
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts
  have hendFitSolm :
      (kickNow48Word evmSolm).toNat +
          (kickTauWord (kickAfterGuyState evmSolm I)).toNat < 2 ^ 48 := by
    simpa [evmSolm, kickNow48Word, kickTimestampWord, initState, htau] using hendFit
  have hmaskedRuntime :
      UInt256.land runtimeAdd flapperUint48Mask = kickEndPostWord evmSolm I := by
    apply u256_inj
    change (UInt256.land (kickRuntimeAddWord I.codeOwner σ_evm I) flapperUint48Mask).toNat =
      (kickEndPostWord evmSolm I).toNat
    rw [kickRuntimeAddWord]
    rw [uint48Mask_add_no_wrap_toNat (UInt256.ofNat I.header.timestamp)
      (kickRuntimeTauWord I.codeOwner σ_evm I) hendFit]
    rw [kickEndPostWord_toNat evmSolm I hendFitSolm]
    simpa [evmSolm, kickNow48Word, kickTimestampWord, initState, htau]
  have hsourceClean :
      UInt256.land (kickEndPostWord evmSolm I) flapperUint48Mask =
        kickEndPostWord evmSolm I := by
    apply flapperUint48Mask_clean_of_canonical
    have hendNat := kickEndPostWord_toNat evmSolm I hendFitSolm
    rw [hendNat]
    simpa [EVM.twoPow] using hendFitSolm
  have hold :
      runtimeOld =
        Solm.EVM.storageLoad (kickAfterGuyState evmSolm I)
          (kickAfterGuyState evmSolm I).executionEnv.codeOwner
          (auctionPackedSlot (kickIdWord evmSolm)) := by
    have hslot := flapperSlotWord_accountMapEquiv (I := I) hAfter packedSlot
    simpa [runtimeOld, packedSlot, flapperSlotWord, solcSlotWord, evmSolm,
      initState, kickAfterGuyState_executionEnv, hid] using hslot
  have hstored :
      kickRuntimeEndStoredWord I.codeOwner σ_evm I = kickEndStoredWord evmSolm I := by
    unfold kickRuntimeEndStoredWord kickEndStoredWord
    change setUint48Offset26Word runtimeOld runtimeAdd =
      setUint48Offset26Word
        (Solm.EVM.storageLoad (kickAfterGuyState evmSolm I)
          (kickAfterGuyState evmSolm I).executionEnv.codeOwner
          (auctionPackedSlot (kickIdWord evmSolm)))
        (kickEndPostWord evmSolm I)
    apply u256_inj
    rw [setUint48Offset26Word_toNat, setUint48Offset26Word_toNat]
    rw [hold, hmaskedRuntime, hsourceClean]
  simpa [evmSolm, initState, storageStore_accountMap, kickAfterGuyState_executionEnv,
    packedSlot, runtimeOld, runtimeAdd, kickRuntimeBeforeMoveMap, kickAfterEndState,
    hstored, hid] using
    accountMapEquiv_sstoreAccountMap I.codeOwner packedSlot
      (kickRuntimeEndStoredWord I.codeOwner σ_evm I) hAfter

theorem flapperKickBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 8))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flapperSelBytes 8) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some kickTransition :=
    flapperDispatchKick hsel
  have hreach := flapperReachKickBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := flapperDecode_kick_ok (I := I) hsz68
    obtain ⟨_, _, rd3901⟩ :=
      flapperKickX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · obtain ⟨_, _, rd3994⟩ :=
        flapperKickX_authorized (g := Sat256.ofUInt256 g) hauth rd3901
      have hauthSolm :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
              (relyAuthStorageSlot I) = ⟨1⟩ := by
        have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
        have hsolm : relyAuthWord σ_solm I = ⟨1⟩ := by
          rw [← hword]
          exact hauth
        simpa [evmSolm, relyAuthWord, flapperSlotWord, initState,
          Solm.EVM.storageLoad, State.lookupAccount] using hsolm
      by_cases hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩
      · obtain ⟨_, _, rd4068⟩ :=
          flapperKickX_liveOk (g := Sat256.ofUInt256 g) hlive rd3994
        have hliveSolm : kickLiveWord evmSolm = ⟨1⟩ := by
          have hslot := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
          simpa [kickLiveWord, evmSolm, initState, hslot] using hlive
        by_cases hkicksLt : (flapperSlotWord ⟨6⟩ σ_evm I).toNat < UInt256.size - 1
        · obtain ⟨_, _, rd4143⟩ :=
            flapperKickX_kicksOk (g := Sat256.ofUInt256 g) hkicksLt rd4068
          have hkicksLtSolm : (kickKicksWord evmSolm).toNat < UInt256.size - 1 := by
            have hslot := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨6⟩
            simpa [kickKicksWord, evmSolm, initState, hslot] using hkicksLt
          by_cases hfillFit :
              (flapperSlotWord ⟨9⟩ σ_evm I).toNat + (kickLotWord I).toNat <
                UInt256.size
          · obtain ⟨_, _, rd4155⟩ :=
              flapperKickX_fillAddOk (g := Sat256.ofUInt256 g) hfillFit rd4143
            have hfillFitSolm :
                (kickFillWord evmSolm).toNat + (kickLotWord I).toNat < UInt256.size := by
              have hslot := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨9⟩
              simpa [kickFillWord, evmSolm, initState, hslot] using hfillFit
            have hfillWordAfter :
                kickFillWord (kickAfterFillState evmSolm I) =
                  flapperSlotWord ⟨9⟩ σ_evm I + kickLotWord I := by
              have hownerSome :
                  evmSolm.accountMap.find? evmSolm.executionEnv.codeOwner ≠ none := by
                intro howner
                have hload0 :
                    Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
                        (relyAuthStorageSlot I) = ⟨0⟩ := by
                  simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                    Option.option, howner]
                have hbad : (⟨0⟩ : UInt256) = ⟨1⟩ := by
                  simpa [hload0] using hauthSolm
                exact (by native_decide : (⟨0⟩ : UInt256) ≠ ⟨1⟩) hbad
              obtain ⟨_, hownerPresent⟩ := Option.ne_none_iff_exists'.mp hownerSome
              have hslot := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨9⟩
              have hloadFill :=
                storageLoad_storageStore_same_present evmSolm evmSolm.executionEnv.codeOwner
                  hownerPresent ⟨9⟩ (kickFillNewWord evmSolm I)
              have hloadFillSlot :
                  flapperSlotWord ⟨9⟩
                      (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                        ⟨9⟩ (kickFillNewWord evmSolm I)).accountMap
                      evmSolm.executionEnv =
                    kickFillNewWord evmSolm I := by
                simpa [flapperSlotWord, solcSlotWord, Solm.EVM.storageLoad,
                  State.lookupAccount, Account.lookupStorage] using hloadFill
              have hstoreExec :
                  (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                      ⟨9⟩ (kickFillNewWord evmSolm I)).executionEnv =
                    evmSolm.executionEnv :=
                storageStore_executionEnv evmSolm evmSolm.executionEnv.codeOwner
                  ⟨9⟩ (kickFillNewWord evmSolm I)
              change flapperSlotWord ⟨9⟩
                  (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                    ⟨9⟩ (kickFillNewWord evmSolm I)).accountMap
                  (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                    ⟨9⟩ (kickFillNewWord evmSolm I)).executionEnv =
                flapperSlotWord ⟨9⟩ σ_evm I + kickLotWord I
              rw [hstoreExec]
              simpa [kickFillNewWord, kickFillWord, evmSolm, initState, hslot]
                using hloadFillSlot
            have hAfterFill :=
              kickRuntimeAfterFillMap_source_accountMapEquiv
                (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
                (I := I) (g := g) hAccounts
            have hlidWordAfter :
                kickLidWord (kickAfterFillState evmSolm I) =
                  flapperSlotWord ⟨8⟩ (kickRuntimeAfterFillMap I.codeOwner σ_evm I) I := by
              have hslot := flapperSlotWord_accountMapEquiv (I := I) hAfterFill ⟨8⟩
              simpa [kickLidWord, evmSolm, initState, kickAfterFillState_executionEnv]
                using hslot.symm
            by_cases hfillLe :
                (flapperSlotWord ⟨9⟩ σ_evm I + kickLotWord I).toNat ≤
                  (flapperSlotWord ⟨8⟩ (kickRuntimeAfterFillMap I.codeOwner σ_evm I) I).toNat
            · obtain ⟨_, _, rd4233⟩ :=
                flapperKickX_lidOk (g := Sat256.ofUInt256 g) hperm hfillLe rd4155
              have hfillLeSolm :
                  (kickFillWord (kickAfterFillState evmSolm I)).toNat ≤
                    (kickLidWord (kickAfterFillState evmSolm I)).toNat := by
                simpa [hfillWordAfter, hlidWordAfter] using hfillLe
              obtain ⟨_, _, rd4936⟩ :=
                flapperKickX_toCheckedAddStart (g := Sat256.ofUInt256 g) hperm rd4233
              by_cases hendFit :
                  (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
                    (kickRuntimeTauWord I.codeOwner σ_evm I).toNat < 2 ^ 48
              · obtain ⟨_, _, rd4319⟩ :=
                  flapperKickX_toEndStoreStart (g := Sat256.ofUInt256 g) hendFit rd4936
                obtain ⟨_, _, rd4379⟩ :=
                  flapperKickX_toMoveSetupStart (g := Sat256.ofUInt256 g) hperm rd4319
                have htau :=
                  kickRuntimeTauWord_source_eq
                    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
                    (I := I) (g := g) hAccounts
                have hendFitSolm :
                    (kickNow48Word evmSolm).toNat +
                        (kickTauWord (kickAfterGuyState evmSolm I)).toNat < 2 ^ 48 := by
                  simpa [evmSolm, kickNow48Word, kickTimestampWord, initState, htau]
                    using hendFit
                have hBeforeAccounts :=
                  kickRuntimeBeforeMoveMap_source_accountMapEquiv
                    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
                    (I := I) (g := g) hAccounts hendFit
                by_cases hnoCode :
                    Reasoning.Theory.extCodeSizeWord
                      (kickRuntimeBeforeMoveMap I.codeOwner σ_evm I)
                      (kickVatWord (kickRuntimeBeforeMoveMap I.codeOwner σ_evm I) I) =
                        ⟨0⟩
                · have hnoCodeSolm :
                      Reasoning.Theory.extCodeSizeWord
                          (kickAfterEndState evmSolm I).accountMap
                          (kickVatWord (kickAfterEndState evmSolm I).accountMap
                            (kickAfterEndState evmSolm I).executionEnv) = ⟨0⟩ := by
                    simpa [kickVatWord, kickAfterEndState_executionEnv] using
                      flapperCodeSize_zero_accountMapEquiv_addressSlot
                        hBeforeAccounts ⟨2⟩ hnoCode
                  have hbody :
                      ExecTransitionBody config contract evmSolm (kickLocals I)
                        kickTransition.body .reverted := by
                    exact flapperKickBodyReverts_moveNoCode evmSolm I
                      (by simpa [evmSolm, initState] using hwv)
                      (by simp [evmSolm, initState])
                      hauthSolm hliveSolm hkicksLtSolm hfillFitSolm hfillLeSolm
                      hendFitSolm hnoCodeSolm
                  exact (flapperKickX_moveNoCode (g := Sat256.ofUInt256 g) hnoCode rd4379)
                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hcodeSize :
                      Reasoning.Theory.extCodeSizeWord
                        (kickRuntimeBeforeMoveMap I.codeOwner σ_evm I)
                        (kickVatWord (kickRuntimeBeforeMoveMap I.codeOwner σ_evm I) I) ≠
                          ⟨0⟩ := hnoCode
                  have hcodeSizeSolm :
                      Reasoning.Theory.extCodeSizeWord
                          (kickAfterEndState evmSolm I).accountMap
                          (kickVatWord (kickAfterEndState evmSolm I).accountMap
                            (kickAfterEndState evmSolm I).executionEnv) ≠ ⟨0⟩ := by
                    simpa [kickVatWord, kickAfterEndState_executionEnv] using
                      flapperCodeSize_ne_accountMapEquiv_addressSlot
                        hBeforeAccounts ⟨2⟩ hcodeSize
                  by_cases hdepthEq : I.depth = 1024
                  · let evmMoveSolm := kickAfterEndState evmSolm I
                    let vat := kickVatWord evmMoveSolm.accountMap evmMoveSolm.executionEnv
                    let src := kickSenderWord I
                    let guy := kickThisWord I
                    let rad := kickLotWord I
                    let memStore := twoWordHashMem (kickRuntimeIdWord σ_evm I) ⟨1⟩
                      (relyAuthHashMem I)
                    let memEndStore := twoWordHashMem (kickRuntimeIdWord σ_evm I) ⟨1⟩
                      memStore
                    let A_move := (evmMoveSolm.addAccessedAccount
                      (EVM.address (AccountAddress.ofNat vat.toNat))).substate
                    have hmemStore : memStore.size = 96 := by
                      simpa [memStore] using
                        twoWordHashMem_size_96 (kickRuntimeIdWord σ_evm I) ⟨1⟩
                          (relyAuthHashMem_size I)
                    have hmemEnd : memEndStore.size = 96 := by
                      have hreadStore :
                          memStore.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
                        simpa [memStore] using
                          twoWordHashMem_read64 (kickRuntimeIdWord σ_evm I) ⟨1⟩
                            (relyAuthHashMem_size I) (relyAuthHashMem_read64 I)
                      simpa [memEndStore] using
                        twoWordHashMem_size_96 (kickRuntimeIdWord σ_evm I) ⟨1⟩ hmemStore
                    have hsrcCanon : src.toNat < EVM.addressModulus := by
                      simpa [src, kickSenderWord, solcSourceWord] using
                        solcSourceWord_canonical I
                    have hguyCanon : guy.toNat < EVM.addressModulus := by
                      have hsizeAddr : AccountAddress.size < UInt256.size := by decide
                      have hval : (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val := by
                        rw [UInt256.toNat_ofNat_of_lt (lt_trans I.codeOwner.isLt hsizeAddr)]
                      rw [show guy = UInt256.ofNat I.codeOwner.val by rfl, hval]
                      exact I.codeOwner.isLt
                    have hsrcAddr : AccountAddress.ofNat src.toNat = I.source := by
                      simpa [src, kickSenderWord, solcSourceWord] using solcSource_ofNat I
                    have hguyAddr : AccountAddress.ofNat guy.toNat = I.codeOwner := by
                      rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
                      simpa [guy, kickThisWord] using accountAddress_roundtrip I.codeOwner
                    have hdepthMove : evmMoveSolm.executionEnv.depth = 1024 := by
                      simpa [evmMoveSolm, evmSolm, kickAfterEndState_executionEnv, initState]
                        using hdepthEq
                    have hcallSolm :
                        typedCallViaEVM config evmMoveSolm
                          (EVM.address (AccountAddress.ofNat vat.toNat)) "move" 0
                          [.address evmMoveSolm.executionEnv.source,
                            .address evmMoveSolm.executionEnv.codeOwner, kickLotValue I]
                          (false, { evmMoveSolm with substate := A_move }, ByteArray.empty)
                          true := by
                      simpa [evmMoveSolm, evmSolm, A_move, vat, src, guy, rad,
                        kickAfterEndState_executionEnv, initState, hsrcAddr, hguyAddr,
                        kickLotValue, kickLotWord] using
                        (callNotMade_depthLimit (cfg := config) (evm := evmMoveSolm)
                          (tgt := EVM.address (AccountAddress.ofNat vat.toNat))
                          (name := "move")
                          (args := [.address (AccountAddress.ofNat src.toNat),
                            .address (AccountAddress.ofNat guy.toNat),
                            .int (Int.ofNat rad.toNat)])
                          (callPerm := true)
                          (calldata := (cageMoveCalldataMem src guy rad memEndStore).readWithPadding
                            cageMoveOutPtr.toNat cageMoveInSize.toNat)
                          (cageMoveEncode_eq src guy rad hmemEnd hsrcCanon hguyCanon)
                          hdepthMove)
                    have hbody :
                        ExecTransitionBody config contract evmSolm (kickLocals I)
                          kickTransition.body .reverted := by
                      simpa [evmMoveSolm] using
                        flapperKickBodyReverts_moveCallFailure evmSolm
                          { evmMoveSolm with substate := A_move } I ByteArray.empty
                          (by simpa [evmSolm, initState] using hwv)
                          (by simp [evmSolm, initState])
                          hauthSolm hliveSolm hkicksLtSolm hfillFitSolm hfillLeSolm
                          hendFitSolm hcodeSizeSolm hcallSolm
                    obtain ⟨_, _, rd4462⟩ :=
                      flapperKickX_moveCallDepthLimit (g := Sat256.ofUInt256 g)
                        hcodeSize hdepthEq rd4379
                    exact (flapperKickX_moveCallFailure rd4462 (by native_decide))
                      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have hdepthLt : I.depth.val < 1024 := by
                      have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
                      by_contra hn
                      have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hn
                      have hval : I.depth.val = 1024 := by omega
                      apply hdepthEq
                      apply Fin.ext
                      exact hval
                    obtain ⟨cA', σ', z, out, A', k4462, C4462, rd4462, hcall,
                        houtSize⟩ :=
                      flapperKickX_moveCall (g := Sat256.ofUInt256 g) hperm hcodeSize
                        hdepthLt rd4379
                    let evmEvm : EVM.State :=
                      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := kickRuntimeBeforeMoveMap I.codeOwner σ_evm I }
                    let evmMoveSolm := kickAfterEndState evmSolm I
                    have hMoveAccounts :
                        accountMapEquiv evmEvm.accountMap evmMoveSolm.accountMap := by
                      simpa [evmEvm, evmMoveSolm] using hBeforeAccounts
                    obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hpostAccounts⟩ :=
                      typedCallViaEVM_accountMapEquiv (hcall := hcall) hMoveAccounts
                        (by simp [evmEvm, evmMoveSolm, evmSolm, kickAfterEndState,
                          kickAfterGuyState, kickAfterLotState, kickAfterBidState,
                          kickAfterKicksState, kickAfterFillState, initState,
                          cageStorageStore_sigma0])
                        (by simp [evmEvm, evmMoveSolm, evmSolm, kickAfterEndState,
                          kickAfterGuyState, kickAfterLotState, kickAfterBidState,
                          kickAfterKicksState, kickAfterFillState, initState,
                          storageStore_createdAccounts])
                        (by simp [evmEvm, evmMoveSolm, evmSolm, kickAfterEndState,
                          kickAfterGuyState, kickAfterLotState, kickAfterBidState,
                          kickAfterKicksState, kickAfterFillState, initState,
                          cageStorageStore_genesisBlockHeader])
                        (by simp [evmEvm, evmMoveSolm, evmSolm, kickAfterEndState,
                          kickAfterGuyState, kickAfterLotState, kickAfterBidState,
                          kickAfterKicksState, kickAfterFillState, initState,
                          cageStorageStore_blocks])
                        (by simp [evmEvm, evmMoveSolm, evmSolm, kickAfterEndState,
                          kickAfterGuyState, kickAfterLotState, kickAfterBidState,
                          kickAfterKicksState, kickAfterFillState, initState,
                          cageStorageStore_substate])
                        (by simp [evmEvm, evmMoveSolm, evmSolm, kickAfterEndState_executionEnv,
                          initState])
                    let evmCallSolm : EVM.State :=
                      { evmMoveSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
                    have hvatEq :
                        kickVatWord (kickRuntimeBeforeMoveMap I.codeOwner σ_evm I) I =
                          kickVatWord evmMoveSolm.accountMap evmMoveSolm.executionEnv := by
                      have hword :=
                        flapperAddressReturnWord_accountMapEquiv (I := I) hMoveAccounts ⟨2⟩
                      simpa [evmEvm, evmMoveSolm, kickVatWord, kickAfterEndState_executionEnv]
                        using hword
                    have hcallSolm :
                        typedCallViaEVM config evmMoveSolm
                          (EVM.address (AccountAddress.ofNat
                            (kickVatWord evmMoveSolm.accountMap
                              evmMoveSolm.executionEnv).toNat))
                          "move" 0
                          [.address evmMoveSolm.executionEnv.source,
                            .address evmMoveSolm.executionEnv.codeOwner, kickLotValue I]
                          (z, evmCallSolm, out) true := by
                      simpa [evmEvm, evmMoveSolm, evmCallSolm, evmSolm,
                        kickAfterEndState_executionEnv, initState, kickLotValue, hvatEq]
                        using hcallSolmRaw
                    by_cases hz : z = true
                    · have rd4462True : RD flapperBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4462⟩
                          (⟨1⟩ :: cageMoveEndPtr :: cageMoveSelectorWord ::
                            kickVatWord (kickRuntimeBeforeMoveMap I.codeOwner σ_evm I) I ::
                            kickRuntimeIdWord σ_evm I :: kickBidWord I :: kickLotWord I ::
                            ⟨313⟩ :: flapperSelWord I :: [])
                          (cageMoveCalldataMem (kickSenderWord I) (kickThisWord I)
                            (kickLotWord I)
                            (twoWordHashMem (kickRuntimeIdWord σ_evm I) ⟨1⟩
                              (twoWordHashMem (kickRuntimeIdWord σ_evm I) ⟨1⟩
                                (relyAuthHashMem I))))
                          (UInt256.ofNat 8) out (cA', σ') k4462 C4462 := by
                        simpa [hz] using rd4462
                      have hcallTrue :
                          typedCallViaEVM config evmMoveSolm
                            (EVM.address (AccountAddress.ofNat
                              (kickVatWord evmMoveSolm.accountMap
                                evmMoveSolm.executionEnv).toNat))
                            "move" 0
                            [.address evmMoveSolm.executionEnv.source,
                              .address evmMoveSolm.executionEnv.codeOwner, kickLotValue I]
                            (true, evmCallSolm, out) true := by
                        simpa [hz] using hcallSolm
                      have hbody :
                          ExecTransitionBody config contract evmSolm (kickLocals I)
                            kickTransition.body
                            (.returned { contract := contract, locals := kickMoveLocals evmSolm I }
                              evmCallSolm
                              (some [.int (Int.ofNat (kickIdWord evmSolm).toNat)])) := by
                        simpa [evmMoveSolm, evmCallSolm] using
                          flapperKickBodyReturns_moveCallSuccess evmSolm evmCallSolm I out
                            (by simpa [evmSolm, initState] using hwv)
                            (by simp [evmSolm, initState])
                            hauthSolm hliveSolm hkicksLtSolm hfillFitSolm hfillLeSolm
                            hendFitSolm hcodeSizeSolm hcallTrue
                      have hret :=
                        flapperKickX_moveCallSuccess
                          (g := Sat256.ofUInt256 g) (σ := σ_evm) (sel := flapperSelWord I)
                          hperm rd4462True
                      have hid := kickRuntimeIdWord_source_eq
                        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
                        (I := I) (g := g) hAccounts
                      exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                        (by simp [evmCallSolm, evmMoveSolm, evmSolm, kickAfterEndState,
                          kickAfterGuyState, kickAfterLotState, kickAfterBidState,
                          kickAfterKicksState, kickAfterFillState, initState,
                          storageStore_createdAccounts])
                        (by simpa [evmCallSolm] using hpostAccounts)
                        (by
                          rw [hid]
                          simpa [kickTransition] using
                            (returnEquiv_of_encode
                              (by simpa [uint256] using
                                uint256ReturnEncoding (kickIdWord evmSolm))))
                    · have hzFalse : z = false := by
                        cases z <;> simp at hz ⊢
                      have rd4462False : RD flapperBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4462⟩
                          (⟨0⟩ :: cageMoveEndPtr :: cageMoveSelectorWord ::
                            kickVatWord (kickRuntimeBeforeMoveMap I.codeOwner σ_evm I) I ::
                            kickRuntimeIdWord σ_evm I :: kickBidWord I :: kickLotWord I ::
                            ⟨313⟩ :: flapperSelWord I :: [])
                          (cageMoveCalldataMem (kickSenderWord I) (kickThisWord I)
                            (kickLotWord I)
                            (twoWordHashMem (kickRuntimeIdWord σ_evm I) ⟨1⟩
                              (twoWordHashMem (kickRuntimeIdWord σ_evm I) ⟨1⟩
                                (relyAuthHashMem I))))
                          (UInt256.ofNat 8) out (cA', σ') k4462 C4462 := by
                        simpa [hzFalse] using rd4462
                      have hcallFalse :
                          typedCallViaEVM config evmMoveSolm
                            (EVM.address (AccountAddress.ofNat
                              (kickVatWord evmMoveSolm.accountMap
                                evmMoveSolm.executionEnv).toNat))
                            "move" 0
                            [.address evmMoveSolm.executionEnv.source,
                              .address evmMoveSolm.executionEnv.codeOwner, kickLotValue I]
                            (false, evmCallSolm, out) true := by
                        simpa [hzFalse] using hcallSolm
                      have hbody :
                          ExecTransitionBody config contract evmSolm (kickLocals I)
                            kickTransition.body .reverted := by
                        simpa [evmMoveSolm, evmCallSolm] using
                          flapperKickBodyReverts_moveCallFailure evmSolm evmCallSolm I out
                            (by simpa [evmSolm, initState] using hwv)
                            (by simp [evmSolm, initState])
                            hauthSolm hliveSolm hkicksLtSolm hfillFitSolm hfillLeSolm
                            hendFitSolm hcodeSizeSolm hcallFalse
                      exact (flapperKickX_moveCallFailure rd4462False houtSize)
                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have htau :=
                  kickRuntimeTauWord_source_eq
                    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
                    (I := I) (g := g) hAccounts
                have hendOverflowSolm :
                    2 ^ 48 ≤
                      (kickNow48Word evmSolm).toNat +
                        (kickTauWord (kickAfterGuyState evmSolm I)).toNat := by
                  simpa [evmSolm, kickNow48Word, kickTimestampWord, initState, htau]
                    using (Nat.le_of_not_gt hendFit)
                have hbody :
                    ExecTransitionBody config contract evmSolm (kickLocals I)
                      kickTransition.body .reverted := by
                  exact flapperKickBodyReverts_endAddOverflow evmSolm I
                    (by simpa [evmSolm, initState] using hwv)
                    (by simp [evmSolm, initState])
                    hauthSolm hliveSolm hkicksLtSolm hfillFitSolm hfillLeSolm
                    hendOverflowSolm
                exact (flapperKickX_endAddOverflow
                    (g := Sat256.ofUInt256 g) (Nat.le_of_not_gt hendFit) rd4936)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hgtSolm :
                  (kickLidWord (kickAfterFillState evmSolm I)).toNat <
                    (kickFillWord (kickAfterFillState evmSolm I)).toNat := by
                have hgt := Nat.lt_of_not_ge hfillLe
                simpa [hfillWordAfter, hlidWordAfter] using hgt
              have hbody :
                  ExecTransitionBody config contract evmSolm (kickLocals I)
                    kickTransition.body .reverted := by
                exact flapperKickBodyReverts_overLid evmSolm I
                  (by simpa [evmSolm, initState] using hwv)
                  (by simp [evmSolm, initState])
                  hauthSolm hliveSolm hkicksLtSolm hfillFitSolm hgtSolm
              exact (flapperKickX_overLid (g := Sat256.ofUInt256 g) hperm
                  (Nat.lt_of_not_ge hfillLe) rd4155)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hfillOverflowSolm :
                UInt256.size ≤ (kickFillWord evmSolm).toNat + (kickLotWord I).toNat := by
              have hslot := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨9⟩
              simpa [kickFillWord, evmSolm, initState, hslot] using
                (Nat.le_of_not_gt hfillFit)
            have hbody :
                ExecTransitionBody config contract evmSolm (kickLocals I)
                  kickTransition.body .reverted := by
              exact flapperKickBodyReverts_fillAddOverflow evmSolm I
                (by simpa [evmSolm, initState] using hwv)
                (by simp [evmSolm, initState])
                hauthSolm hliveSolm hkicksLtSolm hfillOverflowSolm
            exact (flapperKickX_fillAddOverflow
                (g := Sat256.ofUInt256 g) (Nat.le_of_not_gt hfillFit) rd4143)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hkicksGeSolm : UInt256.size - 1 ≤ (kickKicksWord evmSolm).toNat := by
            have hslot := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨6⟩
            simpa [kickKicksWord, evmSolm, initState, hslot] using
              (Nat.le_of_not_gt hkicksLt)
          have hbody :
              ExecTransitionBody config contract evmSolm (kickLocals I)
                kickTransition.body .reverted := by
            exact flapperKickBodyReverts_kicksOverflow evmSolm I
              (by simpa [evmSolm, initState] using hwv)
              (by simp [evmSolm, initState])
              hauthSolm hliveSolm hkicksGeSolm
          exact (flapperKickX_kicksOverflow
              (g := Sat256.ofUInt256 g) (Nat.le_of_not_gt hkicksLt) rd4068)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hliveSolmNe : kickLiveWord evmSolm ≠ ⟨1⟩ := by
          intro hbad
          apply hlive
          have hslot := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
          rw [hslot]
          simpa [kickLiveWord, evmSolm, initState] using hbad
        have hbody :
            ExecTransitionBody config contract evmSolm (kickLocals I)
              kickTransition.body .reverted := by
          exact flapperKickBodyReverts_notLive evmSolm I
            (by simpa [evmSolm, initState] using hwv)
            (by simp [evmSolm, initState])
            hauthSolm hliveSolmNe
        exact (flapperKickX_notLive (g := Sat256.ofUInt256 g) hlive rd3994)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolmNe :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
              (relyAuthStorageSlot I) ≠ ⟨1⟩ := by
        have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
        intro hbad
        have hbad' : relyAuthWord σ_solm I = ⟨1⟩ := by
          simpa [evmSolm, relyAuthWord, flapperSlotWord, initState,
            Solm.EVM.storageLoad, State.lookupAccount] using hbad
        exact hauth (by rw [hword, hbad'])
      have hbody :
          ExecTransitionBody config contract evmSolm (kickLocals I)
            kickTransition.body .reverted := by
        exact flapperKickBodyReverts_unauthorized evmSolm I
          (by simpa [evmSolm, initState] using hwv)
          (by simp [evmSolm, initState])
          hauthSolmNe
      exact (flapperKickX_unauthorized (g := Sat256.ofUInt256 g) hauth rd3901)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact (flapperKickX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize
        (by omega) hreach)
      |>.reEquivDecodingFailed hcode hdispatch
        (flapperDecode_kick_none_short hsz4 (by omega))

end Benchmarks.Dss.Flapper
