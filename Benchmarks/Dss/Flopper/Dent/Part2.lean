import Benchmarks.Dss.Flopper.Dent.Part1

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

namespace Benchmarks.Dss.Flopper
theorem evalExpr_dent_tic_gt_timestamp_false (evm : EVM.State) (I : ExecutionEnv)
    (hle : (dentTicWord evm I).toNat ≤ (dentTimestampWord evm).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
        .ok (.bool false) := by
  have hticEval := evalExpr_dent_tic_storage evm I
  have hnlt : ¬ (Int.ofNat (dentTimestampWord evm).toNat <
      Int.ofNat (dentTicWord evm I).toNat) := by
    intro hlt
    have hltNat : (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat :=
      Int.ofNat_lt.mp hlt
    exact (Nat.not_lt.mpr hle) hltNat
  have hdec :
      decide (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        Int.ofNat (dentTicWord evm I).toNat) = false := by
    rw [decide_eq_false_iff_not]
    simpa [dentTimestampWord] using hnlt
  simp only [evalExpr?, hticEval, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hdec]

theorem evalExpr_dent_tic_eq_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (htic : dentTicWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) = .ok (.bool true) := by
  have hticEval := evalExpr_dent_tic_storage evm I
  simp only [evalExpr?, hticEval, EvalResult.bind, bind, pure]
  rw [htic]
  simp [evalBinaryOp?]

theorem evalExpr_dent_tic_eq_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (htic : dentTicWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) = .ok (.bool false) := by
  have hticEval := evalExpr_dent_tic_storage evm I
  have hne :
      Value.int (Int.ofNat (dentTicWord evm I).toNat) ≠ Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    exact htic (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hbeq :
      (Value.int (Int.ofNat (dentTicWord evm I).toNat) == Value.int 0) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hticEval, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_dent_tic_eq_zero_false_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (dentIdValue I))
    (hbids : "bids" ∉ locals)
    (htic : dentTicWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) = .ok (.bool false) := by
  have hticEval := evalExpr_dent_tic_storage_of_locals evm I hid hbids
  have hne :
      Value.int (Int.ofNat (dentTicWord evm I).toNat) ≠ Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    exact htic (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hbeq :
      (Value.int (Int.ofNat (dentTicWord evm I).toNat) == Value.int 0) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hticEval, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_dent_tic_eq_zero_true_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (dentIdValue I))
    (hbids : "bids" ∉ locals)
    (htic : dentTicWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) = .ok (.bool true) := by
  have hticEval := evalExpr_dent_tic_storage_of_locals evm I hid hbids
  simp only [evalExpr?, hticEval, EvalResult.bind, bind, pure]
  rw [htic]
  simp [evalBinaryOp?]

theorem evalExpr_dent_tic_guard_true_gt (evm : EVM.State) (I : ExecutionEnv)
    (hgt : (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .or
        (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
      .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_dent_tic_gt_timestamp_true evm I hgt,
    EvalResult.bind, bind, pure]

theorem evalExpr_dent_tic_guard_true_zero (evm : EVM.State) (I : ExecutionEnv)
    (htic : dentTicWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .or
        (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
      .ok (.bool true) := by
  by_cases hgt : (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat
  · exact evalExpr_dent_tic_guard_true_gt evm I hgt
  · have hle : (dentTicWord evm I).toNat ≤ (dentTimestampWord evm).toNat :=
      Nat.le_of_not_gt hgt
    simp only [evalExpr?, evalExpr_dent_tic_gt_timestamp_false evm I hle,
      evalExpr_dent_tic_eq_zero_true evm I htic, EvalResult.bind, bind, pure]

theorem evalExpr_dent_tic_guard_false (evm : EVM.State) (I : ExecutionEnv)
    (hticNe : dentTicWord evm I ≠ ⟨0⟩)
    (hticLe : (dentTicWord evm I).toNat ≤ (dentTimestampWord evm).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .or
        (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
      .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_dent_tic_gt_timestamp_false evm I hticLe,
    evalExpr_dent_tic_eq_zero_false evm I hticNe, EvalResult.bind, bind, pure]

theorem evalExpr_dent_end_gt_timestamp_true (evm : EVM.State) (I : ExecutionEnv)
    (hgt : (dentTimestampWord evm).toNat < (dentEndWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool true) := by
  have hendEval := evalExpr_dent_end_storage evm I
  simp only [evalExpr?, hendEval, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  simpa [dentTimestampWord] using hgt

theorem evalExpr_dent_end_gt_timestamp_false (evm : EVM.State) (I : ExecutionEnv)
    (hle : (dentEndWord evm I).toNat ≤ (dentTimestampWord evm).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool false) := by
  have hendEval := evalExpr_dent_end_storage evm I
  have hnlt : ¬ (Int.ofNat (dentTimestampWord evm).toNat <
      Int.ofNat (dentEndWord evm I).toNat) := by
    intro hlt
    have hltNat : (dentTimestampWord evm).toNat < (dentEndWord evm I).toNat :=
      Int.ofNat_lt.mp hlt
    exact (Nat.not_lt.mpr hle) hltNat
  have hdec :
      decide (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        Int.ofNat (dentEndWord evm I).toNat) = false := by
    rw [decide_eq_false_iff_not]
    simpa [dentTimestampWord] using hnlt
  simp only [evalExpr?, hendEval, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hdec]

theorem evalExpr_dent_bid_eq_true (evm : EVM.State) (I : ExecutionEnv)
    (hbid : dentBidWord I = dentBidStoredWord evm I) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) = .ok (.bool true) := by
  have hbidVar := evalExpr_dent_bid_var evm I
  have hbidStorage := evalExpr_dent_bid_storage evm I
  simp only [evalExpr?, hbidVar, hbidStorage, EvalResult.bind, bind, pure, evalBinaryOp?]
  simp [dentBidValue, hbid]

theorem evalExpr_dent_bid_eq_false (evm : EVM.State) (I : ExecutionEnv)
    (hbid : dentBidWord I ≠ dentBidStoredWord evm I) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) = .ok (.bool false) := by
  have hbidVar := evalExpr_dent_bid_var evm I
  have hbidStorage := evalExpr_dent_bid_storage evm I
  have hne :
      Value.int (Int.ofNat (dentBidWord I).toNat) ≠
        Value.int (Int.ofNat (dentBidStoredWord evm I).toNat) := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hbid
    apply u256_inj
    exact Int.ofNat.inj hbad
  have hbeq :
      (Value.int (Int.ofNat (dentBidWord I).toNat) ==
        Value.int (Int.ofNat (dentBidStoredWord evm I).toNat)) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hbidVar, hbidStorage, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_dent_lot_lt_true (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (dentLotWord I).toNat < (dentLotStoredWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) = .ok (.bool true) := by
  have hlotVar := evalExpr_dent_lot_var evm I
  have hlotStorage := evalExpr_dent_lot_storage evm I
  simp only [evalExpr?, hlotVar, hlotStorage, EvalResult.bind, bind, pure, evalBinaryOp?]
  simpa using hlt

theorem evalExpr_dent_lot_lt_false (evm : EVM.State) (I : ExecutionEnv)
    (hle : (dentLotStoredWord evm I).toNat ≤ (dentLotWord I).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) = .ok (.bool false) := by
  have hlotVar := evalExpr_dent_lot_var evm I
  have hlotStorage := evalExpr_dent_lot_storage evm I
  have hnlt : ¬ (Int.ofNat (dentLotWord I).toNat <
      Int.ofNat (dentLotStoredWord evm I).toNat) := by
    intro hlt
    exact (Nat.not_lt.mpr hle) (Int.ofNat_lt.mp hlt)
  have hdec :
      decide (Int.ofNat (dentLotWord I).toNat <
        Int.ofNat (dentLotStoredWord evm I).toNat) = false := by
    rw [decide_eq_false_iff_not]
    exact hnlt
  simp only [evalExpr?, hlotVar, hlotStorage, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hdec]

theorem evalExpr_dent_lot_var_begLotLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentBegLotLocals evm I } evm
        (.var "lot") =
      .ok (dentLotValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((dentBegLotLocals evm I).get? "lot") = .ok (dentLotValue I)
  rw [dentBegLotLocals_get_lot]
  rfl

theorem evalExpr_dent_bid_var_lotOneLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
        (.var "bid") =
      .ok (dentBidValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((dentLotOneLocals evm I).get? "bid") = .ok (dentBidValue I)
  rw [dentLotOneLocals_get_bid]
  rfl

theorem evalExpr_dent_lot_var_lotOneLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
        (.var "lot") =
      .ok (dentLotValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((dentLotOneLocals evm I).get? "lot") = .ok (dentLotValue I)
  rw [dentLotOneLocals_get_lot]
  rfl

theorem evalExpr_dent_begLot_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentBegLotLocals evm I } evm
        (.var "begLot") =
      .ok (.int (Int.ofNat (dentBegLotWord evm I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((dentBegLotLocals evm I).get? "begLot") =
    .ok (.int (Int.ofNat (dentBegLotWord evm I).toNat))
  rw [dentBegLotLocals_get_begLot]
  rfl

theorem evalExpr_dent_begLot_var_lotOneLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
        (.var "begLot") =
      .ok (.int (Int.ofNat (dentBegLotWord evm I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((dentLotOneLocals evm I).get? "begLot") =
    .ok (.int (Int.ofNat (dentBegLotWord evm I).toNat))
  rw [dentLotOneLocals_get_begLot]
  rfl

theorem evalExpr_dent_lotOne_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
        (.var "lotOne") =
      .ok (.int (Int.ofNat (dentLotOneWord evm I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((dentLotOneLocals evm I).get? "lotOne") =
    .ok (.int (Int.ofNat (dentLotOneWord evm I).toNat))
  rw [dentLotOneLocals_get_lotOne]
  rfl

theorem evalExpr_dent_beg_storage_begLotLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentBegLotLocals evm I } evm
        (.storage begRef) =
      .ok (.int (Int.ofNat (dentBegWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := dentBegLotLocals evm I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := begRef) (er := dentBegEvaledRef)
    (t := .int uint256Int) (loc := wordLoc ⟨4⟩)
    (value := .int (Int.ofNat (dentBegWord evm).toNat))
    (by simp [frame, begRef, dentBegLotLocals, dentLocals])
    (by simp [frame, dentBegEvaledRef, evalStorageRef, evalStorageRefSteps,
      begRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [dentBegWord, flopperSlotWord] using flopperStorageLocLoad_uint256 evm ⟨4⟩)

theorem evalExpr_dent_lot_storage_begLotLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentBegLotLocals evm I } evm
        (.storage (bidsF (.var "id") "lot")) =
      .ok (.int (Int.ofNat (dentLotStoredWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := dentBegLotLocals evm I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "lot") (er := dentLotEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (auctionLotSlot (dentIdWord I)))
    (value := .int (Int.ofNat (dentLotStoredWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simpa [frame, dentLotEvaledRef] using
        evalStorageRef_auction_field evm (dentBegLotLocals evm I) (dentIdWord I) "lot"
          (by simpa [dentIdValue] using dentBegLotLocals_get_id evm I))
    (by simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
      BidStructTy, uint256St])
    (by rfl)
    (by simpa [dentLotStoredWord, flopperSlotWord] using
      flopperStorageLocLoad_uint256 evm (auctionLotSlot (dentIdWord I)))

theorem evalExpr_dent_lot_storage_lotOneLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
        (.storage (bidsF (.var "id") "lot")) =
      .ok (.int (Int.ofNat (dentLotStoredWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := dentLotOneLocals evm I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "lot") (er := dentLotEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (auctionLotSlot (dentIdWord I)))
    (value := .int (Int.ofNat (dentLotStoredWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simpa [frame, dentLotEvaledRef] using
        evalStorageRef_auction_field evm (dentLotOneLocals evm I) (dentIdWord I) "lot"
          (by simpa [dentIdValue] using dentLotOneLocals_get_id evm I))
    (by simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
      BidStructTy, uint256St])
    (by rfl)
    (by simpa [dentLotStoredWord, flopperSlotWord] using
      flopperStorageLocLoad_uint256 evm (auctionLotSlot (dentIdWord I)))

theorem dentBegLotWord_toNat_of_fit (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (dentBegWord evm).toNat * (dentLotWord I).toNat < UInt256.size) :
    (dentBegLotWord evm I).toNat =
      (dentBegWord evm).toNat * (dentLotWord I).toNat := by
  rw [dentBegLotWord, u256_mul_op_toNat, Nat.mod_eq_of_lt hfit]

theorem dentLotOneWord_toNat_of_fit (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (dentLotStoredWord evm I).toNat * dentOneWord.toNat < UInt256.size) :
    (dentLotOneWord evm I).toNat =
      (dentLotStoredWord evm I).toNat * dentOneWord.toNat := by
  rw [dentLotOneWord, u256_mul_op_toNat, Nat.mod_eq_of_lt hfit]

set_option maxHeartbeats 1000000 in
theorem evalExpr_dent_begLot_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (dentBegWord evm).toNat * (dentLotWord I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
        (mul256 (.storage begRef) (.var "lot")) =
      .ok (.int (Int.ofNat (dentBegLotWord evm I).toNat)) := by
  have hbeg := evalExpr_dent_beg_storage evm I
  have hlot := evalExpr_dent_lot_var evm I
  have hprod := dentBegLotWord_toNat_of_fit evm I hfit
  unfold mul256 u256
  simp only [evalExpr?, hbeg, hlot, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hfitNat :
      (dentBegWord evm).toNat * (dentLotWord I).toNat < 2 ^ 256 := by
    simpa [UInt256.size] using hfit
  have hltInt :
      Int.ofNat ((dentBegWord evm).toNat * (dentLotWord I).toNat) <
        (2 : Int) ^ (256 : Nat) := by
    change Int.ofNat ((dentBegWord evm).toNat * (dentLotWord I).toNat) <
      Int.ofNat (2 ^ 256)
    exact Int.ofNat_lt.mpr hfitNat
  simp [uint256Int, hprod]
  constructor
  · exact Int.natCast_nonneg _
  · exact hltInt

theorem evalExpr_dent_begLot_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hoverflow : UInt256.size ≤ (dentBegWord evm).toNat * (dentLotWord I).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
        (mul256 (.storage begRef) (.var "lot")) =
      .revert := by
  have hbeg := evalExpr_dent_beg_storage evm I
  have hlot := evalExpr_dent_lot_var evm I
  unfold mul256 u256
  simp only [evalExpr?, hbeg, hlot, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hoverflowNat :
      2 ^ 256 ≤ (dentBegWord evm).toNat * (dentLotWord I).toNat := by
    simpa [UInt256.size] using hoverflow
  have hgeInt :
      (2 : Int) ^ (256 : Nat) ≤
        Int.ofNat ((dentBegWord evm).toNat * (dentLotWord I).toNat) := by
    change Int.ofNat (2 ^ 256) ≤
      Int.ofNat ((dentBegWord evm).toNat * (dentLotWord I).toNat)
    exact Int.ofNat_le.mpr hoverflowNat
  simp [uint256Int]
  intro _hnonneg
  exact hgeInt

theorem evalExpr_dent_lotOne_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (dentLotStoredWord evm I).toNat * dentOneWord.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := dentBegLotLocals evm I } evm
        (mul256 (.storage (bidsF (.var "id") "lot")) (.intLit ONE)) =
      .ok (.int (Int.ofNat (dentLotOneWord evm I).toNat)) := by
  have hlot := evalExpr_dent_lot_storage_begLotLocals evm I
  have hprod := dentLotOneWord_toNat_of_fit evm I hfit
  unfold mul256 u256
  simp only [evalExpr?, hlot, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hone : dentOneWord.toNat = 1000000000000000000 := by native_decide
  have hfitNat :
      (dentLotStoredWord evm I).toNat * 1000000000000000000 < 2 ^ 256 := by
    simpa [UInt256.size, hone] using hfit
  have hltInt :
      Int.ofNat ((dentLotStoredWord evm I).toNat * 1000000000000000000) <
        (2 : Int) ^ (256 : Nat) := by
    change Int.ofNat ((dentLotStoredWord evm I).toNat * 1000000000000000000) <
      Int.ofNat (2 ^ 256)
    exact Int.ofNat_lt.mpr hfitNat
  have hmulCast :
      Int.ofNat ((dentLotStoredWord evm I).toNat * 1000000000000000000) =
        Int.ofNat (dentLotStoredWord evm I).toNat * 1000000000000000000 := by
    norm_num
  have hltIntMul :
      Int.ofNat (dentLotStoredWord evm I).toNat * 1000000000000000000 <
        (2 : Int) ^ (256 : Nat) := by
    rw [← hmulCast]
    exact hltInt
  have hnonneg :
      ¬ Int.ofNat (dentLotStoredWord evm I).toNat *
          (1000000000000000000 : Int) < 0 := by
    rw [← hmulCast]
    exact not_lt_of_ge (Int.natCast_nonneg _)
  have hnotge :
      ¬ 115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤
          Int.ofNat (dentLotStoredWord evm I).toNat * 1000000000000000000 := by
    simpa using not_le_of_gt hltIntMul
  simp [uint256Int, ONE, hprod, dentOneWord]
  rw [if_neg]
  · simp [show ({ val := 1000000000000000000 } : UInt256).toNat =
        1000000000000000000 from by native_decide]
  · intro hbad
    cases hbad with
    | inl hlt => exact hnonneg hlt
    | inr hge => exact hnotge hge

theorem evalExpr_dent_lotOne_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hoverflow : UInt256.size ≤ (dentLotStoredWord evm I).toNat * dentOneWord.toNat) :
    evalExpr? config { contract := contract, locals := dentBegLotLocals evm I } evm
        (mul256 (.storage (bidsF (.var "id") "lot")) (.intLit ONE)) =
      .revert := by
  have hlot := evalExpr_dent_lot_storage_begLotLocals evm I
  unfold mul256 u256
  simp only [evalExpr?, hlot, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hone : dentOneWord.toNat = 1000000000000000000 := by native_decide
  have hoverflowNat :
      2 ^ 256 ≤ (dentLotStoredWord evm I).toNat * 1000000000000000000 := by
    simpa [UInt256.size, hone] using hoverflow
  have hgeInt :
      (2 : Int) ^ (256 : Nat) ≤
        Int.ofNat ((dentLotStoredWord evm I).toNat * 1000000000000000000) := by
    change Int.ofNat (2 ^ 256) ≤
      Int.ofNat ((dentLotStoredWord evm I).toNat * 1000000000000000000)
    exact Int.ofNat_le.mpr hoverflowNat
  simp [uint256Int, ONE]
  exact hgeInt

theorem evalExpr_dent_lot_eq_zero_true_begLotLocals (evm : EVM.State) (I : ExecutionEnv)
    (hlot : dentLotWord I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dentBegLotLocals evm I } evm
      (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool true) := by
  have hlotEval := evalExpr_dent_lot_var_begLotLocals evm I
  simp only [evalExpr?, hlotEval, EvalResult.bind, bind, pure]
  simp [dentLotValue, hlot, evalBinaryOp?]

theorem evalExpr_dent_lot_eq_zero_false_begLotLocals (evm : EVM.State) (I : ExecutionEnv)
    (hlot : dentLotWord I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dentBegLotLocals evm I } evm
      (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool false) := by
  have hlotEval := evalExpr_dent_lot_var_begLotLocals evm I
  have hne :
      Value.int (Int.ofNat (dentLotWord I).toNat) ≠ Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    exact hlot (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hbeq :
      (Value.int (Int.ofNat (dentLotWord I).toNat) == Value.int 0) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hlotEval, EvalResult.bind, bind, pure]
  simp only [dentLotValue, evalBinaryOp?]
  rw [hbeq]

set_option maxHeartbeats 1000000 in
theorem evalExpr_dent_begLot_div_lot_eq_beg (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (dentBegWord evm).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlot : dentLotWord I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dentBegLotLocals evm I } evm
      (.binary .eq (.binary .div (.var "begLot") (.var "lot")) (.storage begRef)) =
        .ok (.bool true) := by
  have hbase := evalExpr_dent_begLot_var evm I
  have hlotEval := evalExpr_dent_lot_var_begLotLocals evm I
  have hbegEval := evalExpr_dent_beg_storage_begLotLocals evm I
  have hbaseNat := dentBegLotWord_toNat_of_fit evm I hfit
  have hlotPos : 0 < (dentLotWord I).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hlot (uint256_toNat_eq_zero hzero))
  have hdivNat :
      (dentBegLotWord evm I).toNat / (dentLotWord I).toNat =
        (dentBegWord evm).toNat := by
    rw [hbaseNat]
    rw [Nat.mul_comm]
    exact Nat.mul_div_right _ hlotPos
  have hdivInt :
      Int.ofNat (dentBegLotWord evm I).toNat / Int.ofNat (dentLotWord I).toNat =
        Int.ofNat (dentBegWord evm).toNat := by
    simpa [Int.natCast_ediv] using
      (congrArg (fun n : Nat => (n : Int)) hdivNat)
  simp only [evalExpr?, hbase, hlotEval, hbegEval, EvalResult.bind, bind]
  simp [dentLotValue, evalBinaryOp?, hlotPos.ne']
  exact hdivInt

theorem evalExpr_dent_begLot_mul_guard_true (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (dentBegWord evm).toNat * (dentLotWord I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := dentBegLotLocals evm I } evm
      (.binary .or
        (.binary .eq (.var "lot") (.intLit 0))
        (.binary .eq (.binary .div (.var "begLot") (.var "lot")) (.storage begRef))) =
      .ok (.bool true) := by
  by_cases hlotZero : dentLotWord I = ⟨0⟩
  · simp only [evalExpr?, evalExpr_dent_lot_eq_zero_true_begLotLocals evm I hlotZero,
      EvalResult.bind, bind, pure]
  · simp only [evalExpr?, evalExpr_dent_lot_eq_zero_false_begLotLocals evm I hlotZero,
      evalExpr_dent_begLot_div_lot_eq_beg evm I hfit hlotZero, EvalResult.bind, bind, pure]

theorem evalExpr_dent_one_eq_zero_false_lotOneLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
      (.binary .eq (.intLit ONE) (.intLit 0)) = .ok (.bool false) := by
  simp only [evalExpr?, pure, EvalResult.bind, bind]
  rfl

theorem evalExpr_dent_lotOne_div_one_eq_lot (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (dentLotStoredWord evm I).toNat * dentOneWord.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
      (.binary .eq
        (.binary .div (.var "lotOne") (.intLit ONE))
        (.storage (bidsF (.var "id") "lot"))) = .ok (.bool true) := by
  have hbase := evalExpr_dent_lotOne_var evm I
  have hlotEval := evalExpr_dent_lot_storage_lotOneLocals evm I
  have hbaseNat := dentLotOneWord_toNat_of_fit evm I hfit
  have honeNat : dentOneWord.toNat = 1000000000000000000 := by native_decide
  have honePos : 0 < dentOneWord.toNat := by
    rw [honeNat]
    norm_num
  have hdivNat :
      (dentLotOneWord evm I).toNat / dentOneWord.toNat =
        (dentLotStoredWord evm I).toNat := by
    rw [hbaseNat]
    rw [Nat.mul_comm]
    exact Nat.mul_div_right _ honePos
  have hdivInt :
      Int.ofNat (dentLotOneWord evm I).toNat / ONE =
        Int.ofNat (dentLotStoredWord evm I).toNat := by
    have hcast := congrArg (fun n : Nat => (n : Int)) hdivNat
    simpa [ONE, honeNat, Int.natCast_ediv] using hcast
  simp only [evalExpr?, hbase, hlotEval, EvalResult.bind, bind]
  simp [evalBinaryOp?, ONE]
  exact hdivInt

theorem evalExpr_dent_lotOne_mul_guard_true (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (dentLotStoredWord evm I).toNat * dentOneWord.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
      (.binary .or
        (.binary .eq (.intLit ONE) (.intLit 0))
        (.binary .eq
          (.binary .div (.var "lotOne") (.intLit ONE))
          (.storage (bidsF (.var "id") "lot")))) =
      .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_dent_one_eq_zero_false_lotOneLocals evm I,
    evalExpr_dent_lotOne_div_one_eq_lot evm I hfit, EvalResult.bind, bind, pure]

theorem evalExpr_dent_decrease_true (evm : EVM.State) (I : ExecutionEnv)
    (hsuff : (dentBegLotWord evm I).toNat ≤ (dentLotOneWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
      (.binary .le (.var "begLot") (.var "lotOne")) = .ok (.bool true) := by
  have hbeg := evalExpr_dent_begLot_var_lotOneLocals evm I
  have hlotOne := evalExpr_dent_lotOne_var evm I
  simp only [evalExpr?, hbeg, hlotOne, EvalResult.bind, bind, pure, evalBinaryOp?]
  simpa using hsuff

theorem evalExpr_dent_decrease_false (evm : EVM.State) (I : ExecutionEnv)
    (hinsuff : (dentLotOneWord evm I).toNat < (dentBegLotWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
      (.binary .le (.var "begLot") (.var "lotOne")) = .ok (.bool false) := by
  have hbeg := evalExpr_dent_begLot_var_lotOneLocals evm I
  have hlotOne := evalExpr_dent_lotOne_var evm I
  have hnle :
      ¬ (Int.ofNat (dentBegLotWord evm I).toNat ≤
        Int.ofNat (dentLotOneWord evm I).toNat) := by
    intro hle
    exact (Nat.not_le_of_gt hinsuff) (Int.ofNat_le.mp hle)
  have hdec :
      decide
          (Int.ofNat (dentBegLotWord evm I).toNat ≤
            Int.ofNat (dentLotOneWord evm I).toNat) = false := by
    rw [decide_eq_false_iff_not]
    exact hnle
  simp only [evalExpr?, hbeg, hlotOne, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hdec]

theorem evalExpr_dent_sender_ne_guy_false_lotOneLocals (evm : EVM.State) (I : ExecutionEnv)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val = dentGuyWord evm I) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
      (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) = .ok (.bool false) := by
  let frame : Frame := { contract := contract, locals := dentLotOneLocals evm I }
  have hsender :
      evalExpr? config frame evm sender =
        .ok (.address evm.executionEnv.source) := by
    simp [frame, sender, evalExpr?, envValue, pure]
  have hguy :
      evalExpr? config frame evm (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat (dentGuyWord evm I).toNat)) := by
    let frame0 : Frame := { contract := contract, locals := dentLotOneLocals evm I }
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame0) (evm := evm)
      (slot := bidsF (.var "id") "guy") (er := dentGuyEvaledRef I)
      (t := .address) (loc := addrLoc (auctionPackedSlot (dentIdWord I)))
      (value := .address (AccountAddress.ofNat (dentGuyWord evm I).toNat))
      (by simp [frame0, bidsF])
      (by
        simpa [frame0, dentGuyEvaledRef] using
          evalStorageRef_auction_field evm (dentLotOneLocals evm I) (dentIdWord I) "guy"
            (by simpa [dentIdValue] using dentLotOneLocals_get_id evm I))
      (by simp [frame0, auctionIdKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, BidStructTy, addrSt])
      (by rfl)
      (by
        simpa [dentGuyWord, flopperAddressReturnWord, flopperSlotWord] using
          flopperStorageLocLoad_address_offset0 evm (auctionPackedSlot (dentIdWord I)))
  have haddr :
      AccountAddress.ofNat (dentGuyWord evm I).toNat = evm.executionEnv.source := by
    rw [← hcaller]
    simpa [solcSourceWord] using solcSource_ofNat evm.executionEnv
  change evalExpr? config frame evm
      (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) = .ok (.bool false)
  simp only [evalExpr?, hsender, hguy, EvalResult.bind, bind, pure]
  rw [haddr]
  simp [evalBinaryOp?]

theorem evalExpr_dent_sender_ne_guy_true_lotOneLocals (evm : EVM.State) (I : ExecutionEnv)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ dentGuyWord evm I) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
      (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) = .ok (.bool true) := by
  let frame : Frame := { contract := contract, locals := dentLotOneLocals evm I }
  have hsender :
      evalExpr? config frame evm sender =
        .ok (.address evm.executionEnv.source) := by
    simpa [frame] using evalExpr_dent_sender evm (dentLotOneLocals evm I)
  have hguy :
      evalExpr? config frame evm (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat (dentGuyWord evm I).toNat)) := by
    simpa [frame] using
      evalExpr_dent_guy_storage_of_locals evm I
        (locals := dentLotOneLocals evm I) (dentLotOneLocals_get_id evm I)
        (by simp [dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hguyCanon : (dentGuyWord evm I).toNat < EVM.addressModulus := by
    simpa [dentGuyWord, flopperAddressReturnWord] using
      solcAddrMask_result_canonical
        (flopperSlotWord (auctionPackedSlot (dentIdWord I)) evm.accountMap
          evm.executionEnv)
  have haddrNe :
      evm.executionEnv.source ≠ AccountAddress.ofNat (dentGuyWord evm I).toNat := by
    intro heq
    apply hcaller
    calc
      UInt256.ofNat evm.executionEnv.source.val
          = UInt256.ofNat (AccountAddress.ofNat (dentGuyWord evm I).toNat).val := by
              rw [heq]
      _ = EVM.word (AccountAddress.ofNat (dentGuyWord evm I).toNat).val := rfl
      _ = dentGuyWord evm I := flopperAddressWord_eq_ofNat_address hguyCanon
  have hne :
      Value.address evm.executionEnv.source ≠
        Value.address (AccountAddress.ofNat (dentGuyWord evm I).toNat) := by
    intro hbad
    injection hbad with haddr
    exact haddrNe haddr
  have hbeq :
      (Value.address evm.executionEnv.source ==
        Value.address (AccountAddress.ofNat (dentGuyWord evm I).toNat)) = false :=
    beq_eq_false_iff_ne.mpr hne
  change evalExpr? config frame evm
      (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) = .ok (.bool true)
  simp only [evalExpr?, hsender, hguy, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hbeq]
  rfl

set_option maxHeartbeats 1000000 in
theorem assign_dentLotStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := dentLotOneLocals evm I } evm
      .storage (bidsF (.var "id") "lot") (.int (Int.ofNat (dentLotWord I).toNat)) =
      .ok ({ contract := contract, locals := dentLotOneLocals evm I },
        dentAfterLotStore evm I) := by
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals := dentLotOneLocals evm I })
    (evm := evm)
    (evm' := dentAfterLotStore evm I)
    (slot := bidsF (.var "id") "lot")
    (er := dentLotEvaledRef I)
    (ty := uint256St)
    (loc := wordLoc (auctionLotSlot (dentIdWord I)))
    (n := Int.ofNat (dentLotWord I).toNat)
    (dentLotOneLocals_get_bids evm I)
    (by
      simpa [dentLotEvaledRef, dentIdValue] using
        evalStorageRef_auction_field evm (dentLotOneLocals evm I)
          (dentIdWord I) "lot"
          (by simpa [dentIdValue] using dentLotOneLocals_get_id evm I))
    (by
      simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
    (by
      funext evm'
      exact auctionLotLayout evm' (dentIdWord I))
    (by
      simpa [wordLoc, uint256Loc, dentAfterLotStore] using
        storageLocStore_uint256 evm (auctionLotSlot (dentIdWord I)) (dentLotWord I))

set_option maxHeartbeats 1000000 in
theorem assign_dentLotStorage_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (dentIdValue I))
    (hbids : locals.get? "bids" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (bidsF (.var "id") "lot") (.int (Int.ofNat (dentLotWord I).toNat)) =
      .ok ({ contract := contract, locals := locals }, dentAfterLotStore evm I) := by
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (evm := evm)
    (evm' := dentAfterLotStore evm I)
    (slot := bidsF (.var "id") "lot")
    (er := dentLotEvaledRef I)
    (ty := uint256St)
    (loc := wordLoc (auctionLotSlot (dentIdWord I)))
    (n := Int.ofNat (dentLotWord I).toNat)
    hbids
    (by
      simpa [dentLotEvaledRef, dentIdValue] using
        evalStorageRef_auction_field evm locals (dentIdWord I) "lot"
          (by simpa [dentIdValue] using hid))
    (by
      simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
    (by
      funext evm'
      exact auctionLotLayout evm' (dentIdWord I))
    (by
      simpa [wordLoc, uint256Loc, dentAfterLotStore] using
        storageLocStore_uint256 evm (auctionLotSlot (dentIdWord I)) (dentLotWord I))

set_option maxHeartbeats 1000000 in
theorem assign_dentGuyStorage_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (dentIdValue I))
    (hbids : locals.get? "bids" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (bidsF (.var "id") "guy") (.address evm.executionEnv.source) =
      .ok ({ contract := contract, locals := locals }, dentAfterGuyStore evm I) := by
  let src := UInt256.ofNat evm.executionEnv.source.val
  have haddr :
      evm.executionEnv.source = AccountAddress.ofNat src.toNat := by
    symm
    simpa [src, solcSourceWord] using solcSource_ofNat evm.executionEnv
  rw [haddr]
  apply assignStorageRef_storage_scalar_value
      (ty := addrSt)
      (er := dentGuyEvaledRef I)
      (loc := addrLoc (auctionPackedSlot (dentIdWord I)))
      (hbase := hbids)
      (her := by
        simpa [dentGuyEvaledRef, dentIdValue] using
          evalStorageRef_auction_field evm locals (dentIdWord I) "guy"
            (by simpa [dentIdValue] using hid))
      (hty := by simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, BidStructTy, addrSt])
      (hloc := by rfl)
      (hscalar := by trivial)
  have hcanon : src.toNat < EVM.addressModulus := by
    simpa [src, solcSourceWord] using solcSourceWord_canonical evm.executionEnv
  simpa [dentAfterGuyStore, addrLoc, src] using
    storageLocStore_address_offset0 evm (auctionPackedSlot (dentIdWord I)) src hcanon

theorem dentAfterLotStore_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (dentAfterLotStore evm I).executionEnv = evm.executionEnv := by
  simp [dentAfterLotStore, storageStore_executionEnv]

theorem dentNow48Word_toNat (evm : EVM.State) :
    (dentNow48Word evm).toNat = (dentTimestampWord evm).toNat % 2 ^ 48 := by
  unfold dentNow48Word
  rw [u256_land_toNat]
  change Nat.land (dentTimestampWord evm).toNat (2 ^ 48 - 1) % UInt256.size =
    (dentTimestampWord evm).toNat % 2 ^ 48
  rw [nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt
    (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num [UInt256.size]))

theorem dentTicPostWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat <
        2 ^ 48) :
    (dentTicPostWord evm I).toNat =
      (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat := by
  unfold dentTicPostWord
  exact UInt256.toNat_ofNat_of_lt (lt_trans hfit (by norm_num [UInt256.size]))

theorem evalExpr_dent_now48_lotOneLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I }
        (dentAfterLotStore evm I) now48 =
      .ok (.int (Int.ofNat (dentNow48Word evm).toNat)) := by
  unfold now48 wrap48
  simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hmod :
      Int.ofNat (UInt256.ofNat (dentAfterLotStore evm I).executionEnv.header.timestamp).toNat %
          uint48Modulus =
        Int.ofNat (dentNow48Word evm).toNat := by
    have hnow := dentNow48Word_toNat evm
    have henv :
        (UInt256.ofNat (dentAfterLotStore evm I).executionEnv.header.timestamp).toNat =
          (dentTimestampWord evm).toNat := by
      simp [dentTimestampWord, dentAfterLotStore_executionEnv]
    rw [henv, hnow]
    norm_num [uint48Modulus, Int.natCast_mod]
  simpa [uint48Modulus] using hmod

theorem evalExpr_dent_ttl_storage_lotOneLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I }
        (dentAfterLotStore evm I) (.storage ttlRef) =
      .ok (.int (Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat)) := by
  let frame : Frame := { contract := contract, locals := dentLotOneLocals evm I }
  have hload :
      storageLocLoad (dentAfterLotStore evm I) (uint48Loc ⟨6⟩ ⟨0, by decide⟩ (by decide)) =
        .int (Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat) := by
    simpa [dentTtlWord, flopperUint48Offset0Word, flopperSlotWord] using
      flopperStorageLocLoad_uint48_offset0 (dentAfterLotStore evm I) ⟨6⟩
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := dentAfterLotStore evm I)
    (slot := ttlRef) (er := dentTtlEvaledRef)
    (t := .int uint48Int) (loc := uint48Loc ⟨6⟩ ⟨0, by decide⟩ (by decide))
    (value := .int (Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat))
    (by simp [frame, ttlRef, dentLotOneLocals, dentBegLotLocals, dentLocals])
    (by simp [frame, dentTtlEvaledRef, evalStorageRef, evalStorageRefSteps,
      ttlRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint48St])
    (by rfl)
    hload

theorem evalExpr_dent_ticAdd_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat <
        2 ^ 48) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I }
        (dentAfterLotStore evm I)
        (wrap48 (.binary .add now48 (.storage ttlRef))) =
      .ok (.int (Int.ofNat (dentTicPostWord evm I).toNat)) := by
  have hnow := evalExpr_dent_now48_lotOneLocals evm I
  have httl := evalExpr_dent_ttl_storage_lotOneLocals evm I
  have hticNat := dentTicPostWord_toNat evm I hfit
  unfold wrap48
  simp only [evalExpr?, hnow, httl, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hsumMod :
      (Int.ofNat (dentNow48Word evm).toNat +
          Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat) %
          uint48Modulus =
        Int.ofNat (dentTicPostWord evm I).toNat := by
    rw [hticNat]
    have hsumCast :
        Int.ofNat ((dentNow48Word evm).toNat +
            (dentTtlWord (dentAfterLotStore evm I)).toNat) =
          Int.ofNat (dentNow48Word evm).toNat +
            Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat := by
      norm_num
    rw [← hsumCast]
    have hfitInt :
        Int.ofNat ((dentNow48Word evm).toNat +
            (dentTtlWord (dentAfterLotStore evm I)).toNat) < uint48Modulus := by
      change Int.ofNat ((dentNow48Word evm).toNat +
          (dentTtlWord (dentAfterLotStore evm I)).toNat) < Int.ofNat (2 ^ 48)
      exact Int.ofNat_lt.mpr hfit
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) hfitInt
  simpa [uint48Modulus] using hsumMod

theorem evalExpr_dent_ticAdd_wrapped (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLotOneLocals evm I }
        (dentAfterLotStore evm I)
        (wrap48 (.binary .add now48 (.storage ttlRef))) =
      .ok (.int (Int.ofNat (dentTicWrappedNat evm I))) := by
  have hnow := evalExpr_dent_now48_lotOneLocals evm I
  have httl := evalExpr_dent_ttl_storage_lotOneLocals evm I
  unfold wrap48
  simp only [evalExpr?, hnow, httl, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hsumMod :
      (Int.ofNat (dentNow48Word evm).toNat +
          Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat) %
          uint48Modulus =
        Int.ofNat (dentTicWrappedNat evm I) := by
    have hsumCast :
        Int.ofNat ((dentNow48Word evm).toNat +
            (dentTtlWord (dentAfterLotStore evm I)).toNat) =
          Int.ofNat (dentNow48Word evm).toNat +
            Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat := by
      norm_num
    rw [← hsumCast]
    norm_num [dentTicWrappedNat, uint48Modulus, Int.natCast_mod]
  simpa [uint48Modulus] using hsumMod

theorem evalExpr_dent_tic_guard_true (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat <
        2 ^ 48) :
    evalExpr? config { contract := contract, locals := dentTicLocals evm I }
        (dentAfterLotStore evm I)
      (.binary .ge (.var "tic_") now48) = .ok (.bool true) := by
  have htic :
      evalExpr? config { contract := contract, locals := dentTicLocals evm I }
          (dentAfterLotStore evm I) (.var "tic_") =
        .ok (.int (Int.ofNat (dentTicPostWord evm I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((dentTicLocals evm I).get? "tic_") =
      .ok (.int (Int.ofNat (dentTicPostWord evm I).toNat))
    rw [dentTicLocals_get_tic]
    rfl
  have hnow :
      evalExpr? config { contract := contract, locals := dentTicLocals evm I }
          (dentAfterLotStore evm I) now48 =
        .ok (.int (Int.ofNat (dentNow48Word evm).toNat)) := by
    unfold now48 wrap48
    simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
    have hmod :
        Int.ofNat (UInt256.ofNat (dentAfterLotStore evm I).executionEnv.header.timestamp).toNat %
            uint48Modulus =
          Int.ofNat (dentNow48Word evm).toNat := by
      have hnowNat := dentNow48Word_toNat evm
      have henv :
          (UInt256.ofNat (dentAfterLotStore evm I).executionEnv.header.timestamp).toNat =
            (dentTimestampWord evm).toNat := by
        simp [dentTimestampWord, dentAfterLotStore_executionEnv]
      rw [henv, hnowNat]
      norm_num [uint48Modulus, Int.natCast_mod]
    simpa [uint48Modulus] using hmod
  have hticNat := dentTicPostWord_toNat evm I hfit
  have hge :
      Int.ofNat (dentNow48Word evm).toNat ≤
        Int.ofNat (dentTicPostWord evm I).toNat := by
    rw [hticNat]
    change Int.ofNat (dentNow48Word evm).toNat ≤
      Int.ofNat ((dentNow48Word evm).toNat +
        (dentTtlWord (dentAfterLotStore evm I)).toNat)
    exact Int.ofNat_le.mpr (Nat.le_add_right _ _)
  simp only [evalExpr?, htic, hnow, EvalResult.bind, bind, evalBinaryOp?]
  simpa using hge

theorem evalExpr_dent_tic_guard_false_wrapped (evm : EVM.State) (I : ExecutionEnv)
    (hoverflow :
      2 ^ 48 ≤
        (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat) :
    evalExpr? config { contract := contract, locals := dentTicWrappedLocals evm I }
        (dentAfterLotStore evm I)
      (.binary .ge (.var "tic_") now48) = .ok (.bool false) := by
  have htic :
      evalExpr? config { contract := contract, locals := dentTicWrappedLocals evm I }
          (dentAfterLotStore evm I) (.var "tic_") =
        .ok (.int (Int.ofNat (dentTicWrappedNat evm I))) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((dentTicWrappedLocals evm I).get? "tic_") =
      .ok (.int (Int.ofNat (dentTicWrappedNat evm I)))
    rw [dentTicWrappedLocals_get_tic]
    rfl
  have hnow :
      evalExpr? config { contract := contract, locals := dentTicWrappedLocals evm I }
          (dentAfterLotStore evm I) now48 =
        .ok (.int (Int.ofNat (dentNow48Word evm).toNat)) := by
    unfold now48 wrap48
    simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
    have hmod :
        Int.ofNat (UInt256.ofNat (dentAfterLotStore evm I).executionEnv.header.timestamp).toNat %
            uint48Modulus =
          Int.ofNat (dentNow48Word evm).toNat := by
      have hnowNat := dentNow48Word_toNat evm
      have henv :
          (UInt256.ofNat (dentAfterLotStore evm I).executionEnv.header.timestamp).toNat =
            (dentTimestampWord evm).toNat := by
        simp [dentTimestampWord, dentAfterLotStore_executionEnv]
      rw [henv, hnowNat]
      norm_num [uint48Modulus, Int.natCast_mod]
    simpa [uint48Modulus] using hmod
  have hnowLt : (dentNow48Word evm).toNat < 2 ^ 48 := by
    have h := dentNow48Word_toNat evm
    rw [h]
    exact Nat.mod_lt _ (by norm_num)
  have httlLt : (dentTtlWord (dentAfterLotStore evm I)).toNat < 2 ^ 48 := by
    simpa [dentTtlWord, flopperUint48Offset0Word, EVM.twoPow] using
      flopperUint48Masked_lt
        (flopperSlotWord ⟨6⟩ (dentAfterLotStore evm I).accountMap
          (dentAfterLotStore evm I).executionEnv)
  have hwrappedLt :
      dentTicWrappedNat evm I < (dentNow48Word evm).toNat := by
    unfold dentTicWrappedNat
    have hsumLt :
        (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat <
          2 ^ 49 := by
      omega
    rw [Nat.mod_eq_sub_mod hoverflow]
    have hsubLt :
        (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat -
            2 ^ 48 < 2 ^ 48 := by
      omega
    rw [Nat.mod_eq_of_lt hsubLt]
    omega
  have hdec :
      decide
          (Int.ofNat (dentNow48Word evm).toNat ≤
            Int.ofNat (dentTicWrappedNat evm I)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    exact (Nat.not_le_of_gt hwrappedLt) (Int.ofNat_le.mp hle)
  simp only [evalExpr?, htic, hnow, EvalResult.bind, bind, evalBinaryOp?]
  rw [hdec]

set_option maxHeartbeats 1000000 in
theorem assign_dentTicStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := dentTicLocals evm I }
        (dentAfterLotStore evm I)
      .storage (bidsF (.var "id") "tic")
        (.int (Int.ofNat (dentTicPostWord evm I).toNat % uint48Modulus)) =
      .ok ({ contract := contract, locals := dentTicLocals evm I }, dentPostState evm I) := by
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals := dentTicLocals evm I })
    (evm := dentAfterLotStore evm I)
    (evm' := dentPostState evm I)
    (slot := bidsF (.var "id") "tic")
    (er := dentTicEvaledRef I)
    (ty := uint48St)
    (loc := uint48Loc (auctionPackedSlot (dentIdWord I)) ⟨20, by decide⟩ (by decide))
    (n := Int.ofNat (dentTicPostWord evm I).toNat % uint48Modulus)
    (dentTicLocals_get_bids evm I)
    (by
      simpa [dentTicEvaledRef, dentIdValue] using
        evalStorageRef_auction_field (dentAfterLotStore evm I) (dentTicLocals evm I)
          (dentIdWord I) "tic"
          (by simpa [dentIdValue] using dentTicLocals_get_id evm I))
    (by
      simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint48St])
    (by
      funext evm'
      exact auctionTicLayout evm' (dentIdWord I))
    (by
      simpa [dentPostState, dentAfterTicStore, uint48Loc] using
        storageLocStore_uint48_offset20_word (dentAfterLotStore evm I)
          (auctionPackedSlot (dentIdWord I)) (dentTicPostWord evm I))

theorem dentTicPostWord_mod (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat <
        2 ^ 48) :
    Int.ofNat (dentTicPostWord evm I).toNat % uint48Modulus =
      Int.ofNat (dentTicPostWord evm I).toNat := by
  have hticNat := dentTicPostWord_toNat evm I hfit
  have hticLt : (dentTicPostWord evm I).toNat < 2 ^ 48 := by
    rw [hticNat]
    exact hfit
  have hticLtInt :
      Int.ofNat (dentTicPostWord evm I).toNat < uint48Modulus := by
    change Int.ofNat (dentTicPostWord evm I).toNat < Int.ofNat (2 ^ 48)
    exact Int.ofNat_lt.mpr hticLt
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) hticLtInt

theorem assign_dentTicStorage_value (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat <
        2 ^ 48) :
    assignStorageRef? config { contract := contract, locals := dentTicLocals evm I }
        (dentAfterLotStore evm I)
      .storage (bidsF (.var "id") "tic")
        (.int (Int.ofNat (dentTicPostWord evm I).toNat)) =
      .ok ({ contract := contract, locals := dentTicLocals evm I }, dentPostState evm I) := by
  rw [← dentTicPostWord_mod evm I hfit]
  exact assign_dentTicStorage evm I

theorem evalExpr_dent_tic_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentTicLocals evm I }
        (dentAfterLotStore evm I) (.var "tic_") =
      .ok (.int (Int.ofNat (dentTicPostWord evm I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((dentTicLocals evm I).get? "tic_") =
    .ok (.int (Int.ofNat (dentTicPostWord evm I).toNat))
  rw [dentTicLocals_get_tic]
  rfl

theorem evalExpr_dent_lot_var_moveLocals
    (startEvm evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentMoveLocals startEvm I } evm
        (.var "lot") =
      .ok (dentLotValue I) := by
  exact evalExpr_dent_var_of_get evm (dentMoveLocals_get_lot startEvm I)

theorem evalExpr_dent_now48_afterLot_of_locals
    (evm : EVM.State) (I : ExecutionEnv) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals }
        (dentAfterLotStore evm I) now48 =
      .ok (.int (Int.ofNat (dentNow48Word evm).toNat)) := by
  unfold now48 wrap48
  simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hmod :
      Int.ofNat (UInt256.ofNat (dentAfterLotStore evm I).executionEnv.header.timestamp).toNat %
          uint48Modulus =
        Int.ofNat (dentNow48Word evm).toNat := by
    have hnow := dentNow48Word_toNat evm
    have henv :
        (UInt256.ofNat (dentAfterLotStore evm I).executionEnv.header.timestamp).toNat =
          (dentTimestampWord evm).toNat := by
      simp [dentTimestampWord, dentAfterLotStore_executionEnv]
    rw [henv, hnow]
    norm_num [uint48Modulus, Int.natCast_mod]
  simpa [uint48Modulus] using hmod

theorem evalExpr_dent_ttl_storage_afterLot_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (httl : locals.get? "ttl" = none) :
    evalExpr? config { contract := contract, locals := locals }
        (dentAfterLotStore evm I) (.storage ttlRef) =
      .ok (.int (Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat)) := by
  let frame : Frame := { contract := contract, locals := locals }
  have hload :
      storageLocLoad (dentAfterLotStore evm I) (uint48Loc ⟨6⟩ ⟨0, by decide⟩ (by decide)) =
        .int (Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat) := by
    simpa [dentTtlWord, flopperUint48Offset0Word, flopperSlotWord] using
      flopperStorageLocLoad_uint48_offset0 (dentAfterLotStore evm I) ⟨6⟩
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := dentAfterLotStore evm I)
    (slot := ttlRef) (er := dentTtlEvaledRef)
    (t := .int uint48Int) (loc := uint48Loc ⟨6⟩ ⟨0, by decide⟩ (by decide))
    (value := .int (Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat))
    (by simpa [frame, ttlRef] using httl)
    (by simp [frame, dentTtlEvaledRef, evalStorageRef, evalStorageRefSteps,
      ttlRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint48St])
    (by rfl)
    hload

theorem evalExpr_dent_ticAdd_ok_moveLocals
    (startEvm evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat <
        2 ^ 48) :
    evalExpr? config { contract := contract, locals := dentMoveLocals startEvm I }
        (dentAfterLotStore evm I)
        (wrap48 (.binary .add now48 (.storage ttlRef))) =
      .ok (.int (Int.ofNat (dentTicPostWord evm I).toNat)) := by
  have hnow := evalExpr_dent_now48_afterLot_of_locals evm I (dentMoveLocals startEvm I)
  have httl := evalExpr_dent_ttl_storage_afterLot_of_locals evm I
    (locals := dentMoveLocals startEvm I)
    (by simp [dentMoveLocals, dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hticNat := dentTicPostWord_toNat evm I hfit
  unfold wrap48
  simp only [evalExpr?, hnow, httl, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hsumMod :
      (Int.ofNat (dentNow48Word evm).toNat +
          Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat) %
          uint48Modulus =
        Int.ofNat (dentTicPostWord evm I).toNat := by
    rw [hticNat]
    have hsumCast :
        Int.ofNat ((dentNow48Word evm).toNat +
            (dentTtlWord (dentAfterLotStore evm I)).toNat) =
          Int.ofNat (dentNow48Word evm).toNat +
            Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat := by
      norm_num
    rw [← hsumCast]
    have hfitInt :
        Int.ofNat ((dentNow48Word evm).toNat +
            (dentTtlWord (dentAfterLotStore evm I)).toNat) < uint48Modulus := by
      change Int.ofNat ((dentNow48Word evm).toNat +
          (dentTtlWord (dentAfterLotStore evm I)).toNat) < Int.ofNat (2 ^ 48)
      exact Int.ofNat_lt.mpr hfit
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) hfitInt
  simpa [uint48Modulus] using hsumMod

theorem evalExpr_dent_ticAdd_wrapped_moveLocals
    (startEvm evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentMoveLocals startEvm I }
        (dentAfterLotStore evm I)
        (wrap48 (.binary .add now48 (.storage ttlRef))) =
      .ok (.int (Int.ofNat
        (((dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat) %
          2 ^ 48))) := by
  have hnow := evalExpr_dent_now48_afterLot_of_locals evm I (dentMoveLocals startEvm I)
  have httl := evalExpr_dent_ttl_storage_afterLot_of_locals evm I
    (locals := dentMoveLocals startEvm I)
    (by simp [dentMoveLocals, dentLotOneLocals, dentBegLotLocals, dentLocals])
  unfold wrap48
  simp only [evalExpr?, hnow, httl, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hsumMod :
      (Int.ofNat (dentNow48Word evm).toNat +
          Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat) %
          uint48Modulus =
        Int.ofNat (((dentNow48Word evm).toNat +
          (dentTtlWord (dentAfterLotStore evm I)).toNat) % 2 ^ 48) := by
    have hsumCast :
        Int.ofNat ((dentNow48Word evm).toNat +
            (dentTtlWord (dentAfterLotStore evm I)).toNat) =
          Int.ofNat (dentNow48Word evm).toNat +
            Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat := by
      norm_num
    rw [← hsumCast]
    norm_num [uint48Modulus, Int.natCast_mod]
  simpa [uint48Modulus] using hsumMod

theorem evalExpr_dent_tic_guard_true_moveLocals
    (startEvm evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat <
        2 ^ 48) :
    evalExpr? config { contract := contract, locals := dentMoveTicLocals startEvm evm I }
        (dentAfterLotStore evm I)
      (.binary .ge (.var "tic_") now48) = .ok (.bool true) := by
  have htic :
      evalExpr? config { contract := contract, locals := dentMoveTicLocals startEvm evm I }
          (dentAfterLotStore evm I) (.var "tic_") =
        .ok (.int (Int.ofNat (dentTicPostWord evm I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((dentMoveTicLocals startEvm evm I).get? "tic_") =
      .ok (.int (Int.ofNat (dentTicPostWord evm I).toNat))
    rw [dentMoveTicLocals_get_tic]
    rfl
  have hnow := evalExpr_dent_now48_afterLot_of_locals evm I
    (dentMoveTicLocals startEvm evm I)
  have hticNat := dentTicPostWord_toNat evm I hfit
  have hge :
      Int.ofNat (dentNow48Word evm).toNat ≤
        Int.ofNat (dentTicPostWord evm I).toNat := by
    rw [hticNat]
    change Int.ofNat (dentNow48Word evm).toNat ≤
      Int.ofNat ((dentNow48Word evm).toNat +
        (dentTtlWord (dentAfterLotStore evm I)).toNat)
    exact Int.ofNat_le.mpr (Nat.le_add_right _ _)
  simp only [evalExpr?, htic, hnow, EvalResult.bind, bind, evalBinaryOp?]
  simpa using hge

theorem evalExpr_dent_tic_guard_false_wrapped_moveLocals
    (startEvm evm : EVM.State) (I : ExecutionEnv)
    (hoverflow :
      2 ^ 48 ≤
        (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat) :
    evalExpr? config { contract := contract, locals := dentMoveTicWrappedLocals startEvm evm I }
        (dentAfterLotStore evm I)
      (.binary .ge (.var "tic_") now48) = .ok (.bool false) := by
  have htic :
      evalExpr? config { contract := contract, locals := dentMoveTicWrappedLocals startEvm evm I }
          (dentAfterLotStore evm I) (.var "tic_") =
        .ok (.int (Int.ofNat
          (((dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat) %
            2 ^ 48))) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((dentMoveTicWrappedLocals startEvm evm I).get? "tic_") =
      .ok (.int (Int.ofNat
        (((dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat) %
          2 ^ 48)))
    rw [dentMoveTicWrappedLocals_get_tic]
    rfl
  have hnow := evalExpr_dent_now48_afterLot_of_locals evm I
    (dentMoveTicWrappedLocals startEvm evm I)
  have hnowLt : (dentNow48Word evm).toNat < 2 ^ 48 := by
    have h := dentNow48Word_toNat evm
    rw [h]
    exact Nat.mod_lt _ (by norm_num)
  have httlLt : (dentTtlWord (dentAfterLotStore evm I)).toNat < 2 ^ 48 := by
    simpa [dentTtlWord, flopperUint48Offset0Word, EVM.twoPow] using
      flopperUint48Masked_lt
        (flopperSlotWord ⟨6⟩ (dentAfterLotStore evm I).accountMap
          (dentAfterLotStore evm I).executionEnv)
  have hwrappedLt :
      ((dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat) %
          2 ^ 48 <
        (dentNow48Word evm).toNat := by
    have hsumLt :
        (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat <
          2 ^ 49 := by
      omega
    rw [Nat.mod_eq_sub_mod hoverflow]
    have hsubLt :
        (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat -
            2 ^ 48 < 2 ^ 48 := by
      omega
    rw [Nat.mod_eq_of_lt hsubLt]
    omega
  have hdec :
      decide
          (Int.ofNat (dentNow48Word evm).toNat ≤
            Int.ofNat (((dentNow48Word evm).toNat +
              (dentTtlWord (dentAfterLotStore evm I)).toNat) % 2 ^ 48)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    exact (Nat.not_le_of_gt hwrappedLt) (Int.ofNat_le.mp hle)
  simp only [evalExpr?, htic, hnow, EvalResult.bind, bind, evalBinaryOp?]
  rw [hdec]

set_option maxHeartbeats 1000000 in
theorem assign_dentTicStorage_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (dentIdValue I))
    (hbids : locals.get? "bids" = none) :
    assignStorageRef? config { contract := contract, locals := locals }
        (dentAfterLotStore evm I)
      .storage (bidsF (.var "id") "tic")
        (.int (Int.ofNat (dentTicPostWord evm I).toNat % uint48Modulus)) =
      .ok ({ contract := contract, locals := locals }, dentPostState evm I) := by
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (evm := dentAfterLotStore evm I)
    (evm' := dentPostState evm I)
    (slot := bidsF (.var "id") "tic")
    (er := dentTicEvaledRef I)
    (ty := uint48St)
    (loc := uint48Loc (auctionPackedSlot (dentIdWord I)) ⟨20, by decide⟩ (by decide))
    (n := Int.ofNat (dentTicPostWord evm I).toNat % uint48Modulus)
    hbids
    (by
      simpa [dentTicEvaledRef, dentIdValue] using
        evalStorageRef_auction_field (dentAfterLotStore evm I) locals
          (dentIdWord I) "tic" (by simpa [dentIdValue] using hid))
    (by
      simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint48St])
    (by
      funext evm'
      exact auctionTicLayout evm' (dentIdWord I))
    (by
      simpa [dentPostState, dentAfterTicStore, uint48Loc] using
        storageLocStore_uint48_offset20_word (dentAfterLotStore evm I)
          (auctionPackedSlot (dentIdWord I)) (dentTicPostWord evm I))

theorem assign_dentTicStorage_value_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (dentIdValue I))
    (hbids : locals.get? "bids" = none)
    (hfit :
      (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat <
        2 ^ 48) :
    assignStorageRef? config { contract := contract, locals := locals }
        (dentAfterLotStore evm I)
      .storage (bidsF (.var "id") "tic")
        (.int (Int.ofNat (dentTicPostWord evm I).toNat)) =
      .ok ({ contract := contract, locals := locals }, dentPostState evm I) := by
  rw [← dentTicPostWord_mod evm I hfit]
  exact assign_dentTicStorage_of_locals evm I hid hbids

theorem evalExpr_dent_tic_var_moveTicLocals
    (startEvm evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentMoveTicLocals startEvm evm I }
        (dentAfterLotStore evm I) (.var "tic_") =
      .ok (.int (Int.ofNat (dentTicPostWord evm I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((dentMoveTicLocals startEvm evm I).get? "tic_") =
    .ok (.int (Int.ofNat (dentTicPostWord evm I).toNat))
  rw [dentMoveTicLocals_get_tic]
  rfl

theorem evalExpr_dent_lot_var_kissRetLocals
    (startEvm evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? config { contract := contract, locals := dentKissRetLocals startEvm I out } evm
        (.var "lot") =
      .ok (dentLotValue I) := by
  exact evalExpr_dent_var_of_get evm (dentKissRetLocals_get_lot startEvm I out)

theorem evalExpr_dent_ticAdd_ok_kissRetLocals
    (startEvm evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hfit :
      (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat <
        2 ^ 48) :
    evalExpr? config { contract := contract, locals := dentKissRetLocals startEvm I out }
        (dentAfterLotStore evm I)
        (wrap48 (.binary .add now48 (.storage ttlRef))) =
      .ok (.int (Int.ofNat (dentTicPostWord evm I).toNat)) := by
  have hnow := evalExpr_dent_now48_afterLot_of_locals evm I
    (dentKissRetLocals startEvm I out)
  have httl := evalExpr_dent_ttl_storage_afterLot_of_locals evm I
    (locals := dentKissRetLocals startEvm I out)
    (dentKissRetLocals_get_ttl startEvm I out)
  have hticNat := dentTicPostWord_toNat evm I hfit
  unfold wrap48
  simp only [evalExpr?, hnow, httl, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hsumMod :
      (Int.ofNat (dentNow48Word evm).toNat +
          Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat) %
          uint48Modulus =
        Int.ofNat (dentTicPostWord evm I).toNat := by
    rw [hticNat]
    have hsumCast :
        Int.ofNat ((dentNow48Word evm).toNat +
            (dentTtlWord (dentAfterLotStore evm I)).toNat) =
          Int.ofNat (dentNow48Word evm).toNat +
            Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat := by
      norm_num
    rw [← hsumCast]
    have hfitInt :
        Int.ofNat ((dentNow48Word evm).toNat +
            (dentTtlWord (dentAfterLotStore evm I)).toNat) < uint48Modulus := by
      change Int.ofNat ((dentNow48Word evm).toNat +
          (dentTtlWord (dentAfterLotStore evm I)).toNat) < Int.ofNat (2 ^ 48)
      exact Int.ofNat_lt.mpr hfit
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) hfitInt
  simpa [uint48Modulus] using hsumMod

theorem evalExpr_dent_ticAdd_wrapped_kissRetLocals
    (startEvm evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? config { contract := contract, locals := dentKissRetLocals startEvm I out }
        (dentAfterLotStore evm I)
        (wrap48 (.binary .add now48 (.storage ttlRef))) =
      .ok (.int (Int.ofNat (dentTicWrappedNat evm I))) := by
  have hnow := evalExpr_dent_now48_afterLot_of_locals evm I
    (dentKissRetLocals startEvm I out)
  have httl := evalExpr_dent_ttl_storage_afterLot_of_locals evm I
    (locals := dentKissRetLocals startEvm I out)
    (dentKissRetLocals_get_ttl startEvm I out)
  unfold wrap48
  simp only [evalExpr?, hnow, httl, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hsumMod :
      (Int.ofNat (dentNow48Word evm).toNat +
          Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat) %
          uint48Modulus =
        Int.ofNat (dentTicWrappedNat evm I) := by
    have hsumCast :
        Int.ofNat ((dentNow48Word evm).toNat +
            (dentTtlWord (dentAfterLotStore evm I)).toNat) =
          Int.ofNat (dentNow48Word evm).toNat +
            Int.ofNat (dentTtlWord (dentAfterLotStore evm I)).toNat := by
      norm_num
    rw [← hsumCast]
    norm_num [dentTicWrappedNat, uint48Modulus, Int.natCast_mod]
  simpa [uint48Modulus] using hsumMod

theorem evalExpr_dent_tic_guard_true_kissRetLocals
    (startEvm evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hfit :
      (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat <
        2 ^ 48) :
    evalExpr? config { contract := contract, locals := dentKissRetTicLocals startEvm evm I out }
        (dentAfterLotStore evm I)
      (.binary .ge (.var "tic_") now48) = .ok (.bool true) := by
  have htic :
      evalExpr? config
          { contract := contract, locals := dentKissRetTicLocals startEvm evm I out }
          (dentAfterLotStore evm I) (.var "tic_") =
        .ok (.int (Int.ofNat (dentTicPostWord evm I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((dentKissRetTicLocals startEvm evm I out).get? "tic_") =
      .ok (.int (Int.ofNat (dentTicPostWord evm I).toNat))
    rw [dentKissRetTicLocals_get_tic]
    rfl
  have hnow := evalExpr_dent_now48_afterLot_of_locals evm I
    (dentKissRetTicLocals startEvm evm I out)
  have hticNat := dentTicPostWord_toNat evm I hfit
  have hge :
      Int.ofNat (dentNow48Word evm).toNat ≤
        Int.ofNat (dentTicPostWord evm I).toNat := by
    rw [hticNat]
    change Int.ofNat (dentNow48Word evm).toNat ≤
      Int.ofNat ((dentNow48Word evm).toNat +
        (dentTtlWord (dentAfterLotStore evm I)).toNat)
    exact Int.ofNat_le.mpr (Nat.le_add_right _ _)
  simp only [evalExpr?, htic, hnow, EvalResult.bind, bind, evalBinaryOp?]
  simpa using hge

theorem evalExpr_dent_tic_guard_false_wrapped_kissRetLocals
    (startEvm evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hoverflow :
      2 ^ 48 ≤
        (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat) :
    evalExpr? config
        { contract := contract, locals := dentKissRetTicWrappedLocals startEvm evm I out }
        (dentAfterLotStore evm I)
      (.binary .ge (.var "tic_") now48) = .ok (.bool false) := by
  have htic :
      evalExpr? config
          { contract := contract, locals := dentKissRetTicWrappedLocals startEvm evm I out }
          (dentAfterLotStore evm I) (.var "tic_") =
        .ok (.int (Int.ofNat (dentTicWrappedNat evm I))) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((dentKissRetTicWrappedLocals startEvm evm I out).get? "tic_") =
      .ok (.int (Int.ofNat (dentTicWrappedNat evm I)))
    rw [dentKissRetTicWrappedLocals_get_tic]
    rfl
  have hnow := evalExpr_dent_now48_afterLot_of_locals evm I
    (dentKissRetTicWrappedLocals startEvm evm I out)
  have hnowLt : (dentNow48Word evm).toNat < 2 ^ 48 := by
    have h := dentNow48Word_toNat evm
    rw [h]
    exact Nat.mod_lt _ (by norm_num)
  have httlLt : (dentTtlWord (dentAfterLotStore evm I)).toNat < 2 ^ 48 := by
    simpa [dentTtlWord, flopperUint48Offset0Word, EVM.twoPow] using
      flopperUint48Masked_lt
        (flopperSlotWord ⟨6⟩ (dentAfterLotStore evm I).accountMap
          (dentAfterLotStore evm I).executionEnv)
  have hwrappedLt :
      (dentTicWrappedNat evm I) < (dentNow48Word evm).toNat := by
    have hsumLt :
        (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat <
          2 ^ 49 := by
      omega
    rw [dentTicWrappedNat, Nat.mod_eq_sub_mod hoverflow]
    have hsubLt :
        (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat -
            2 ^ 48 < 2 ^ 48 := by
      omega
    rw [Nat.mod_eq_of_lt hsubLt]
    omega
  have hdec :
      decide
          (Int.ofNat (dentNow48Word evm).toNat ≤
            Int.ofNat (dentTicWrappedNat evm I)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    exact (Nat.not_le_of_gt hwrappedLt) (Int.ofNat_le.mp hle)
  simp only [evalExpr?, htic, hnow, EvalResult.bind, bind, evalBinaryOp?]
  rw [hdec]

theorem evalExpr_dent_tic_var_kissRetTicLocals
    (startEvm evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? config { contract := contract, locals := dentKissRetTicLocals startEvm evm I out }
        (dentAfterLotStore evm I) (.var "tic_") =
      .ok (.int (Int.ofNat (dentTicPostWord evm I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((dentKissRetTicLocals startEvm evm I out).get? "tic_") =
    .ok (.int (Int.ofNat (dentTicPostWord evm I).toNat))
  rw [dentKissRetTicLocals_get_tic]
  rfl

theorem flopperDentBodyReverts_notLive (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dentTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_dent_live_one_false evm I hlive)))

theorem flopperDentBodyReverts_guyNotSet (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I = ⟨0⟩) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dentTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_live_one_true evm I hlive)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_dent_guy_ne_zero_false evm I hguy)))

theorem flopperDentBodyReverts_ticFinished (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩)
    (hticNe : dentTicWord evm I ≠ ⟨0⟩)
    (hticLe : (dentTicWord evm I).toNat ≤ (dentTimestampWord evm).toNat) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dentTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_dent_tic_guard_false evm I hticNe hticLe)))

theorem flopperDentBodyReverts_endFinished (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat ∨
        dentTicWord evm I = ⟨0⟩)
    (hendLe : (dentEndWord evm I).toNat ≤ (dentTimestampWord evm).toNat) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dentTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_dent_end_gt_timestamp_false evm I hendLe)))

theorem flopperDentBodyReverts_bidMismatch (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat ∨
        dentTicWord evm I = ⟨0⟩)
    (hendGt : (dentTimestampWord evm).toNat < (dentEndWord evm I).toNat)
    (hbid : dentBidWord I ≠ dentBidStoredWord evm I) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dentTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_dent_bid_eq_false evm I hbid)))

theorem flopperDentBodyReverts_lotNotLower (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat ∨
        dentTicWord evm I = ⟨0⟩)
    (hendGt : (dentTimestampWord evm).toNat < (dentEndWord evm I).toNat)
    (hbid : dentBidWord I = dentBidStoredWord evm I)
    (hlotLe : (dentLotStoredWord evm I).toNat ≤ (dentLotWord I).toNat) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dentTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_bid_eq_true evm I hbid)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_dent_lot_lt_false evm I hlotLe)))

theorem flopperDentBodyReverts_begLotOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat ∨
        dentTicWord evm I = ⟨0⟩)
    (hendGt : (dentTimestampWord evm).toNat < (dentEndWord evm I).toNat)
    (hbid : dentBidWord I = dentBidStoredWord evm I)
    (hlotLt : (dentLotWord I).toNat < (dentLotStoredWord evm I).toNat)
    (hoverflow : UInt256.size ≤ (dentBegWord evm).toNat * (dentLotWord I).toNat) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dentTransition, nonpayable, checkedMulUintInto] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_bid_eq_true evm I hbid)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lot_lt_true evm I hlotLt)) <|
      ExecBlock.consRevert
        (ExecStmt.letDeclRevert (evalExpr_dent_begLot_overflow evm I hoverflow)))

theorem flopperDentBodyReverts_lotOneOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat ∨
        dentTicWord evm I = ⟨0⟩)
    (hendGt : (dentTimestampWord evm).toNat < (dentEndWord evm I).toNat)
    (hbid : dentBidWord I = dentBidStoredWord evm I)
    (hlotLt : (dentLotWord I).toNat < (dentLotStoredWord evm I).toNat)
    (hbegFit : (dentBegWord evm).toNat * (dentLotWord I).toNat < UInt256.size)
    (hoverflow : UInt256.size ≤ (dentLotStoredWord evm I).toNat * dentOneWord.toNat) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dentTransition, nonpayable, checkedMulUintInto, List.cons_append, List.nil_append]
    using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_bid_eq_true evm I hbid)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lot_lt_true evm I hlotLt)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_begLot_ok evm I hbegFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_begLot_mul_guard_true evm I hbegFit)) <|
      ExecBlock.consRevert
        (ExecStmt.letDeclRevert (evalExpr_dent_lotOne_overflow evm I hoverflow)))

end Benchmarks.Dss.Flopper
