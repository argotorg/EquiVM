import Benchmarks.Dss.Flipper.Dispatch
import Benchmarks.Dss.Flipper.BidAccess
import Benchmarks.Dss.Flipper.ErrorStringFull

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flipper

/-! ## `tend(uint256,uint256,uint256)` -/

abbrev tendId (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev tendLot (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev tendBid (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev tendLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "id" (.int (Int.ofNat (tendId I).toNat))).insert
    "lot" (.int (Int.ofNat (tendLot I).toNat))).insert
    "bid" (.int (Int.ofNat (tendBid I).toNat))

theorem tendLocals_get_id (I : ExecutionEnv) :
    (tendLocals I).get? "id" = some (.int (Int.ofNat (tendId I).toNat)) := by
  rw [tendLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem tendLocals_get_lot (I : ExecutionEnv) :
    (tendLocals I).get? "lot" = some (.int (Int.ofNat (tendLot I).toNat)) := by
  rw [tendLocals, store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem tendLocals_get_bid (I : ExecutionEnv) :
    (tendLocals I).get? "bid" = some (.int (Int.ofNat (tendBid I).toNat)) := by
  rw [tendLocals, store_get_self]

theorem tendLocals_get_bids (I : ExecutionEnv) :
    (tendLocals I).get? "bids" = none := by
  rw [tendLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_tendGuyNeZero_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguy : bidGuyWord (tendId I) σ I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
        .ok (.bool false) := by
  have hguyEval :=
    evalExpr_bidGuy_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := tendLocals I) (id := tendId I) (tendLocals_get_id I)
      (tendLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hguyEval]
  simp [evalExpr?, evalBinaryOp?, zeroAddr, hguy]
  all_goals decide

theorem evalExpr_tendGuyNeZero_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
        .ok (.bool true) := by
  have hguyEval :=
    evalExpr_bidGuy_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := tendLocals I) (id := tendId I) (tendLocals_get_id I)
      (tendLocals_get_bids I)
  have hguyAddr :
      AccountAddress.ofNat (bidGuyWord (tendId I) σ I).toNat ≠ AccountAddress.ofNat 0 := by
    intro hzeroAddr
    have hmask := keyValueToWord_address_ofNat_mask (bidGuyWord (tendId I) σ I)
    rw [hzeroAddr] at hmask
    have hclean :
        UInt256.land solcAddrMask (bidGuyWord (tendId I) σ I) =
          bidGuyWord (tendId I) σ I := by
      simpa [bidGuyWord, flipperAddressReturnWord, u256_land_comm] using
        (solcAddrMask_clean
          (solcAddrMask_result_canonical
            (flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ I)))
    exact hguy (by simpa [keyValueToWord_address, hclean] using hmask.symm)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hguyEval]
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, bind, pure,
    EvalResult.ofOption]
  norm_num [evalBinaryOp?]
  · exact hguyAddr
  all_goals
    intro h
    cases h

theorem evalExpr_tendTicGtTimestamp_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle : (bidTicWord (tendId I) σ I).toNat ≤ (UInt256.ofNat I.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
        .ok (.bool false) := by
  have hticEval :=
    evalExpr_bidTic_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := tendLocals I) (id := tendId I) (tendLocals_get_id I)
      (tendLocals_get_bids I)
  have hnot : ¬ (UInt256.ofNat I.header.timestamp).toNat <
      (bidTicWord (tendId I) σ I).toNat := by
    omega
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hticEval]
  simp [evalExpr?, envValue, initState, evalBinaryOp?, hnot]
  all_goals decide

theorem evalExpr_tendTicGtTimestamp_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : (UInt256.ofNat I.header.timestamp).toNat <
      (bidTicWord (tendId I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
        .ok (.bool true) := by
  have hticEval :=
    evalExpr_bidTic_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := tendLocals I) (id := tendId I) (tendLocals_get_id I)
      (tendLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hticEval]
  simp [evalExpr?, envValue, initState, evalBinaryOp?, hlt]
  all_goals decide

theorem evalExpr_tendTicEqZero_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (htic : bidTicWord (tendId I) σ I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
        .ok (.bool false) := by
  have hticEval :=
    evalExpr_bidTic_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := tendLocals I) (id := tendId I) (tendLocals_get_id I)
      (tendLocals_get_bids I)
  have hneNat : ¬ (bidTicWord (tendId I) σ I).toNat = 0 := by
    intro hzero
    exact htic (uint256_toNat_eq_zero hzero)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hticEval]
  simp [evalExpr?, evalBinaryOp?, hneNat]
  all_goals decide

theorem evalExpr_tendTicEqZero_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (htic : bidTicWord (tendId I) σ I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
        .ok (.bool true) := by
  have hticEval :=
    evalExpr_bidTic_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := tendLocals I) (id := tendId I) (tendLocals_get_id I)
      (tendLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hticEval]
  simp [evalExpr?, evalBinaryOp?, htic]
  all_goals decide

theorem evalExpr_tendTicActive_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (htic : bidTicWord (tendId I) σ I ≠ ⟨0⟩)
    (hle : (bidTicWord (tendId I) σ I).toNat ≤ (UInt256.ofNat I.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .or
        (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool false) := by
  have hgt := evalExpr_tendTicGtTimestamp_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hle
  have heq := evalExpr_tendTicEqZero_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) htic
  simp [evalExpr?, EvalResult.bind, bind, pure, hgt, heq]

theorem evalExpr_tendTicActive_true_left {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : (UInt256.ofNat I.header.timestamp).toNat <
      (bidTicWord (tendId I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .or
        (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
  have hgt := evalExpr_tendTicGtTimestamp_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hlt
  simp [evalExpr?, EvalResult.bind, bind, pure, hgt]

theorem evalExpr_tendTicActive_true_right {cA gh bl σ σ₀ A I} {g : Sat256}
    (htic : bidTicWord (tendId I) σ I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .or
        (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
  have hle : (bidTicWord (tendId I) σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat := by
    simp [htic]
  have hgt := evalExpr_tendTicGtTimestamp_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hle
  have heq := evalExpr_tendTicEqZero_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) htic
  simp [evalExpr?, EvalResult.bind, bind, pure, hgt, heq]

theorem evalExpr_tendEndGtTimestamp_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle : (bidEndWord (tendId I) σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool false) := by
  have hendEval :=
    evalExpr_bidEnd_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := tendLocals I) (id := tendId I) (tendLocals_get_id I)
      (tendLocals_get_bids I)
  have hnot : ¬ (UInt256.ofNat I.header.timestamp).toNat <
      (bidEndWord (tendId I) σ I).toNat := by
    omega
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hendEval]
  simp [evalExpr?, envValue, initState, evalBinaryOp?, hnot]
  all_goals decide

theorem evalExpr_tendEndGtTimestamp_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : (UInt256.ofNat I.header.timestamp).toNat <
      (bidEndWord (tendId I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool true) := by
  have hendEval :=
    evalExpr_bidEnd_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := tendLocals I) (id := tendId I) (tendLocals_get_id I)
      (tendLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hendEval]
  simp [evalExpr?, envValue, initState, evalBinaryOp?, hlt]
  all_goals decide

theorem evalExpr_tendLotEqBidLot_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlot : tendLot I ≠ bidLotWord (tendId I) σ I) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
        .ok (.bool false) := by
  have hlotVar :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ g A I) (.var "lot") =
          .ok (.int (Int.ofNat (tendLot I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((tendLocals I).get? "lot") =
      .ok (.int (Int.ofNat (tendLot I).toNat))
    rw [tendLocals_get_lot]
    rfl
  have hlotEval :=
    evalExpr_bidLot_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := tendLocals I) (id := tendId I) (tendLocals_get_id I)
      (tendLocals_get_bids I)
  have hneNat : ¬ (tendLot I).toNat = (bidLotWord (tendId I) σ I).toNat := by
    intro hnat
    exact hlot (u256_inj hnat)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hlotVar, hlotEval]
  simp [evalBinaryOp?, hneNat]
  all_goals decide

theorem evalExpr_tendLotEqBidLot_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlot : tendLot I = bidLotWord (tendId I) σ I) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
        .ok (.bool true) := by
  have hlotVar :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ g A I) (.var "lot") =
          .ok (.int (Int.ofNat (tendLot I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((tendLocals I).get? "lot") =
      .ok (.int (Int.ofNat (tendLot I).toNat))
    rw [tendLocals_get_lot]
    rfl
  have hlotEval :=
    evalExpr_bidLot_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := tendLocals I) (id := tendId I) (tendLocals_get_id I)
      (tendLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hlotVar, hlotEval]
  simp [evalBinaryOp?, hlot]
  all_goals decide

theorem evalExpr_tendBidLeBidTab_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hgt : (bidTabWord (tendId I) σ I).toNat < (tendBid I).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
        .ok (.bool false) := by
  have hbidVar :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ g A I) (.var "bid") =
          .ok (.int (Int.ofNat (tendBid I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((tendLocals I).get? "bid") =
      .ok (.int (Int.ofNat (tendBid I).toNat))
    rw [tendLocals_get_bid]
    rfl
  have htabEval :=
    evalExpr_bidTab_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := tendLocals I) (id := tendId I) (tendLocals_get_id I)
      (tendLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hbidVar, htabEval]
  simp [evalBinaryOp?]
  · exact hgt
  all_goals decide

theorem evalExpr_tendBidLeBidTab_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle : (tendBid I).toNat ≤ (bidTabWord (tendId I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
        .ok (.bool true) := by
  have hbidVar :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ g A I) (.var "bid") =
          .ok (.int (Int.ofNat (tendBid I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((tendLocals I).get? "bid") =
      .ok (.int (Int.ofNat (tendBid I).toNat))
    rw [tendLocals_get_bid]
    rfl
  have htabEval :=
    evalExpr_bidTab_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := tendLocals I) (id := tendId I) (tendLocals_get_id I)
      (tendLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hbidVar, htabEval]
  simp [evalBinaryOp?]
  · exact hle
  all_goals decide

theorem flipperTendSourceBodyGuyNotSet {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I = ⟨0⟩) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
  intro locals evm0
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_tendGuyNeZero_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hguy
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguyGuard)
  simpa [ExecTransitionBody, tendTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem flipperTendSourceBodyAlreadyFinishedTic {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (htic : bidTicWord (tendId I) σ I ≠ ⟨0⟩)
    (hle : (bidTicWord (tendId I) σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
  intro locals evm0
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_tendGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hguy
  have hticGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_tendTicActive_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        htic hle
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hticGuard)
  simpa [ExecTransitionBody, tendTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem flipperTendSourceBodyAlreadyFinishedEnd {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendLe : (bidEndWord (tendId I) σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
  intro locals evm0
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_tendGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hguy
  have hticGuardLocal :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true) := by
    simpa [locals, evm0] using hticGuard
  have hendGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_tendEndGtTimestamp_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hendLe
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hticGuardLocal) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hendGuard)
  simpa [ExecTransitionBody, tendTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem flipperTendSourceBodyLotNotMatching {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlot : tendLot I ≠ bidLotWord (tendId I) σ I) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
  intro locals evm0
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_tendGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hguy
  have hticGuardLocal :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true) := by
    simpa [locals, evm0] using hticGuard
  have hendGuardLocal :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true) := by
    simpa [locals, evm0] using hendGuard
  have hlotGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_tendLotEqBidLot_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hlot
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hticGuardLocal) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hendGuardLocal) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hlotGuard)
  simpa [ExecTransitionBody, tendTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem flipperTendSourceBodyHigherThanTab {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (hgt : (bidTabWord (tendId I) σ I).toNat < (tendBid I).toNat) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
  intro locals evm0
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_tendGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hguy
  have hticGuardLocal :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true) := by
    simpa [locals, evm0] using hticGuard
  have hendGuardLocal :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true) := by
    simpa [locals, evm0] using hendGuard
  have hlotGuardLocal :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true) := by
    simpa [locals, evm0] using hlotGuard
  have htabGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_tendBidLeBidTab_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hgt
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hticGuardLocal) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hendGuardLocal) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hlotGuardLocal) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse htabGuard)
  simpa [ExecTransitionBody, tendTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

noncomputable abbrev tendHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (tendId I) ⟨1⟩ solcFreePtrMem

noncomputable abbrev tendHashMem1 (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (tendId I) ⟨1⟩ (tendHashMem I)

noncomputable abbrev tendHashMem2 (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (tendId I) ⟨1⟩ (tendHashMem1 I)

theorem tendHashMem_size (I : ExecutionEnv) :
    (tendHashMem I).size = 96 := by
  unfold tendHashMem
  exact twoWordHashMem_size_96 (tendId I) ⟨1⟩ solcFreePtrMem_size

theorem tendHashMem_read64 (I : ExecutionEnv) :
    (tendHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold tendHashMem
  exact twoWordHashMem_read64 (tendId I) ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64

theorem tendHashMem1_size (I : ExecutionEnv) :
    (tendHashMem1 I).size = 96 := by
  unfold tendHashMem1
  exact twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem_size I)

theorem tendHashMem1_read64 (I : ExecutionEnv) :
    (tendHashMem1 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold tendHashMem1
  exact twoWordHashMem_read64 (tendId I) ⟨1⟩ (tendHashMem_size I) (tendHashMem_read64 I)

theorem tendHashMem2_size (I : ExecutionEnv) :
    (tendHashMem2 I).size = 96 := by
  unfold tendHashMem2
  exact twoWordHashMem_size_96 (tendId I) ⟨1⟩ (tendHashMem1_size I)

theorem tendHashMem2_read64 (I : ExecutionEnv) :
    (tendHashMem2 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold tendHashMem2
  exact twoWordHashMem_read64 (tendId I) ⟨1⟩ (tendHashMem1_size I)
    (tendHashMem1_read64 I)

abbrev flipperAlreadyFinishedTicWord : UInt256 :=
  ⟨31853446598541861569097437671217369822383545270177637832041123590441915121664⟩

abbrev flipperTendAlreadyFinishedEndWord : UInt256 :=
  ⟨31853446598541861569097437671217369822383545270177637832041119373819117568000⟩

abbrev flipperTendLotNotMatchingWord : UInt256 :=
  ⟨31853446598541861569367444895842886991173014508583632875832765480833818558464⟩

abbrev flipperTendHigherThanTabWord : UInt256 :=
  ⟨31853446598541861569268785717699472785673837977477559993563557443338227417088⟩

theorem flipperTendDecodePushMask2788 :
    decode flipperBytecode (⟨2788⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperTendDecodePushMask2828 :
    decode flipperBytecode (⟨2828⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperTendDecodePushMask2946 :
    decode flipperBytecode (⟨2946⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperDecode_tend_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
      (transitionSignature tendTransition).paramTypes I.calldata =
        some (tendLocals I) := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "lot", "bid"]
      [abiUInt256, abiUInt256, abiUInt256] I.calldata = some (tendLocals I)
  exact flipperDecodeCalldataLegacyUInt256UInt256UInt256_ok (cd := I.calldata)
    (x := "id") (y := "lot") (z := "bid") hsz100

theorem flipperDecode_tend_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
      (transitionSignature tendTransition).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "lot", "bid"]
      [abiUInt256, abiUInt256, abiUInt256] I.calldata = none
  exact flipperDecodeCalldataLegacyUInt256UInt256UInt256_none_short (cd := I.calldata)
    (x := "id") (y := "lot") (z := "bid") hsz4 hshort

theorem flipperReachTendBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flipperSelBytes 13)) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨594⟩ [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flipperSelWord I = ⟨0x4b43ed12⟩ :=
    flipperSelWord_eq_of_beq I hsz 0x4b 0x43 0xed 0x12 ⟨0x4b43ed12⟩
      (by native_decide) (by simpa [flipperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flipperBytecode flipperHighSplitPc)
      (flipperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighHighFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighHighFirstArmPc 1))
        (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact flipperReachHighHighBody 1 (by omega) ⟨594⟩ hcode hwv hsz hsize hroot hhigh
    heq0 htake (by jump_dest) (by native_decide)

theorem RD.flipperTendDecodeToRoutine {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨616⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = flipperBytecode)
    (hroutine : (D_J code 0).contains ⟨2662⟩ = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨2662⟩
      (calldataWord ee.calldata 68 :: calldataWord ee.calldata 36 ::
        calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd2662 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw push2 ⟨2662⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) hroutine (by evm_ov)]
  exact ⟨_, _, by
    simpa [calldataWord, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using rd2662⟩

theorem flipperTendX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨594⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2662⟩
        [tendBid I, tendLot I, tendId I, ⟨323⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flipperBytecode) (sel := sel) (entry := ⟨594⟩) (ret := ⟨323⟩)
    (decoded := ⟨616⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.flipperTendDecodeToRoutine
    (code := flipperBytecode) (ret := ⟨323⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [tendBid, tendLot, tendId] using hroutine⟩

theorem flipperTendX_guyNotSet {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hguy : bidGuyWord (tendId I) σ I = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨2662⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd2679 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (tendHashMem I) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [tendHashMem, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) solcFreePtrMem_size)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k2680, C2680, rd2680raw⟩ := rd2679.sload (by native_decide) (by evm_ov)
  have rd2681 : RD flipperBytecode I g s0 ⟨2681⟩
      (bidPackedWord (tendId I) σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2680 C2680 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (tendId I) = bidPackedSlotOfWord (tendId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd2680raw
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hguyClean :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (bidPackedWord (tendId I) σ I) = ⟨0⟩ := by
    rw [hmask160, u256_land_comm]
    simpa [bidGuyWord, bidPackedWord, flipperAddressReturnWord] using hguy
  have rd2694 := evm_run rd2681 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push2 ⟨2760⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) hguyClean (by evm_ov)]
  have hwf :
      solcErrorStringRevertTailWf flipperBytecode ⟨2694⟩ ⟨19⟩
        ⟨0x119b1a5c1c195c8bd9dd5e4b5b9bdd0b5cd95d⟩ ⟨106⟩ .PUSH19 19 := by
    unfold solcErrorStringRevertTailWf
    repeat' first | apply And.intro | native_decide
  exact RD.solcErrorStringRevertTail
    (pc := ⟨2694⟩) (len := ⟨19⟩)
    (rawWord := ⟨0x119b1a5c1c195c8bd9dd5e4b5b9bdd0b5cd95d⟩)
    (shift := ⟨106⟩)
    (word := UInt256.shiftLeft
      (⟨0x119b1a5c1c195c8bd9dd5e4b5b9bdd0b5cd95d⟩ : UInt256) ⟨106⟩)
    (op := .PUSH19) (width := 19) rd2694
    hwf (by decide) rfl (tendHashMem_size I) (tendHashMem_read64 I) (by simp)

theorem flipperTendX_guyOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨2662⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2760⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      (tendHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2679 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (tendHashMem I) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [tendHashMem, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) solcFreePtrMem_size)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k2680, C2680, rd2680raw⟩ := rd2679.sload (by native_decide) (by evm_ov)
  have rd2681 : RD flipperBytecode I g s0 ⟨2681⟩
      (bidPackedWord (tendId I) σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2680 C2680 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (tendId I) = bidPackedSlotOfWord (tendId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd2680raw
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hguyClean :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (bidPackedWord (tendId I) σ I) ≠ ⟨0⟩ := by
    intro hzero
    exact hguy (by
      rw [hmask160, u256_land_comm] at hzero
      simpa [bidGuyWord, bidPackedWord, flipperAddressReturnWord] using hzero)
  have rd2760 := evm_run rd2681 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push2 ⟨2760⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) hguyClean (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd2760⟩

theorem flipperTendX_alreadyFinishedTic {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hticNe : bidTicWord (tendId I) σ I ≠ ⟨0⟩)
    (hticLe : (bidTicWord (tendId I) σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat)
    (h : RD flipperBytecode I g s0 ⟨2760⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      (tendHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd2778 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) (tendHashMem I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (tendHashMem1 I) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [tendHashMem1, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) (tendHashMem_size I))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k2778, C2778, rd2778raw⟩ := rd2778.sload (by native_decide) (by evm_ov)
  have rd2779 : RD flipperBytecode I g s0 ⟨2779⟩
      (bidPackedWord (tendId I) σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2778 C2778 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (tendId I) = bidPackedSlotOfWord (tendId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd2778raw
  have rd2797 := evm_run rd2779 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTendDecodePushMask2788 (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  have hticGt0 :
      UInt256.gt
        (UInt256.land uint48Mask
          (UInt256.div (bidPackedWord (tendId I) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)))
        (UInt256.ofNat I.header.timestamp) = ⟨0⟩ := by
    simpa [bidTicWord, bidPackedWord, flipperUint48Offset20Word, uint48Divisor20,
      u256_land_comm] using (ugt_zero hticLe)
  rw [hticGt0] at rd2797
  have rd2803 := evm_run rd2797 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨2837⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd2820 := evm_run rd2803 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) (tendHashMem1 I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (tendHashMem2 I) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [tendHashMem2, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) (tendHashMem1_size I))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k2820, C2820, rd2820raw⟩ := rd2820.sload (by native_decide) (by evm_ov)
  have rd2821 : RD flipperBytecode I g s0 ⟨2821⟩
      (bidPackedWord (tendId I) σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2820 C2820 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (tendId I) = bidPackedSlotOfWord (tendId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd2820raw
  have rd2837raw := evm_run rd2821 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTendDecodePushMask2828 (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  have hticRaw :
      UInt256.land uint48Mask
        (UInt256.div (bidPackedWord (tendId I) σ I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)) =
        bidTicWord (tendId I) σ I := by
    simp [bidTicWord, bidPackedWord, flipperUint48Offset20Word, uint48Divisor20,
      u256_land_comm]
  rw [hticRaw] at rd2837raw
  rw [Reasoning.Theory.isZero_eq_zero_of_ne hticNe] at rd2837raw
  have rd2838 := rd2837raw.jumpdest (by native_decide) (by evm_ov)
  have rd2842 := evm_run rd2838 with [
    raw push2 ⟨2918⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  have rdMload := evm_run rd2842 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [tendHashMem2_size I]; decide) (by decide)
        (tendHashMem2_read64 I))
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 (tendHashMem2 I)) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 (tendHashMem2 I)) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨28⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 (⟨28⟩ : UInt256) (tendHashMem2 I))
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst flipperAlreadyFinishedTicWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 (⟨28⟩ : UInt256) flipperAlreadyFinishedTicWord
        (tendHashMem2 I))
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide) mem_cost
      (solcErrorStringMem3_mload64 (⟨28⟩ : UInt256) flipperAlreadyFinishedTicWord
        (tendHashMem2_size I) (tendHashMem2_read64 I))
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem flipperTendX_ticGtOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hticGt : (UInt256.ofNat I.header.timestamp).toNat <
      (bidTicWord (tendId I) σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨2760⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      (tendHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2918⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      (tendHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2778 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) (tendHashMem I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (tendHashMem1 I) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [tendHashMem1, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) (tendHashMem_size I))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k2778, C2778, rd2778raw⟩ := rd2778.sload (by native_decide) (by evm_ov)
  have rd2779 : RD flipperBytecode I g s0 ⟨2779⟩
      (bidPackedWord (tendId I) σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2778 C2778 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (tendId I) = bidPackedSlotOfWord (tendId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd2778raw
  have rd2797 := evm_run rd2779 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTendDecodePushMask2788 (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  have hticGt1 :
      UInt256.gt
        (UInt256.land uint48Mask
          (UInt256.div (bidPackedWord (tendId I) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)))
        (UInt256.ofNat I.header.timestamp) = ⟨1⟩ := by
    simpa [bidTicWord, bidPackedWord, flipperUint48Offset20Word, uint48Divisor20,
      u256_land_comm] using (ugt_one hticGt)
  rw [hticGt1] at rd2797
  have rd2837 := evm_run rd2797 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨2837⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  have rd2838 := rd2837.jumpdest (by native_decide) (by evm_ov)
  have rd2918 := evm_run rd2838 with [
    raw push2 ⟨2918⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd2918⟩

theorem flipperTendX_ticZeroOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (htic : bidTicWord (tendId I) σ I = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨2760⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      (tendHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2918⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      (tendHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2778 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) (tendHashMem I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (tendHashMem1 I) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [tendHashMem1, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) (tendHashMem_size I))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k2778, C2778, rd2778raw⟩ := rd2778.sload (by native_decide) (by evm_ov)
  have rd2779 : RD flipperBytecode I g s0 ⟨2779⟩
      (bidPackedWord (tendId I) σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2778 C2778 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (tendId I) = bidPackedSlotOfWord (tendId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd2778raw
  have rd2797 := evm_run rd2779 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTendDecodePushMask2788 (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  have hticGt0 :
      UInt256.gt
        (UInt256.land uint48Mask
          (UInt256.div (bidPackedWord (tendId I) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)))
        (UInt256.ofNat I.header.timestamp) = ⟨0⟩ := by
    have hle : (bidTicWord (tendId I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat := by
      simp [htic]
    simpa [bidTicWord, bidPackedWord, flipperUint48Offset20Word, uint48Divisor20,
      u256_land_comm] using (ugt_zero hle)
  rw [hticGt0] at rd2797
  have rd2803 := evm_run rd2797 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨2837⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd2820 := evm_run rd2803 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) (tendHashMem1 I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (tendHashMem2 I) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [tendHashMem2, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) (tendHashMem1_size I))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k2820, C2820, rd2820raw⟩ := rd2820.sload (by native_decide) (by evm_ov)
  have rd2821 : RD flipperBytecode I g s0 ⟨2821⟩
      (bidPackedWord (tendId I) σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2820 C2820 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (tendId I) = bidPackedSlotOfWord (tendId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd2820raw
  have rd2837raw := evm_run rd2821 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTendDecodePushMask2828 (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  have hticRaw :
      UInt256.land uint48Mask
        (UInt256.div (bidPackedWord (tendId I) σ I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)) =
        bidTicWord (tendId I) σ I := by
    simp [bidTicWord, bidPackedWord, flipperUint48Offset20Word, uint48Divisor20,
      u256_land_comm]
  rw [hticRaw, htic] at rd2837raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2837raw
  have rd2838 := rd2837raw.jumpdest (by native_decide) (by evm_ov)
  have rd2918 := evm_run rd2838 with [
    raw push2 ⟨2918⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd2918⟩

theorem flipperTendX_endOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hendGt : (UInt256.ofNat I.header.timestamp).toNat <
      (bidEndWord (tendId I) σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨2918⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3035⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2936 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (tendId I) ⟨1⟩ mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) hmemSize)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k2936, C2936, rd2936raw⟩ := rd2936.sload (by native_decide) (by evm_ov)
  have rd2937 : RD flipperBytecode I g s0 ⟨2937⟩
      (bidPackedWord (tendId I) σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2936 C2936 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (tendId I) = bidPackedSlotOfWord (tendId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd2936raw
  have rd2955 := evm_run rd2937 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTendDecodePushMask2946 (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  have hendGt1 :
      UInt256.gt
        (UInt256.land uint48Mask
          (UInt256.div (bidPackedWord (tendId I) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)))
        (UInt256.ofNat I.header.timestamp) = ⟨1⟩ := by
    simpa [bidEndWord, bidPackedWord, flipperUint48Offset26Word, uint48Divisor26,
      u256_land_comm] using (ugt_one hendGt)
  rw [hendGt1] at rd2955
  have rd3035 := evm_run rd2955 with [
    raw push2 ⟨3035⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd3035⟩

theorem flipperTendX_alreadyFinishedEnd {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hendLe : (bidEndWord (tendId I) σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat)
    (h : RD flipperBytecode I g s0 ⟨2918⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  let memEnd := twoWordHashMem (tendId I) ⟨1⟩ mem
  have hmemEndSize : memEnd.size = 96 := by
    dsimp [memEnd]
    exact twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmemSize
  have hmemEndRead64 :
      memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memEnd]
    exact twoWordHashMem_read64 (tendId I) ⟨1⟩ hmemSize hmemRead64
  have rd2936 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 memEnd (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by
        dsimp [memEnd]
        simpa [bidBaseOfWord] using
          twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) hmemSize)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k2936, C2936, rd2936raw⟩ := rd2936.sload (by native_decide) (by evm_ov)
  have rd2937 : RD flipperBytecode I g s0 ⟨2937⟩
      (bidPackedWord (tendId I) σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2936 C2936 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (tendId I) = bidPackedSlotOfWord (tendId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [memEnd, bidPackedWord, flipperSlotWord, hslotAdd]
      using rd2936raw
  have rd2955 := evm_run rd2937 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTendDecodePushMask2946 (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  have hendGt0 :
      UInt256.gt
        (UInt256.land uint48Mask
          (UInt256.div (bidPackedWord (tendId I) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)))
        (UInt256.ofNat I.header.timestamp) = ⟨0⟩ := by
    simpa [bidEndWord, bidPackedWord, flipperUint48Offset26Word, uint48Divisor26,
      u256_land_comm] using (ugt_zero hendLe)
  rw [hendGt0] at rd2955
  have rd2959 := evm_run rd2955 with [
    raw push2 ⟨3035⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  have rdMload := evm_run rd2959 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmemEndSize]; decide) (by decide) hmemEndRead64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 memEnd) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 memEnd) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨28⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 (⟨28⟩ : UInt256) memEnd)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst flipperTendAlreadyFinishedEndWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 (⟨28⟩ : UInt256) flipperTendAlreadyFinishedEndWord memEnd)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide) mem_cost
      (solcErrorStringMem3_mload64 (⟨28⟩ : UInt256) flipperTendAlreadyFinishedEndWord
        hmemEndSize hmemEndRead64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem flipperTendX_lotOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hlot : tendLot I = bidLotWord (tendId I) σ I)
    (h : RD flipperBytecode I g s0 ⟨3035⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3137⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3054 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (tendId I) ⟨1⟩ mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) hmemSize)
      (by decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k3054, C3054, rd3054raw⟩ := rd3054.sload (by native_decide) (by evm_ov)
  have rd3055 : RD flipperBytecode I g s0 ⟨3055⟩
      (bidLotWord (tendId I) σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3054 C3054 := by
    have hslotAdd :
        (⟨1⟩ : UInt256) + bidBaseOfWord (tendId I) = bidSlotOfWord (tendId I) ⟨1⟩ := by
      simpa [bidSlotOfWord] using
        (u256_add_comm (⟨1⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [bidLotWord, flipperSlotWord, hslotAdd]
      using rd3054raw
  have rd3057raw := evm_run rd3055 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq :
      UInt256.eq (tendLot I) (bidLotWord (tendId I) σ I) = ⟨1⟩ := by
    rw [hlot]
    exact u256_eq_refl _
  rw [heq] at rd3057raw
  have rd3137 := evm_run rd3057raw with [
    raw push2 ⟨3137⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd3137⟩

theorem flipperTendX_lotNotMatching {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlot : tendLot I ≠ bidLotWord (tendId I) σ I)
    (h : RD flipperBytecode I g s0 ⟨3035⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  let memLot := twoWordHashMem (tendId I) ⟨1⟩ mem
  have hmemLotSize : memLot.size = 96 := by
    dsimp [memLot]
    exact twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmemSize
  have hmemLotRead64 :
      memLot.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memLot]
    exact twoWordHashMem_read64 (tendId I) ⟨1⟩ hmemSize hmemRead64
  have rd3054 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 memLot (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by
        dsimp [memLot]
        simpa [bidBaseOfWord] using
          twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) hmemSize)
      (by decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k3054, C3054, rd3054raw⟩ := rd3054.sload (by native_decide) (by evm_ov)
  have rd3055 : RD flipperBytecode I g s0 ⟨3055⟩
      (bidLotWord (tendId I) σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3054 C3054 := by
    have hslotAdd :
        (⟨1⟩ : UInt256) + bidBaseOfWord (tendId I) = bidSlotOfWord (tendId I) ⟨1⟩ := by
      simpa [bidSlotOfWord] using
        (u256_add_comm (⟨1⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [memLot, bidLotWord, flipperSlotWord, hslotAdd]
      using rd3054raw
  have rd3057raw := evm_run rd3055 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq :
      UInt256.eq (tendLot I) (bidLotWord (tendId I) σ I) = ⟨0⟩ :=
    u256_eq_of_ne hlot
  rw [heq] at rd3057raw
  have rd3061 := evm_run rd3057raw with [
    raw push2 ⟨3137⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  have rdMload := evm_run rd3061 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmemLotSize]; decide) (by decide) hmemLotRead64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 memLot) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 memLot) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨24⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 (⟨24⟩ : UInt256) memLot)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst flipperTendLotNotMatchingWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 (⟨24⟩ : UInt256) flipperTendLotNotMatchingWord memLot)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide) mem_cost
      (solcErrorStringMem3_mload64 (⟨24⟩ : UInt256) flipperTendLotNotMatchingWord
        hmemLotSize hmemLotRead64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem flipperTendX_tabGuardPrefix {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (h : RD flipperBytecode I g s0 ⟨3137⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3158⟩
      (UInt256.gt (tendBid I) (bidTabWord (tendId I) σ I) :: tendBid I ::
        tendLot I :: tendId I :: ret :: sel :: [])
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3155 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (tendId I) ⟨1⟩ mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) hmemSize)
      (by decide) (by evm_ov),
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k3155, C3155, rd3155raw⟩ := rd3155.sload (by native_decide) (by evm_ov)
  have rd3156 : RD flipperBytecode I g s0 ⟨3156⟩
      (bidTabWord (tendId I) σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3155 C3155 := by
    have hslotAdd :
        (⟨5⟩ : UInt256) + bidBaseOfWord (tendId I) = bidSlotOfWord (tendId I) ⟨5⟩ := by
      simpa [bidSlotOfWord] using
        (u256_add_comm (⟨5⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [bidTabWord, flipperSlotWord, hslotAdd] using rd3155raw
  exact ⟨_, _, evm_run rd3156 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]⟩

theorem flipperTendX_bidLeTabOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hle : (tendBid I).toNat ≤ (bidTabWord (tendId I) σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨3137⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3239⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd3158⟩ := flipperTendX_tabGuardPrefix hmemSize h
  have hgt : UInt256.gt (tendBid I) (bidTabWord (tendId I) σ I) = ⟨0⟩ := ugt_zero hle
  rw [hgt] at rd3158
  have rd3159 := evm_run rd3158 with [raw iszero (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd3159
  exact ⟨_, _, evm_run rd3159 with [
    raw push2 ⟨3239⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]⟩

theorem flipperTendX_higherThanTab {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hgt : (bidTabWord (tendId I) σ I).toNat < (tendBid I).toNat)
    (h : RD flipperBytecode I g s0 ⟨3137⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  let memTab := twoWordHashMem (tendId I) ⟨1⟩ mem
  have hmemTabSize : memTab.size = 96 := by
    dsimp [memTab]
    exact twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmemSize
  have hmemTabRead64 :
      memTab.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memTab]
    exact twoWordHashMem_read64 (tendId I) ⟨1⟩ hmemSize hmemRead64
  obtain ⟨_, _, rd3158⟩ := flipperTendX_tabGuardPrefix hmemSize h
  have hgtWord : UInt256.gt (tendBid I) (bidTabWord (tendId I) σ I) = ⟨1⟩ := ugt_one hgt
  rw [hgtWord] at rd3158
  have rd3159 := evm_run rd3158 with [raw iszero (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd3159
  have rd3163 := evm_run rd3159 with [
    raw push2 ⟨3239⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  obtain ⟨_, _, rd3163'⟩ : ∃ k' C', RD flipperBytecode I g s0 ⟨3163⟩
      [tendBid I, tendLot I, tendId I, ret, sel] memTab
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' :=
    ⟨_, _, by simpa [memTab] using rd3163⟩
  exact RD.solcErrorStringFullWordRevertTail
    (pc := ⟨3163⟩) (len := ⟨23⟩) (word := flipperTendHigherThanTabWord) rd3163'
    (by
      unfold solcErrorStringFullWordRevertTailWf
      repeat' first | apply And.intro | native_decide)
    hmemTabSize hmemTabRead64 (by simp)

set_option maxRecDepth 2000000 in
theorem flipperTendX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨594⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flipperBytecode) (sel := sel) (entry := ⟨594⟩) (ret := ⟨323⟩)
    (decoded := ⟨616⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

end Benchmarks.Dss.Flipper
