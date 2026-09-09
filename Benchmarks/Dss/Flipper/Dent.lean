import Benchmarks.Dss.Flipper.Dispatch
import Benchmarks.Dss.Flipper.BidAccess
import Benchmarks.Dss.Flipper.ErrorStringFull

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flipper

/-! ## `dent(uint256,uint256,uint256)` -/

abbrev dentId (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev dentLot (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev dentBid (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev dentLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "id" (.int (Int.ofNat (dentId I).toNat))).insert
    "lot" (.int (Int.ofNat (dentLot I).toNat))).insert
    "bid" (.int (Int.ofNat (dentBid I).toNat))

theorem dentLocals_get_id (I : ExecutionEnv) :
    (dentLocals I).get? "id" = some (.int (Int.ofNat (dentId I).toNat)) := by
  rw [dentLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem dentLocals_get_lot (I : ExecutionEnv) :
    (dentLocals I).get? "lot" = some (.int (Int.ofNat (dentLot I).toNat)) := by
  rw [dentLocals, store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem dentLocals_get_bid (I : ExecutionEnv) :
    (dentLocals I).get? "bid" = some (.int (Int.ofNat (dentBid I).toNat)) := by
  rw [dentLocals, store_get_self]

theorem dentLocals_get_bids (I : ExecutionEnv) :
    (dentLocals I).get? "bids" = none := by
  rw [dentLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_dentGuyNeZero_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguy : bidGuyWord (dentId I) σ I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
        .ok (.bool false) := by
  have hguyEval :=
    evalExpr_bidGuy_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dentLocals I) (id := dentId I) (dentLocals_get_id I)
      (dentLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hguyEval]
  simp [evalExpr?, evalBinaryOp?, zeroAddr, hguy]
  all_goals decide

theorem evalExpr_dentGuyNeZero_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguy : bidGuyWord (dentId I) σ I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
        .ok (.bool true) := by
  have hguyEval :=
    evalExpr_bidGuy_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dentLocals I) (id := dentId I) (dentLocals_get_id I)
      (dentLocals_get_bids I)
  have hguyAddr :
      AccountAddress.ofNat (bidGuyWord (dentId I) σ I).toNat ≠ AccountAddress.ofNat 0 := by
    intro hzeroAddr
    have hmask := keyValueToWord_address_ofNat_mask (bidGuyWord (dentId I) σ I)
    rw [hzeroAddr] at hmask
    have hclean :
        UInt256.land solcAddrMask (bidGuyWord (dentId I) σ I) =
          bidGuyWord (dentId I) σ I := by
      simpa [bidGuyWord, flipperAddressReturnWord, u256_land_comm] using
        (solcAddrMask_clean
          (solcAddrMask_result_canonical
            (flipperSlotWord (bidPackedSlotOfWord (dentId I)) σ I)))
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

theorem evalExpr_dentTicGtTimestamp_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle : (bidTicWord (dentId I) σ I).toNat ≤ (UInt256.ofNat I.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
        .ok (.bool false) := by
  have hticEval :=
    evalExpr_bidTic_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dentLocals I) (id := dentId I) (dentLocals_get_id I)
      (dentLocals_get_bids I)
  have hnot : ¬ (UInt256.ofNat I.header.timestamp).toNat <
      (bidTicWord (dentId I) σ I).toNat := by
    omega
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hticEval]
  simp [evalExpr?, envValue, initState, evalBinaryOp?, hnot]
  all_goals decide

theorem evalExpr_dentTicGtTimestamp_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : (UInt256.ofNat I.header.timestamp).toNat <
      (bidTicWord (dentId I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
        .ok (.bool true) := by
  have hticEval :=
    evalExpr_bidTic_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dentLocals I) (id := dentId I) (dentLocals_get_id I)
      (dentLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hticEval]
  simp [evalExpr?, envValue, initState, evalBinaryOp?, hlt]
  all_goals decide

theorem evalExpr_dentTicEqZero_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (htic : bidTicWord (dentId I) σ I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
        .ok (.bool false) := by
  have hticEval :=
    evalExpr_bidTic_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dentLocals I) (id := dentId I) (dentLocals_get_id I)
      (dentLocals_get_bids I)
  have hneNat : ¬ (bidTicWord (dentId I) σ I).toNat = 0 := by
    intro hzero
    exact htic (uint256_toNat_eq_zero hzero)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hticEval]
  simp [evalExpr?, evalBinaryOp?, hneNat]
  all_goals decide

theorem evalExpr_dentTicEqZero_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (htic : bidTicWord (dentId I) σ I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
        .ok (.bool true) := by
  have hticEval :=
    evalExpr_bidTic_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dentLocals I) (id := dentId I) (dentLocals_get_id I)
      (dentLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hticEval]
  simp [evalExpr?, evalBinaryOp?, htic]
  all_goals decide

theorem evalExpr_dentTicActive_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (htic : bidTicWord (dentId I) σ I ≠ ⟨0⟩)
    (hle : (bidTicWord (dentId I) σ I).toNat ≤ (UInt256.ofNat I.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .or
        (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool false) := by
  have hgt := evalExpr_dentTicGtTimestamp_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hle
  have heq := evalExpr_dentTicEqZero_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) htic
  simp [evalExpr?, EvalResult.bind, bind, pure, hgt, heq]

theorem evalExpr_dentTicActive_true_left {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : (UInt256.ofNat I.header.timestamp).toNat <
      (bidTicWord (dentId I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .or
        (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
  have hgt := evalExpr_dentTicGtTimestamp_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hlt
  simp [evalExpr?, EvalResult.bind, bind, pure, hgt]

theorem evalExpr_dentTicActive_true_right {cA gh bl σ σ₀ A I} {g : Sat256}
    (htic : bidTicWord (dentId I) σ I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .or
        (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
  have hle : (bidTicWord (dentId I) σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat := by
    simp [htic]
  have hgt := evalExpr_dentTicGtTimestamp_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hle
  have heq := evalExpr_dentTicEqZero_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) htic
  simp [evalExpr?, EvalResult.bind, bind, pure, hgt, heq]

theorem evalExpr_dentEndGtTimestamp_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle : (bidEndWord (dentId I) σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool false) := by
  have hendEval :=
    evalExpr_bidEnd_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dentLocals I) (id := dentId I) (dentLocals_get_id I)
      (dentLocals_get_bids I)
  have hnot : ¬ (UInt256.ofNat I.header.timestamp).toNat <
      (bidEndWord (dentId I) σ I).toNat := by
    omega
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hendEval]
  simp [evalExpr?, envValue, initState, evalBinaryOp?, hnot]
  all_goals decide

theorem evalExpr_dentEndGtTimestamp_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : (UInt256.ofNat I.header.timestamp).toNat <
      (bidEndWord (dentId I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool true) := by
  have hendEval :=
    evalExpr_bidEnd_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dentLocals I) (id := dentId I) (dentLocals_get_id I)
      (dentLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hendEval]
  simp [evalExpr?, envValue, initState, evalBinaryOp?, hlt]
  all_goals decide

theorem evalExpr_dentBidEqBidBid_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbid : dentBid I ≠ bidBidWord (dentId I) σ I) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
        .ok (.bool false) := by
  have hbidVar :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ g A I) (.var "bid") =
          .ok (.int (Int.ofNat (dentBid I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((dentLocals I).get? "bid") =
      .ok (.int (Int.ofNat (dentBid I).toNat))
    rw [dentLocals_get_bid]
    rfl
  have hbidEval :=
    evalExpr_bidBid_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dentLocals I) (id := dentId I) (dentLocals_get_id I)
      (dentLocals_get_bids I)
  have hneNat : ¬ (dentBid I).toNat = (bidBidWord (dentId I) σ I).toNat := by
    intro hnat
    exact hbid (u256_inj hnat)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hbidVar, hbidEval]
  simp [evalBinaryOp?, hneNat]
  all_goals decide

theorem evalExpr_dentBidEqBidBid_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbid : dentBid I = bidBidWord (dentId I) σ I) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
        .ok (.bool true) := by
  have hbidVar :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ g A I) (.var "bid") =
          .ok (.int (Int.ofNat (dentBid I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((dentLocals I).get? "bid") =
      .ok (.int (Int.ofNat (dentBid I).toNat))
    rw [dentLocals_get_bid]
    rfl
  have hbidEval :=
    evalExpr_bidBid_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dentLocals I) (id := dentId I) (dentLocals_get_id I)
      (dentLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hbidVar, hbidEval]
  simp [evalBinaryOp?, hbid]
  all_goals decide

theorem evalExpr_dentBidEqBidTab_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbid : dentBid I ≠ bidTabWord (dentId I) σ I) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
        .ok (.bool false) := by
  have hbidVar :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ g A I) (.var "bid") =
          .ok (.int (Int.ofNat (dentBid I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((dentLocals I).get? "bid") =
      .ok (.int (Int.ofNat (dentBid I).toNat))
    rw [dentLocals_get_bid]
    rfl
  have htabEval :=
    evalExpr_bidTab_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dentLocals I) (id := dentId I) (dentLocals_get_id I)
      (dentLocals_get_bids I)
  have hneNat : ¬ (dentBid I).toNat = (bidTabWord (dentId I) σ I).toNat := by
    intro hnat
    exact hbid (u256_inj hnat)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hbidVar, htabEval]
  simp [evalBinaryOp?, hneNat]
  all_goals decide

theorem evalExpr_dentBidEqBidTab_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbid : dentBid I = bidTabWord (dentId I) σ I) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
        .ok (.bool true) := by
  have hbidVar :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ g A I) (.var "bid") =
          .ok (.int (Int.ofNat (dentBid I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((dentLocals I).get? "bid") =
      .ok (.int (Int.ofNat (dentBid I).toNat))
    rw [dentLocals_get_bid]
    rfl
  have htabEval :=
    evalExpr_bidTab_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dentLocals I) (id := dentId I) (dentLocals_get_id I)
      (dentLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hbidVar, htabEval]
  simp [evalBinaryOp?, hbid]
  all_goals decide

theorem flipperDentSourceBodyGuyNotSet {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (dentId I) σ I = ⟨0⟩) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
  intro locals evm0
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_dentGuyNeZero_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hguy
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguyGuard)
  simpa [ExecTransitionBody, dentTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem flipperDentSourceBodyAlreadyFinishedTic {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (dentId I) σ I ≠ ⟨0⟩)
    (htic : bidTicWord (dentId I) σ I ≠ ⟨0⟩)
    (hle : (bidTicWord (dentId I) σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
  intro locals evm0
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_dentGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hguy
  have hticGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_dentTicActive_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        htic hle
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hticGuard)
  simpa [ExecTransitionBody, dentTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem flipperDentSourceBodyAlreadyFinishedEnd {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (dentId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendLe : (bidEndWord (dentId I) σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
  intro locals evm0
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_dentGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
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
      evalExpr_dentEndGtTimestamp_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hendLe
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hticGuardLocal) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hendGuard)
  simpa [ExecTransitionBody, dentTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem flipperDentSourceBodyNotMatchingBid {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (dentId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hbid : dentBid I ≠ bidBidWord (dentId I) σ I) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
  intro locals evm0
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_dentGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
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
  have hbidGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_dentBidEqBidBid_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hbid
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hticGuardLocal) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hendGuardLocal) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hbidGuard)
  simpa [ExecTransitionBody, dentTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem flipperDentSourceBodyTendNotFinished {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (dentId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (htab : dentBid I ≠ bidTabWord (dentId I) σ I) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
  intro locals evm0
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_dentGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
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
  have hbidGuardLocal :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true) := by
    simpa [locals, evm0] using hbidGuard
  have htabGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_dentBidEqBidTab_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) htab
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hticGuardLocal) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hendGuardLocal) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hbidGuardLocal) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse htabGuard)
  simpa [ExecTransitionBody, dentTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

noncomputable abbrev dentHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (dentId I) ⟨1⟩ solcFreePtrMem

noncomputable abbrev dentHashMem1 (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (dentId I) ⟨1⟩ (dentHashMem I)

noncomputable abbrev dentHashMem2 (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (dentId I) ⟨1⟩ (dentHashMem1 I)

theorem dentHashMem_size (I : ExecutionEnv) :
    (dentHashMem I).size = 96 := by
  unfold dentHashMem
  exact twoWordHashMem_size_96 (dentId I) ⟨1⟩ solcFreePtrMem_size

theorem dentHashMem_read64 (I : ExecutionEnv) :
    (dentHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dentHashMem
  exact twoWordHashMem_read64 (dentId I) ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64

theorem dentHashMem1_size (I : ExecutionEnv) :
    (dentHashMem1 I).size = 96 := by
  unfold dentHashMem1
  exact twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem_size I)

theorem dentHashMem1_read64 (I : ExecutionEnv) :
    (dentHashMem1 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dentHashMem1
  exact twoWordHashMem_read64 (dentId I) ⟨1⟩ (dentHashMem_size I) (dentHashMem_read64 I)

theorem dentHashMem2_size (I : ExecutionEnv) :
    (dentHashMem2 I).size = 96 := by
  unfold dentHashMem2
  exact twoWordHashMem_size_96 (dentId I) ⟨1⟩ (dentHashMem1_size I)

theorem dentHashMem2_read64 (I : ExecutionEnv) :
    (dentHashMem2 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dentHashMem2
  exact twoWordHashMem_read64 (dentId I) ⟨1⟩ (dentHashMem1_size I)
    (dentHashMem1_read64 I)

abbrev flipperDentAlreadyFinishedTicWord : UInt256 :=
  ⟨31853446598541861569097437671217369822383545270177637832041123590441915121664⟩

abbrev flipperDentAlreadyFinishedEndWord : UInt256 :=
  ⟨31853446598541861569097437671217369822383545270177637832041119373819117568000⟩

abbrev flipperDentNotMatchingBidWord : UInt256 :=
  ⟨31853446598541861569416484753144574251805521435935035778473353583784122908672⟩

abbrev flipperDentTendNotFinishedWord : UInt256 :=
  ⟨31853446598541861569562644350505647585104012541916151791950971413388968591360⟩

theorem flipperDentDecodePushMask4061 :
    decode flipperBytecode (⟨4061⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  decide +native

theorem flipperDentDecodePushMask4101 :
    decode flipperBytecode (⟨4101⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  decide +native

theorem flipperDentDecodePushMask4219 :
    decode flipperBytecode (⟨4219⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  decide +native

theorem flipperDecode_dent_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
      (transitionSignature dentTransition).paramTypes I.calldata =
        some (dentLocals I) := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "lot", "bid"]
      [abiUInt256, abiUInt256, abiUInt256] I.calldata = some (dentLocals I)
  exact flipperDecodeCalldataLegacyUInt256UInt256UInt256_ok (cd := I.calldata)
    (x := "id") (y := "lot") (z := "bid") hsz100

theorem flipperDecode_dent_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
      (transitionSignature dentTransition).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "lot", "bid"]
      [abiUInt256, abiUInt256, abiUInt256] I.calldata = none
  exact flipperDecodeCalldataLegacyUInt256UInt256UInt256_none_short (cd := I.calldata)
    (x := "id") (y := "lot") (z := "bid") hsz4 hshort

theorem flipperReachDentBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flipperSelBytes 4)) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨670⟩ [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flipperSelWord I = ⟨0x5ff3a382⟩ :=
    flipperSelWord_eq_of_beq I hsz 0x5f 0xf3 0xa3 0x82 ⟨0x5ff3a382⟩
      (by decide +native) (by simpa [flipperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hhigh : UInt256.gt (armSelNat flipperBytecode flipperHighSplitPc)
      (flipperSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighHighFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighHighFirstArmPc 3))
        (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact flipperReachHighHighBody 3 (by omega) ⟨670⟩ hcode hwv hsz hsize hroot hhigh
    heq0 htake (by jump_dest) (by decide +native)

theorem RD.flipperDentDecodeToRoutine {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨692⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = flipperBytecode)
    (hroutine : (D_J code 0).contains ⟨3935⟩ = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨3935⟩
      (calldataWord ee.calldata 68 :: calldataWord ee.calldata 36 ::
        calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd3935 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw calldataload (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw calldataload (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw calldataload (by decide +native) (by evm_ov),
    raw push2 ⟨3935⟩ (by decide +native) (by evm_ov),
    raw jump (by decide +native) hroutine (by evm_ov)]
  exact ⟨_, _, by
    simpa [calldataWord, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using rd3935⟩

theorem flipperDentX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨670⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3935⟩
        [dentBid I, dentLot I, dentId I, ⟨323⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flipperBytecode) (sel := sel) (entry := ⟨670⟩) (ret := ⟨323⟩)
    (decoded := ⟨692⟩) (need := ⟨96⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.flipperDentDecodeToRoutine
    (code := flipperBytecode) (ret := ⟨323⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [dentBid, dentLot, dentId] using hroutine⟩

theorem flipperDentX_guyNotSet {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hguy : bidGuyWord (dentId I) σ I = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨3935⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd3952 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) solcFreePtrMem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (dentHashMem I) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (by simpa [dentHashMem, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) solcFreePtrMem_size)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k3953, C3953, rd3953raw⟩ := rd3952.sload (by decide +native) (by evm_ov)
  have rd3954 : RD flipperBytecode I g s0 ⟨3954⟩
      (bidPackedWord (dentId I) σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (dentHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3953 C3953 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (dentId I) = bidPackedSlotOfWord (dentId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd3953raw
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have hguyClean :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (bidPackedWord (dentId I) σ I) = ⟨0⟩ := by
    rw [hmask160, u256_land_comm]
    simpa [bidGuyWord, bidPackedWord, flipperAddressReturnWord] using hguy
  have rd3967 := evm_run rd3954 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push2 ⟨4033⟩ (by decide +native) (by evm_ov),
    raw jumpiNT (by decide +native) hguyClean (by evm_ov)]
  have hwf :
      solcErrorStringRevertTailWf flipperBytecode ⟨3967⟩ ⟨19⟩
        ⟨0x119b1a5c1c195c8bd9dd5e4b5b9bdd0b5cd95d⟩ ⟨106⟩ .PUSH19 19 := by
    unfold solcErrorStringRevertTailWf
    repeat' first | apply And.intro | decide +native
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3967⟩) (len := ⟨19⟩)
    (rawWord := ⟨0x119b1a5c1c195c8bd9dd5e4b5b9bdd0b5cd95d⟩)
    (shift := ⟨106⟩)
    (word := UInt256.shiftLeft
      (⟨0x119b1a5c1c195c8bd9dd5e4b5b9bdd0b5cd95d⟩ : UInt256) ⟨106⟩)
    (op := .PUSH19) (width := 19) rd3967
    hwf (by decide) rfl (dentHashMem_size I) (dentHashMem_read64 I) (by simp)

theorem flipperDentX_guyOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hguy : bidGuyWord (dentId I) σ I ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨3935⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4033⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      (dentHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3952 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) solcFreePtrMem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (dentHashMem I) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (by simpa [dentHashMem, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) solcFreePtrMem_size)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k3953, C3953, rd3953raw⟩ := rd3952.sload (by decide +native) (by evm_ov)
  have rd3954 : RD flipperBytecode I g s0 ⟨3954⟩
      (bidPackedWord (dentId I) σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (dentHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3953 C3953 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (dentId I) = bidPackedSlotOfWord (dentId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd3953raw
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have hguyClean :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (bidPackedWord (dentId I) σ I) ≠ ⟨0⟩ := by
    intro hzero
    exact hguy (by
      rw [hmask160, u256_land_comm] at hzero
      simpa [bidGuyWord, bidPackedWord, flipperAddressReturnWord] using hzero)
  have rd4033 := evm_run rd3954 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push2 ⟨4033⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) hguyClean (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd4033⟩

theorem flipperDentX_alreadyFinishedTic {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hticNe : bidTicWord (dentId I) σ I ≠ ⟨0⟩)
    (hticLe : (bidTicWord (dentId I) σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat)
    (h : RD flipperBytecode I g s0 ⟨4033⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      (dentHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd4051 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) (dentHashMem I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (dentHashMem1 I) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (by simpa [dentHashMem1, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) (dentHashMem_size I))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k4051, C4051, rd4051raw⟩ := rd4051.sload (by decide +native) (by evm_ov)
  have rd4052 : RD flipperBytecode I g s0 ⟨4052⟩
      (bidPackedWord (dentId I) σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (dentHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4051 C4051 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (dentId I) = bidPackedSlotOfWord (dentId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd4051raw
  have rd4070 := evm_run rd4052 with [
    raw timestamp (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperDentDecodePushMask4061 (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw gt (by decide +native) (by evm_ov)]
  have hticGt0 :
      UInt256.gt
        (UInt256.land uint48Mask
          (UInt256.div (bidPackedWord (dentId I) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)))
        (UInt256.ofNat I.header.timestamp) = ⟨0⟩ := by
    simpa [bidTicWord, bidPackedWord, flipperUint48Offset20Word, uint48Divisor20,
      u256_land_comm] using (ugt_zero hticLe)
  rw [hticGt0] at rd4070
  have rd4076 := evm_run rd4070 with [
    raw dup1 (by decide +native) (by evm_ov),
    raw push2 ⟨4110⟩ (by decide +native) (by evm_ov),
    raw jumpiNT (by decide +native) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  have rd4093 := evm_run rd4076 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) (dentHashMem1 I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (dentHashMem2 I) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (by simpa [dentHashMem2, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) (dentHashMem1_size I))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k4093, C4093, rd4093raw⟩ := rd4093.sload (by decide +native) (by evm_ov)
  have rd4094 : RD flipperBytecode I g s0 ⟨4094⟩
      (bidPackedWord (dentId I) σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (dentHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4093 C4093 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (dentId I) = bidPackedSlotOfWord (dentId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd4093raw
  have rd4110raw := evm_run rd4094 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperDentDecodePushMask4101 (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov)]
  have hticRaw :
      UInt256.land uint48Mask
        (UInt256.div (bidPackedWord (dentId I) σ I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)) =
        bidTicWord (dentId I) σ I := by
    simp [bidTicWord, bidPackedWord, flipperUint48Offset20Word, uint48Divisor20,
      u256_land_comm]
  rw [hticRaw] at rd4110raw
  rw [Reasoning.Theory.isZero_eq_zero_of_ne hticNe] at rd4110raw
  have rd4111 := rd4110raw.jumpdest (by decide +native) (by evm_ov)
  have rd4115 := evm_run rd4111 with [
    raw push2 ⟨4191⟩ (by decide +native) (by evm_ov),
    raw jumpiNT (by decide +native) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  have rdMload := evm_run rd4115 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost
      (mloadFreePtrValue (by rw [dentHashMem2_size I]; decide) (by decide)
        (dentHashMem2_read64 I))
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by decide +native) (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 (dentHashMem2 I)) (UInt256.ofNat 5)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 (dentHashMem2 I)) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨28⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 (⟨28⟩ : UInt256) (dentHashMem2 I))
      (UInt256.ofNat 7) (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst flipperDentAlreadyFinishedTicWord
    (width := 32) (op := .PUSH32) (by decide) (by decide +native) (by evm_ov)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 (⟨28⟩ : UInt256) flipperDentAlreadyFinishedTicWord
        (dentHashMem2 I))
      (UInt256.ofNat 8) (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native) mem_cost
      (solcErrorStringMem3_mload64 (⟨28⟩ : UInt256) flipperDentAlreadyFinishedTicWord
        (dentHashMem2_size I) (dentHashMem2_read64 I))
      (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨100⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw rev 0 (by decide +native) mem_cost (by evm_ov)]

theorem flipperDentX_ticGtOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hticGt : (UInt256.ofNat I.header.timestamp).toNat <
      (bidTicWord (dentId I) σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨4033⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      (dentHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4191⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      (dentHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4051 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) (dentHashMem I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (dentHashMem1 I) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (by simpa [dentHashMem1, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) (dentHashMem_size I))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k4051, C4051, rd4051raw⟩ := rd4051.sload (by decide +native) (by evm_ov)
  have rd4052 : RD flipperBytecode I g s0 ⟨4052⟩
      (bidPackedWord (dentId I) σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (dentHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4051 C4051 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (dentId I) = bidPackedSlotOfWord (dentId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd4051raw
  have rd4070 := evm_run rd4052 with [
    raw timestamp (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperDentDecodePushMask4061 (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw gt (by decide +native) (by evm_ov)]
  have hticGt1 :
      UInt256.gt
        (UInt256.land uint48Mask
          (UInt256.div (bidPackedWord (dentId I) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)))
        (UInt256.ofNat I.header.timestamp) = ⟨1⟩ := by
    simpa [bidTicWord, bidPackedWord, flipperUint48Offset20Word, uint48Divisor20,
      u256_land_comm] using (ugt_one hticGt)
  rw [hticGt1] at rd4070
  have rd4110 := evm_run rd4070 with [
    raw dup1 (by decide +native) (by evm_ov),
    raw push2 ⟨4110⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  have rd4111 := rd4110.jumpdest (by decide +native) (by evm_ov)
  have rd4191 := evm_run rd4111 with [
    raw push2 ⟨4191⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd4191⟩

theorem flipperDentX_ticZeroOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (htic : bidTicWord (dentId I) σ I = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨4033⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      (dentHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4191⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      (dentHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4051 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) (dentHashMem I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (dentHashMem1 I) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (by simpa [dentHashMem1, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) (dentHashMem_size I))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k4051, C4051, rd4051raw⟩ := rd4051.sload (by decide +native) (by evm_ov)
  have rd4052 : RD flipperBytecode I g s0 ⟨4052⟩
      (bidPackedWord (dentId I) σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (dentHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4051 C4051 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (dentId I) = bidPackedSlotOfWord (dentId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd4051raw
  have rd4070 := evm_run rd4052 with [
    raw timestamp (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperDentDecodePushMask4061 (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw gt (by decide +native) (by evm_ov)]
  have hticGt0 :
      UInt256.gt
        (UInt256.land uint48Mask
          (UInt256.div (bidPackedWord (dentId I) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)))
        (UInt256.ofNat I.header.timestamp) = ⟨0⟩ := by
    have hle : (bidTicWord (dentId I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat := by
      simp [htic]
    simpa [bidTicWord, bidPackedWord, flipperUint48Offset20Word, uint48Divisor20,
      u256_land_comm] using (ugt_zero hle)
  rw [hticGt0] at rd4070
  have rd4076 := evm_run rd4070 with [
    raw dup1 (by decide +native) (by evm_ov),
    raw push2 ⟨4110⟩ (by decide +native) (by evm_ov),
    raw jumpiNT (by decide +native) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  have rd4093 := evm_run rd4076 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) (dentHashMem1 I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (dentHashMem2 I) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (by simpa [dentHashMem2, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) (dentHashMem1_size I))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k4093, C4093, rd4093raw⟩ := rd4093.sload (by decide +native) (by evm_ov)
  have rd4094 : RD flipperBytecode I g s0 ⟨4094⟩
      (bidPackedWord (dentId I) σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (dentHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4093 C4093 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (dentId I) = bidPackedSlotOfWord (dentId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd4093raw
  have rd4110raw := evm_run rd4094 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperDentDecodePushMask4101 (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov)]
  have hticRaw :
      UInt256.land uint48Mask
        (UInt256.div (bidPackedWord (dentId I) σ I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)) =
        bidTicWord (dentId I) σ I := by
    simp [bidTicWord, bidPackedWord, flipperUint48Offset20Word, uint48Divisor20,
      u256_land_comm]
  rw [hticRaw, htic] at rd4110raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4110raw
  have rd4111 := rd4110raw.jumpdest (by decide +native) (by evm_ov)
  have rd4191 := evm_run rd4111 with [
    raw push2 ⟨4191⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd4191⟩

theorem flipperDentX_endOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hendGt : (UInt256.ofNat I.header.timestamp).toNat <
      (bidEndWord (dentId I) σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨4191⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4308⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4209 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) mem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (twoWordHashMem (dentId I) ⟨1⟩ mem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (by simpa [bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) hmemSize)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k4209, C4209, rd4209raw⟩ := rd4209.sload (by decide +native) (by evm_ov)
  have rd4210 : RD flipperBytecode I g s0 ⟨4210⟩
      (bidPackedWord (dentId I) σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4209 C4209 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (dentId I) = bidPackedSlotOfWord (dentId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd]
      using rd4209raw
  have rd4228 := evm_run rd4210 with [
    raw timestamp (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨208⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperDentDecodePushMask4219 (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw gt (by decide +native) (by evm_ov)]
  have hendGt1 :
      UInt256.gt
        (UInt256.land uint48Mask
          (UInt256.div (bidPackedWord (dentId I) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)))
        (UInt256.ofNat I.header.timestamp) = ⟨1⟩ := by
    simpa [bidEndWord, bidPackedWord, flipperUint48Offset26Word, uint48Divisor26,
      u256_land_comm] using (ugt_one hendGt)
  rw [hendGt1] at rd4228
  have rd4308 := evm_run rd4228 with [
    raw push2 ⟨4308⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd4308⟩

theorem flipperDentX_alreadyFinishedEnd {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hendLe : (bidEndWord (dentId I) σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat)
    (h : RD flipperBytecode I g s0 ⟨4191⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  let memEnd := twoWordHashMem (dentId I) ⟨1⟩ mem
  have hmemEndSize : memEnd.size = 96 := by
    dsimp [memEnd]
    exact twoWordHashMem_size_96 (dentId I) ⟨1⟩ hmemSize
  have hmemEndRead64 :
      memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memEnd]
    exact twoWordHashMem_read64 (dentId I) ⟨1⟩ hmemSize hmemRead64
  have rd4209 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) mem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 memEnd (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (by
        dsimp [memEnd]
        simpa [bidBaseOfWord] using
          twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) hmemSize)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k4209, C4209, rd4209raw⟩ := rd4209.sload (by decide +native) (by evm_ov)
  have rd4210 : RD flipperBytecode I g s0 ⟨4210⟩
      (bidPackedWord (dentId I) σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4209 C4209 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (dentId I) = bidPackedSlotOfWord (dentId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [memEnd, bidPackedWord, flipperSlotWord, hslotAdd]
      using rd4209raw
  have rd4228 := evm_run rd4210 with [
    raw timestamp (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨208⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperDentDecodePushMask4219 (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw gt (by decide +native) (by evm_ov)]
  have hendGt0 :
      UInt256.gt
        (UInt256.land uint48Mask
          (UInt256.div (bidPackedWord (dentId I) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)))
        (UInt256.ofNat I.header.timestamp) = ⟨0⟩ := by
    simpa [bidEndWord, bidPackedWord, flipperUint48Offset26Word, uint48Divisor26,
      u256_land_comm] using (ugt_zero hendLe)
  rw [hendGt0] at rd4228
  have rd4232 := evm_run rd4228 with [
    raw push2 ⟨4308⟩ (by decide +native) (by evm_ov),
    raw jumpiNT (by decide +native) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  have rdMload := evm_run rd4232 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost
      (mloadFreePtrValue (by rw [hmemEndSize]; decide) (by decide) hmemEndRead64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by decide +native) (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 memEnd) (UInt256.ofNat 5)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 memEnd) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨28⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 (⟨28⟩ : UInt256) memEnd)
      (UInt256.ofNat 7) (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst flipperDentAlreadyFinishedEndWord
    (width := 32) (op := .PUSH32) (by decide) (by decide +native) (by evm_ov)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 (⟨28⟩ : UInt256) flipperDentAlreadyFinishedEndWord memEnd)
      (UInt256.ofNat 8) (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native) mem_cost
      (solcErrorStringMem3_mload64 (⟨28⟩ : UInt256) flipperDentAlreadyFinishedEndWord
        hmemEndSize hmemEndRead64)
      (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨100⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw rev 0 (by decide +native) mem_cost (by evm_ov)]

theorem flipperDentX_bidOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hbid : dentBid I = bidBidWord (dentId I) σ I)
    (h : RD flipperBytecode I g s0 ⟨4308⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4406⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4324 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) mem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (twoWordHashMem (dentId I) ⟨1⟩ mem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (by simpa [bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) hmemSize)
      (by decide) (by evm_ov)]
  obtain ⟨k4324, C4324, rd4324raw⟩ := rd4324.sload (by decide +native) (by evm_ov)
  have rd4324' : RD flipperBytecode I g s0 ⟨4324⟩
      (bidBidWord (dentId I) σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4324 C4324 := by
    simpa [bidBidWord, flipperSlotWord]
      using rd4324raw
  have rd4326raw := evm_run rd4324' with [
    raw dup2 (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  have heq :
      UInt256.eq (dentBid I) (bidBidWord (dentId I) σ I) = ⟨1⟩ := by
    rw [hbid]
    exact u256_eq_refl _
  rw [heq] at rd4326raw
  have rd4406 := evm_run rd4326raw with [
    raw push2 ⟨4406⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd4406⟩

theorem flipperDentX_notMatchingBid {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hbid : dentBid I ≠ bidBidWord (dentId I) σ I)
    (h : RD flipperBytecode I g s0 ⟨4308⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  let memBid := twoWordHashMem (dentId I) ⟨1⟩ mem
  have hmemBidSize : memBid.size = 96 := by
    dsimp [memBid]
    exact twoWordHashMem_size_96 (dentId I) ⟨1⟩ hmemSize
  have hmemBidRead64 :
      memBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memBid]
    exact twoWordHashMem_read64 (dentId I) ⟨1⟩ hmemSize hmemRead64
  have rd4324 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) mem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 memBid (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (by
        dsimp [memBid]
        simpa [bidBaseOfWord] using
          twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) hmemSize)
      (by decide) (by evm_ov)]
  obtain ⟨k4324, C4324, rd4324raw⟩ := rd4324.sload (by decide +native) (by evm_ov)
  have rd4324' : RD flipperBytecode I g s0 ⟨4324⟩
      (bidBidWord (dentId I) σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      memBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4324 C4324 := by
    simpa [memBid, bidBidWord, flipperSlotWord]
      using rd4324raw
  have rd4326raw := evm_run rd4324' with [
    raw dup2 (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  have heq :
      UInt256.eq (dentBid I) (bidBidWord (dentId I) σ I) = ⟨0⟩ :=
    u256_eq_of_ne hbid
  rw [heq] at rd4326raw
  have rd4330 := evm_run rd4326raw with [
    raw push2 ⟨4406⟩ (by decide +native) (by evm_ov),
    raw jumpiNT (by decide +native) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  have rdMload := evm_run rd4330 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost
      (mloadFreePtrValue (by rw [hmemBidSize]; decide) (by decide) hmemBidRead64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by decide +native) (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 memBid) (UInt256.ofNat 5)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 memBid) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨24⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 (⟨24⟩ : UInt256) memBid)
      (UInt256.ofNat 7) (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst flipperDentNotMatchingBidWord
    (width := 32) (op := .PUSH32) (by decide) (by decide +native) (by evm_ov)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 (⟨24⟩ : UInt256) flipperDentNotMatchingBidWord memBid)
      (UInt256.ofNat 8) (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native) mem_cost
      (solcErrorStringMem3_mload64 (⟨24⟩ : UInt256) flipperDentNotMatchingBidWord
        hmemBidSize hmemBidRead64)
      (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨100⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw rev 0 (by decide +native) mem_cost (by evm_ov)]

theorem flipperDentX_tabGuardPrefix {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (h : RD flipperBytecode I g s0 ⟨4406⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4427⟩
      (UInt256.eq (dentBid I) (bidTabWord (dentId I) σ I) :: dentBid I ::
        dentLot I :: dentId I :: ret :: sel :: [])
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4424 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) mem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (twoWordHashMem (dentId I) ⟨1⟩ mem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (by simpa [bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) hmemSize)
      (by decide) (by evm_ov),
    raw push1 ⟨5⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k4424, C4424, rd4424raw⟩ := rd4424.sload (by decide +native) (by evm_ov)
  have rd4425 : RD flipperBytecode I g s0 ⟨4425⟩
      (bidTabWord (dentId I) σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4424 C4424 := by
    have hslotAdd :
        (⟨5⟩ : UInt256) + bidBaseOfWord (dentId I) = bidSlotOfWord (dentId I) ⟨5⟩ := by
      simpa [bidSlotOfWord] using
        (u256_add_comm (⟨5⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [bidTabWord, flipperSlotWord, hslotAdd] using rd4424raw
  exact ⟨_, _, evm_run rd4425 with [
    raw dup2 (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]⟩

theorem flipperDentX_bidEqTabOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (htab : dentBid I = bidTabWord (dentId I) σ I)
    (h : RD flipperBytecode I g s0 ⟨4406⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4507⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd4427⟩ := flipperDentX_tabGuardPrefix hmemSize h
  have heq : UInt256.eq (dentBid I) (bidTabWord (dentId I) σ I) = ⟨1⟩ := by
    rw [htab]
    exact u256_eq_refl _
  rw [heq] at rd4427
  exact ⟨_, _, evm_run rd4427 with [
    raw push2 ⟨4507⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) one_ne_zero_uint (by jump_dest) (by evm_ov)]⟩

theorem flipperDentX_tendNotFinished {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (htab : dentBid I ≠ bidTabWord (dentId I) σ I)
    (h : RD flipperBytecode I g s0 ⟨4406⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  let memTab := twoWordHashMem (dentId I) ⟨1⟩ mem
  have hmemTabSize : memTab.size = 96 := by
    dsimp [memTab]
    exact twoWordHashMem_size_96 (dentId I) ⟨1⟩ hmemSize
  have hmemTabRead64 :
      memTab.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memTab]
    exact twoWordHashMem_read64 (dentId I) ⟨1⟩ hmemSize hmemRead64
  obtain ⟨_, _, rd4427⟩ := flipperDentX_tabGuardPrefix hmemSize h
  have heq : UInt256.eq (dentBid I) (bidTabWord (dentId I) σ I) = ⟨0⟩ :=
    u256_eq_of_ne htab
  rw [heq] at rd4427
  have rd4431 := evm_run rd4427 with [
    raw push2 ⟨4507⟩ (by decide +native) (by evm_ov),
    raw jumpiNT (by decide +native) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  obtain ⟨_, _, rd4431'⟩ : ∃ k' C', RD flipperBytecode I g s0 ⟨4431⟩
      [dentBid I, dentLot I, dentId I, ret, sel] memTab
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' :=
    ⟨_, _, by simpa [memTab] using rd4431⟩
  exact RD.solcErrorStringFullWordRevertTail
    (pc := ⟨4431⟩) (len := ⟨25⟩) (word := flipperDentTendNotFinishedWord) rd4431'
    (by
      unfold solcErrorStringFullWordRevertTailWf
      repeat' first | apply And.intro | decide +native)
    hmemTabSize hmemTabRead64 (by simp)

set_option maxRecDepth 2000000 in
theorem flipperDentX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨670⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flipperBytecode) (sel := sel) (entry := ⟨670⟩) (ret := ⟨323⟩)
    (decoded := ⟨692⟩) (need := ⟨96⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt

end Benchmarks.Dss.Flipper
