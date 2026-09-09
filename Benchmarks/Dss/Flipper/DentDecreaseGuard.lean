import Benchmarks.Dss.Flipper.DentLotGuard
import Benchmarks.Dss.Flipper.CheckedMul

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flipper

/-! ## `dent` checked decrease guard -/

abbrev flipperDentInsufficientDecreaseWord : UInt256 :=
  ⟨31853446598541861569293789059947845366293458314517486776447481245590548905984⟩

abbrev dentBegWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperSlotWord ⟨4⟩ σ I

abbrev dentLotOneWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.mul (bidLotWord (dentId I) σ I) flipperONEWord

abbrev dentBegLotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.mul (dentBegWord σ I) (dentLot I)

abbrev dentLocalsBegLot (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (dentLocals I).insert "begLot" (.int (Int.ofNat (dentBegLotWord σ I).toNat))

abbrev dentLocalsBegLotLotOne (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (dentLocalsBegLot σ I).insert "lotOne" (.int (Int.ofNat (dentLotOneWord σ I).toNat))

abbrev dentLocalsLotOne (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (dentLocals I).insert "lotOne" (.int (Int.ofNat (dentLotOneWord σ I).toNat))

abbrev dentLocalsLotOneBegLot (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (dentLocalsLotOne σ I).insert "begLot" (.int (Int.ofNat (dentBegLotWord σ I).toNat))

theorem dentLocals_get_beg (I : ExecutionEnv) :
    (dentLocals I).get? "beg" = none := by
  rw [dentLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem dentLocalsBegLot_get_begLot (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsBegLot σ I).get? "begLot" =
      some (.int (Int.ofNat (dentBegLotWord σ I).toNat)) := by
  rw [dentLocalsBegLot, store_get_self]

theorem dentLocalsBegLot_get_lot (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsBegLot σ I).get? "lot" =
      some (.int (Int.ofNat (dentLot I).toNat)) := by
  rw [dentLocalsBegLot, store_get_ne _ _ (by decide), dentLocals_get_lot]

theorem dentLocalsBegLot_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsBegLot σ I).get? "id" =
      some (.int (Int.ofNat (dentId I).toNat)) := by
  rw [dentLocalsBegLot, store_get_ne _ _ (by decide), dentLocals_get_id]

theorem dentLocalsBegLot_get_bids (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsBegLot σ I).get? "bids" = none := by
  rw [dentLocalsBegLot, store_get_ne _ _ (by decide), dentLocals_get_bids]

theorem dentLocalsBegLot_get_beg (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsBegLot σ I).get? "beg" = none := by
  rw [dentLocalsBegLot, store_get_ne _ _ (by decide), dentLocals_get_beg]

theorem dentLocalsBegLotLotOne_get_lotOne (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsBegLotLotOne σ I).get? "lotOne" =
      some (.int (Int.ofNat (dentLotOneWord σ I).toNat)) := by
  rw [dentLocalsBegLotLotOne, store_get_self]

theorem dentLocalsBegLotLotOne_get_begLot (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsBegLotLotOne σ I).get? "begLot" =
      some (.int (Int.ofNat (dentBegLotWord σ I).toNat)) := by
  rw [dentLocalsBegLotLotOne, store_get_ne _ _ (by decide), dentLocalsBegLot_get_begLot]

theorem dentLocalsBegLotLotOne_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsBegLotLotOne σ I).get? "id" =
      some (.int (Int.ofNat (dentId I).toNat)) := by
  rw [dentLocalsBegLotLotOne, store_get_ne _ _ (by decide), dentLocalsBegLot_get_id]

theorem dentLocalsBegLotLotOne_get_bids (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsBegLotLotOne σ I).get? "bids" = none := by
  rw [dentLocalsBegLotLotOne, store_get_ne _ _ (by decide), dentLocalsBegLot_get_bids]

theorem dentLocalsLotOne_get_lotOne (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOne σ I).get? "lotOne" =
      some (.int (Int.ofNat (dentLotOneWord σ I).toNat)) := by
  rw [dentLocalsLotOne, store_get_self]

theorem dentLocalsLotOne_get_lot (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOne σ I).get? "lot" =
      some (.int (Int.ofNat (dentLot I).toNat)) := by
  rw [dentLocalsLotOne, store_get_ne _ _ (by decide), dentLocals_get_lot]

theorem dentLocalsLotOne_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOne σ I).get? "id" =
      some (.int (Int.ofNat (dentId I).toNat)) := by
  rw [dentLocalsLotOne, store_get_ne _ _ (by decide), dentLocals_get_id]

theorem dentLocalsLotOne_get_bids (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOne σ I).get? "bids" = none := by
  rw [dentLocalsLotOne, store_get_ne _ _ (by decide), dentLocals_get_bids]

theorem dentLocalsLotOne_get_beg (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOne σ I).get? "beg" = none := by
  rw [dentLocalsLotOne, store_get_ne _ _ (by decide), dentLocals_get_beg]

theorem dentLocalsLotOneBegLot_get_begLot (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOneBegLot σ I).get? "begLot" =
      some (.int (Int.ofNat (dentBegLotWord σ I).toNat)) := by
  rw [dentLocalsLotOneBegLot, store_get_self]

theorem dentLocalsLotOneBegLot_get_lotOne (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOneBegLot σ I).get? "lotOne" =
      some (.int (Int.ofNat (dentLotOneWord σ I).toNat)) := by
  rw [dentLocalsLotOneBegLot, store_get_ne _ _ (by decide), dentLocalsLotOne_get_lotOne]

theorem dentLocalsLotOneBegLot_get_lot (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOneBegLot σ I).get? "lot" =
      some (.int (Int.ofNat (dentLot I).toNat)) := by
  rw [dentLocalsLotOneBegLot, store_get_ne _ _ (by decide), dentLocalsLotOne_get_lot]

theorem dentLocalsLotOneBegLot_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOneBegLot σ I).get? "id" =
      some (.int (Int.ofNat (dentId I).toNat)) := by
  rw [dentLocalsLotOneBegLot, store_get_ne _ _ (by decide), dentLocalsLotOne_get_id]

theorem dentLocalsLotOneBegLot_get_bids (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOneBegLot σ I).get? "bids" = none := by
  rw [dentLocalsLotOneBegLot, store_get_ne _ _ (by decide), dentLocalsLotOne_get_bids]

theorem dentLocalsLotOneBegLot_get_beg (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOneBegLot σ I).get? "beg" = none := by
  rw [dentLocalsLotOneBegLot, store_get_ne _ _ (by decide), dentLocalsLotOne_get_beg]

theorem evalExpr_dentBegLotMul_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hfit : (dentBegWord σ I).toNat * (dentLot I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I) (mul256 (.storage begRef) (.var "lot")) =
        .ok (.int (Int.ofNat (dentBegLotWord σ I).toNat)) := by
  have hbeg := evalExpr_flipperBeg_of_get (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := dentLocals I) (dentLocals_get_beg I)
  have hlot :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := dentLocals I) (name := "lot") (value := dentLot I)
      (dentLocals_get_lot I)
  exact evalExpr_mul256_ok hbeg hlot rfl hfit

theorem evalExpr_dentBegLotMul_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hover : UInt256.size ≤ (dentBegWord σ I).toNat * (dentLot I).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I) (mul256 (.storage begRef) (.var "lot")) =
        .revert := by
  have hbeg := evalExpr_flipperBeg_of_get (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := dentLocals I) (dentLocals_get_beg I)
  have hlot :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := dentLocals I) (name := "lot") (value := dentLot I)
      (dentLocals_get_lot I)
  exact evalExpr_mul256_revert hbeg hlot hover

theorem evalExpr_dentBegLotMul_afterLotOne_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hfit : (dentBegWord σ I).toNat * (dentLot I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := dentLocalsLotOne σ I }
      (initState cA gh bl σ σ₀ g A I) (mul256 (.storage begRef) (.var "lot")) =
        .ok (.int (Int.ofNat (dentBegLotWord σ I).toNat)) := by
  have hbeg := evalExpr_flipperBeg_of_get (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := dentLocalsLotOne σ I) (dentLocalsLotOne_get_beg σ I)
  have hlot :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := dentLocalsLotOne σ I) (name := "lot") (value := dentLot I)
      (dentLocalsLotOne_get_lot σ I)
  exact evalExpr_mul256_ok hbeg hlot rfl hfit

theorem evalExpr_dentBegLotMul_afterLotOne_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hover : UInt256.size ≤ (dentBegWord σ I).toNat * (dentLot I).toNat) :
    evalExpr? config { contract := contract, locals := dentLocalsLotOne σ I }
      (initState cA gh bl σ σ₀ g A I) (mul256 (.storage begRef) (.var "lot")) =
        .revert := by
  have hbeg := evalExpr_flipperBeg_of_get (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := dentLocalsLotOne σ I) (dentLocalsLotOne_get_beg σ I)
  have hlot :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := dentLocalsLotOne σ I) (name := "lot") (value := dentLot I)
      (dentLocalsLotOne_get_lot σ I)
  exact evalExpr_mul256_revert hbeg hlot hover

theorem evalExpr_dentBegLotRequire_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hfit : (dentBegWord σ I).toNat * (dentLot I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .or
        (.binary .eq (.var "lot") (.intLit 0))
        (.binary .eq (.binary .div (.var "begLot") (.var "lot")) (.storage begRef))) =
        .ok (.bool true) := by
  have hbeg := evalExpr_flipperBeg_of_get (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := dentLocalsLotOneBegLot σ I) (dentLocalsLotOneBegLot_get_beg σ I)
  have hlot :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := dentLocalsLotOneBegLot σ I) (name := "lot") (value := dentLot I)
      (dentLocalsLotOneBegLot_get_lot σ I)
  have hbegLot :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := dentLocalsLotOneBegLot σ I) (name := "begLot")
      (value := dentBegLotWord σ I) (dentLocalsLotOneBegLot_get_begLot σ I)
  exact evalExpr_checkedMulRequire_ok hbeg hlot hbegLot rfl hfit

theorem evalExpr_dentLotOneMul_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hfit : (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (mul256 (.storage (bidsF (.var "id") "lot")) (.intLit ONE)) =
        .ok (.int (Int.ofNat (dentLotOneWord σ I).toNat)) := by
  have hlot := evalExpr_bidLot_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := dentLocals I) (id := dentId I)
    (dentLocals_get_id I) (dentLocals_get_bids I)
  exact evalExpr_mul256_ok hlot evalExpr_flipperONE rfl hfit

theorem evalExpr_dentLotOneMul_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hover : UInt256.size ≤ (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (mul256 (.storage (bidsF (.var "id") "lot")) (.intLit ONE)) =
        .revert := by
  have hlot := evalExpr_bidLot_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := dentLocals I) (id := dentId I)
    (dentLocals_get_id I) (dentLocals_get_bids I)
  exact evalExpr_mul256_revert hlot evalExpr_flipperONE hover

theorem evalExpr_dentLotOneRequire_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hfit : (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := dentLocalsLotOne σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .or
        (.binary .eq (.intLit ONE) (.intLit 0))
        (.binary .eq (.binary .div (.var "lotOne") (.intLit ONE))
          (.storage (bidsF (.var "id") "lot")))) =
        .ok (.bool true) := by
  have hlot := evalExpr_bidLot_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := dentLocalsLotOne σ I) (id := dentId I)
    (dentLocalsLotOne_get_id σ I) (dentLocalsLotOne_get_bids σ I)
  have hlotOne :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := dentLocalsLotOne σ I) (name := "lotOne")
      (value := dentLotOneWord σ I) (dentLocalsLotOne_get_lotOne σ I)
  exact evalExpr_checkedMulRequire_ok hlot evalExpr_flipperONE hlotOne rfl hfit

theorem evalExpr_dentDecreaseRequire_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hgt : (dentLotOneWord σ I).toNat < (dentBegLotWord σ I).toNat) :
    evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .le (.var "begLot") (.var "lotOne")) = .ok (.bool false) := by
  have hbegLot :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := dentLocalsLotOneBegLot σ I) (name := "begLot")
      (value := dentBegLotWord σ I) (dentLocalsLotOneBegLot_get_begLot σ I)
  have hlotOne :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := dentLocalsLotOneBegLot σ I) (name := "lotOne")
      (value := dentLotOneWord σ I) (dentLocalsLotOneBegLot_get_lotOne σ I)
  exact evalExpr_le_uint256_false hbegLot hlotOne hgt

set_option maxHeartbeats 1000000 in
theorem flipperDentSourceBodyBegLotOverflow {cA gh bl σ σ₀ A I} {g : UInt256}
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
    (htabGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (hfitLot : (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat < UInt256.size)
    (hoverBeg : UInt256.size ≤ (dentBegWord σ I).toNat * (dentLot I).toNat) :
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
  have hmulLot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (mul256 (.storage (bidsF (.var "id") "lot")) (.intLit ONE)) =
          .ok (.int (Int.ofNat (dentLotOneWord σ I).toNat)) := by
    dsimp [locals, evm0]
    exact evalExpr_dentLotOneMul_ok (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitLot
  have hreqLot :
      evalExpr? config { contract := contract, locals := dentLocalsLotOne σ I } evm0
        (.binary .or
          (.binary .eq (.intLit ONE) (.intLit 0))
          (.binary .eq (.binary .div (.var "lotOne") (.intLit ONE))
            (.storage (bidsF (.var "id") "lot")))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_dentLotOneRequire_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitLot
  have hmulRev :
      evalExpr? config { contract := contract, locals := dentLocalsLotOne σ I } evm0
        (mul256 (.storage begRef) (.var "lot")) = .revert := by
    dsimp [evm0]
    exact evalExpr_dentBegLotMul_afterLotOne_revert (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hoverBeg
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hticGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hendGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hbidGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using htabGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hlotGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hmulLot) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqLot) ?_
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hmulRev)
  simpa [ExecTransitionBody, dentTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0, dentLocalsLotOne] using
    ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem flipperDentSourceBodyLotOneOverflow {cA gh bl σ σ₀ A I} {g : UInt256}
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
    (htabGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (hoverLot : UInt256.size ≤ (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat) :
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
  have hmulLotRev :
      evalExpr? config { contract := contract, locals := locals } evm0
        (mul256 (.storage (bidsF (.var "id") "lot")) (.intLit ONE)) = .revert := by
    dsimp [locals, evm0]
    exact evalExpr_dentLotOneMul_revert (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hoverLot
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hticGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hendGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hbidGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using htabGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hlotGuard)) ?_
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hmulLotRev)
  simpa [ExecTransitionBody, dentTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem flipperDentSourceBodyInsufficientDecrease {cA gh bl σ σ₀ A I} {g : UInt256}
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
    (htabGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (hfitBeg : (dentBegWord σ I).toNat * (dentLot I).toNat < UInt256.size)
    (hfitLot : (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat < UInt256.size)
    (hgt : (dentLotOneWord σ I).toNat < (dentBegLotWord σ I).toNat) :
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
  have hmulBeg :
      evalExpr? config { contract := contract, locals := dentLocalsLotOne σ I } evm0
        (mul256 (.storage begRef) (.var "lot")) =
          .ok (.int (Int.ofNat (dentBegLotWord σ I).toNat)) := by
    dsimp [evm0]
    exact evalExpr_dentBegLotMul_afterLotOne_ok (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBeg
  have hreqBeg :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.binary .or
          (.binary .eq (.var "lot") (.intLit 0))
          (.binary .eq (.binary .div (.var "begLot") (.var "lot")) (.storage begRef))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_dentBegLotRequire_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBeg
  have hmulLot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (mul256 (.storage (bidsF (.var "id") "lot")) (.intLit ONE)) =
          .ok (.int (Int.ofNat (dentLotOneWord σ I).toNat)) := by
    dsimp [locals, evm0]
    exact evalExpr_dentLotOneMul_ok (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitLot
  have hreqLot :
      evalExpr? config { contract := contract, locals := dentLocalsLotOne σ I } evm0
        (.binary .or
          (.binary .eq (.intLit ONE) (.intLit 0))
          (.binary .eq (.binary .div (.var "lotOne") (.intLit ONE))
            (.storage (bidsF (.var "id") "lot")))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_dentLotOneRequire_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitLot
  have hdec :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.binary .le (.var "begLot") (.var "lotOne")) = .ok (.bool false) := by
    simpa [evm0] using
      evalExpr_dentDecreaseRequire_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hgt
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hticGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hendGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hbidGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using htabGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hlotGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hmulLot) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqLot) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hmulBeg) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqBeg) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hdec)
  simpa [ExecTransitionBody, dentTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0, dentLocalsLotOne,
    dentLocalsLotOneBegLot] using
    ExecFuncBody.execBlockRevert hblock

theorem flipperDentX_lotOneCheckedMulCall {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (h : RD flipperBytecode I g s0 ⟨4601⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨6305⟩
      [flipperONEWord, bidLotWord (dentId I) σ I, ⟨4638⟩, dentBid I,
        dentLot I, dentId I, ret, sel]
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4619 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) mem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 (twoWordHashMem (dentId I) ⟨1⟩ mem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (by simpa [bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) hmemSize)
      (by decide) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k4619, C4619, rd4619raw⟩ := rd4619.sload (by decide +native) (by evm_ov)
  have rd4621 : RD flipperBytecode I g s0 ⟨4621⟩
      [bidLotWord (dentId I) σ I, dentBid I, dentLot I, dentId I, ret, sel]
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4619 C4619 := by
    have hslotAdd :
        (⟨1⟩ : UInt256) + bidBaseOfWord (dentId I) = bidSlotOfWord (dentId I) ⟨1⟩ := by
      simpa [bidSlotOfWord] using
        (u256_add_comm (⟨1⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [bidLotWord, flipperSlotWord, hslotAdd] using rd4619raw
  have rd4625 := evm_run rd4621 with [
    raw push2 ⟨4638⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd4634 := rd4625.pushConst flipperONEWord
    (width := 8) (op := .PUSH8) (by decide +native : Operation.POp.PUSH8 ≠ .PUSH0)
    (by decide +native) (by evm_ov)
  exact ⟨_, _, evm_run rd4634 with [
    raw push2 ⟨6305⟩ (by decide +native) (by evm_ov),
    raw jump (by decide +native) (by jump_dest) (by evm_ov)]⟩

theorem flipperDentX_lotOneOverflow {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hover : UInt256.size ≤ (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat)
    (h : RD flipperBytecode I g s0 ⟨4601⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd6305⟩ := flipperDentX_lotOneCheckedMulCall hmemSize h
  exact flipperCheckedMulRevert (ret := ⟨4638⟩) (x := bidLotWord (dentId I) σ I)
    (y := flipperONEWord) (R := [dentBid I, dentLot I, dentId I, ret, sel])
    (by simp) hover rd6305

theorem flipperDentX_afterLotOneOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hfit : (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat < UInt256.size)
    (h : RD flipperBytecode I g s0 ⟨4601⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4638⟩
      [dentLotOneWord σ I, dentBid I, dentLot I, dentId I, ret, sel]
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd6305⟩ := flipperDentX_lotOneCheckedMulCall hmemSize h
  obtain ⟨_, _, rd4638⟩ := flipperCheckedMulOk
    (ret := ⟨4638⟩) (x := bidLotWord (dentId I) σ I)
    (y := flipperONEWord) (R := [dentBid I, dentLot I, dentId I, ret, sel])
    (by decide +native) (by simp) hfit rd6305
  exact ⟨_, _, by simpa [dentLotOneWord] using rd4638⟩

theorem flipperDentX_begLotCheckedMulCall {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (h : RD flipperBytecode I g s0 ⟨4638⟩
      [dentLotOneWord σ I, dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨6305⟩
      [dentLot I, dentBegWord σ I, ⟨4650⟩, dentLotOneWord σ I, dentBid I,
        dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4644 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨4650⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov)]
  obtain ⟨k4644, C4644, rd4644raw⟩ := rd4644.sload (by decide +native) (by evm_ov)
  have rd4645 : RD flipperBytecode I g s0 ⟨4645⟩
      [dentBegWord σ I, ⟨4650⟩, dentLotOneWord σ I, dentBid I, dentLot I,
        dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4644 C4644 := by
    simpa [dentBegWord, flipperSlotWord] using rd4644raw
  exact ⟨_, _, evm_run rd4645 with [
    raw dup5 (by decide +native) (by evm_ov),
    raw push2 ⟨6305⟩ (by decide +native) (by evm_ov),
    raw jump (by decide +native) (by jump_dest) (by evm_ov)]⟩

theorem flipperDentX_begLotOverflow {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hfitLot : (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat < UInt256.size)
    (hoverBeg : UInt256.size ≤ (dentBegWord σ I).toNat * (dentLot I).toNat)
    (h : RD flipperBytecode I g s0 ⟨4601⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd4638⟩ := flipperDentX_afterLotOneOk hmemSize hfitLot h
  obtain ⟨_, _, rd6305⟩ := flipperDentX_begLotCheckedMulCall rd4638
  exact flipperCheckedMulRevert (ret := ⟨4650⟩) (x := dentBegWord σ I)
    (y := dentLot I)
    (R := [dentLotOneWord σ I, dentBid I, dentLot I, dentId I, ret, sel])
    (by simp) hoverBeg rd6305

theorem flipperDentX_checkedMulOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hfitLot : (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg : (dentBegWord σ I).toNat * (dentLot I).toNat < UInt256.size)
    (h : RD flipperBytecode I g s0 ⟨4601⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4650⟩
      [dentBegLotWord σ I, dentLotOneWord σ I, dentBid I, dentLot I, dentId I, ret, sel]
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd4638⟩ := flipperDentX_afterLotOneOk hmemSize hfitLot h
  obtain ⟨_, _, rd6305⟩ := flipperDentX_begLotCheckedMulCall rd4638
  obtain ⟨_, _, rd4650⟩ := flipperCheckedMulOk
    (ret := ⟨4650⟩) (x := dentBegWord σ I) (y := dentLot I)
    (R := [dentLotOneWord σ I, dentBid I, dentLot I, dentId I, ret, sel])
    (by decide +native) (by simp) hfitBeg rd6305
  exact ⟨_, _, by simpa [dentBegLotWord] using rd4650⟩

theorem flipperDentX_decreaseOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hle : (dentBegLotWord σ I).toNat ≤ (dentLotOneWord σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨4650⟩
      [dentBegLotWord σ I, dentLotOneWord σ I, dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4733⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4653 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw gt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov)]
  have hgtWord : UInt256.gt (dentBegLotWord σ I) (dentLotOneWord σ I) = ⟨0⟩ :=
    ugt_zero hle
  rw [hgtWord, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4653
  exact ⟨_, _, evm_run rd4653 with [
    raw push2 ⟨4733⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) one_ne_zero_uint (by jump_dest) (by evm_ov)]⟩

theorem flipperDentX_insufficientDecrease {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hgt : (dentLotOneWord σ I).toNat < (dentBegLotWord σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨4650⟩
      [dentBegLotWord σ I, dentLotOneWord σ I, dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd4653 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw gt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov)]
  have hgtWord : UInt256.gt (dentBegLotWord σ I) (dentLotOneWord σ I) = ⟨1⟩ :=
    ugt_one hgt
  rw [hgtWord, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd4653
  have rd4657 := evm_run rd4653 with [
    raw push2 ⟨4733⟩ (by decide +native) (by evm_ov),
    raw jumpiNT (by decide +native) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)]
  exact RD.solcErrorStringFullWordRevertTail
    (pc := ⟨4657⟩) (len := ⟨29⟩) (word := flipperDentInsufficientDecreaseWord)
    rd4657
    (by
      unfold solcErrorStringFullWordRevertTailWf
      repeat' first | apply And.intro | decide +native)
    hmemSize hmemRead64 (by simp)

end Benchmarks.Dss.Flipper
