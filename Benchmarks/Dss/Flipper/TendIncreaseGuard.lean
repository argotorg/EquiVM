import Benchmarks.Dss.Flipper.TendBidGuard
import Benchmarks.Dss.Flipper.CheckedMul

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Flipper

/-! ## `tend` checked increase guard -/

abbrev flipperTendInsufficientIncreaseWord : UInt256 :=
  ⟨31853446598541861569293789059947845366293458314517492863577877664563229360128⟩

abbrev tendBegWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperSlotWord ⟨4⟩ σ I

abbrev tendBegBidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.mul (tendBegWord σ I) (bidBidWord (tendId I) σ I)

abbrev tendBidOneWord (I : ExecutionEnv) : UInt256 :=
  UInt256.mul (tendBid I) flipperONEWord

abbrev tendLocalsBidOne (I : ExecutionEnv) : Store :=
  (tendLocals I).insert "bidOne" (.int (Int.ofNat (tendBidOneWord I).toNat))

abbrev tendLocalsBidOneBegBid (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (tendLocalsBidOne I).insert "begBid" (.int (Int.ofNat (tendBegBidWord σ I).toNat))

theorem tendLocals_get_beg (I : ExecutionEnv) :
    (tendLocals I).get? "beg" = none := by
  rw [tendLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem tendLocalsBidOne_get_bidOne (I : ExecutionEnv) :
    (tendLocalsBidOne I).get? "bidOne" =
      some (.int (Int.ofNat (tendBidOneWord I).toNat)) := by
  rw [tendLocalsBidOne, store_get_self]

theorem tendLocalsBidOne_get_bid (I : ExecutionEnv) :
    (tendLocalsBidOne I).get? "bid" =
      some (.int (Int.ofNat (tendBid I).toNat)) := by
  rw [tendLocalsBidOne, store_get_ne _ _ (by decide), tendLocals_get_bid]

theorem tendLocalsBidOne_get_id (I : ExecutionEnv) :
    (tendLocalsBidOne I).get? "id" =
      some (.int (Int.ofNat (tendId I).toNat)) := by
  rw [tendLocalsBidOne, store_get_ne _ _ (by decide), tendLocals_get_id]

theorem tendLocalsBidOne_get_bids (I : ExecutionEnv) :
    (tendLocalsBidOne I).get? "bids" = none := by
  rw [tendLocalsBidOne, store_get_ne _ _ (by decide), tendLocals_get_bids]

theorem tendLocalsBidOne_get_beg (I : ExecutionEnv) :
    (tendLocalsBidOne I).get? "beg" = none := by
  rw [tendLocalsBidOne, store_get_ne _ _ (by decide), tendLocals_get_beg]

theorem tendLocalsBidOneBegBid_get_begBid (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsBidOneBegBid σ I).get? "begBid" =
      some (.int (Int.ofNat (tendBegBidWord σ I).toNat)) := by
  rw [tendLocalsBidOneBegBid, store_get_self]

theorem tendLocalsBidOneBegBid_get_bidOne (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsBidOneBegBid σ I).get? "bidOne" =
      some (.int (Int.ofNat (tendBidOneWord I).toNat)) := by
  rw [tendLocalsBidOneBegBid, store_get_ne _ _ (by decide), tendLocalsBidOne_get_bidOne]

theorem tendLocalsBidOneBegBid_get_bid (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsBidOneBegBid σ I).get? "bid" =
      some (.int (Int.ofNat (tendBid I).toNat)) := by
  rw [tendLocalsBidOneBegBid, store_get_ne _ _ (by decide), tendLocalsBidOne_get_bid]

theorem tendLocalsBidOneBegBid_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsBidOneBegBid σ I).get? "id" =
      some (.int (Int.ofNat (tendId I).toNat)) := by
  rw [tendLocalsBidOneBegBid, store_get_ne _ _ (by decide), tendLocalsBidOne_get_id]

theorem tendLocalsBidOneBegBid_get_bids (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsBidOneBegBid σ I).get? "bids" = none := by
  rw [tendLocalsBidOneBegBid, store_get_ne _ _ (by decide), tendLocalsBidOne_get_bids]

theorem tendLocalsBidOneBegBid_get_beg (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsBidOneBegBid σ I).get? "beg" = none := by
  rw [tendLocalsBidOneBegBid, store_get_ne _ _ (by decide), tendLocalsBidOne_get_beg]

theorem evalExpr_tendBidOneMul_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hfit : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I) (mul256 (.var "bid") (.intLit ONE)) =
        .ok (.int (Int.ofNat (tendBidOneWord I).toNat)) := by
  have hbid :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := tendLocals I) (name := "bid") (value := tendBid I)
      (tendLocals_get_bid I)
  exact evalExpr_mul256_ok hbid evalExpr_flipperONE rfl hfit

theorem evalExpr_tendBidOneMul_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hover : UInt256.size ≤ (tendBid I).toNat * flipperONEWord.toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I) (mul256 (.var "bid") (.intLit ONE)) =
        .revert := by
  have hbid :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := tendLocals I) (name := "bid") (value := tendBid I)
      (tendLocals_get_bid I)
  exact evalExpr_mul256_revert hbid evalExpr_flipperONE hover

theorem evalExpr_tendBidOneRequire_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hfit : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := tendLocalsBidOne I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .or
        (.binary .eq (.intLit ONE) (.intLit 0))
        (.binary .eq (.binary .div (.var "bidOne") (.intLit ONE)) (.var "bid"))) =
        .ok (.bool true) := by
  have hbid :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := tendLocalsBidOne I) (name := "bid") (value := tendBid I)
      (tendLocalsBidOne_get_bid I)
  have hbidOne :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := tendLocalsBidOne I) (name := "bidOne") (value := tendBidOneWord I)
      (tendLocalsBidOne_get_bidOne I)
  exact evalExpr_checkedMulRequire_ok hbid evalExpr_flipperONE hbidOne rfl hfit

theorem evalExpr_tendBegBidMul_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hfit :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := tendLocalsBidOne I }
      (initState cA gh bl σ σ₀ g A I)
      (mul256 (.storage begRef) (.storage (bidsF (.var "id") "bid"))) =
        .ok (.int (Int.ofNat (tendBegBidWord σ I).toNat)) := by
  have hbeg := evalExpr_flipperBeg_of_get (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := tendLocalsBidOne I) (tendLocalsBidOne_get_beg I)
  have hbid := evalExpr_bidBid_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := tendLocalsBidOne I) (id := tendId I)
    (tendLocalsBidOne_get_id I) (tendLocalsBidOne_get_bids I)
  exact evalExpr_mul256_ok hbeg hbid rfl hfit

theorem evalExpr_tendBegBidMul_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hover :
      UInt256.size ≤ (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := tendLocalsBidOne I }
      (initState cA gh bl σ σ₀ g A I)
      (mul256 (.storage begRef) (.storage (bidsF (.var "id") "bid"))) =
        .revert := by
  have hbeg := evalExpr_flipperBeg_of_get (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := tendLocalsBidOne I) (tendLocalsBidOne_get_beg I)
  have hbid := evalExpr_bidBid_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := tendLocalsBidOne I) (id := tendId I)
    (tendLocalsBidOne_get_id I) (tendLocalsBidOne_get_bids I)
  exact evalExpr_mul256_revert hbeg hbid hover

theorem evalExpr_tendBegBidRequire_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hfit :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .or
        (.binary .eq (.storage (bidsF (.var "id") "bid")) (.intLit 0))
        (.binary .eq (.binary .div (.var "begBid")
          (.storage (bidsF (.var "id") "bid"))) (.storage begRef))) =
        .ok (.bool true) := by
  have hbeg := evalExpr_flipperBeg_of_get (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := tendLocalsBidOneBegBid σ I) (tendLocalsBidOneBegBid_get_beg σ I)
  have hbid := evalExpr_bidBid_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := tendLocalsBidOneBegBid σ I) (id := tendId I)
    (tendLocalsBidOneBegBid_get_id σ I) (tendLocalsBidOneBegBid_get_bids σ I)
  have hbegBid :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := tendLocalsBidOneBegBid σ I) (name := "begBid")
      (value := tendBegBidWord σ I) (tendLocalsBidOneBegBid_get_begBid σ I)
  exact evalExpr_checkedMulRequire_ok hbeg hbid hbegBid rfl hfit

theorem evalExpr_tendIncreaseRequire_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : (tendBidOneWord I).toNat < (tendBegBidWord σ I).toNat)
    (htab : tendBid I ≠ bidTabWord (tendId I) σ I) :
    evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .or
        (.binary .ge (.var "bidOne") (.var "begBid"))
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
        .ok (.bool false) := by
  have hbidOne :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := tendLocalsBidOneBegBid σ I) (name := "bidOne")
      (value := tendBidOneWord I) (tendLocalsBidOneBegBid_get_bidOne σ I)
  have hbegBid :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := tendLocalsBidOneBegBid σ I) (name := "begBid")
      (value := tendBegBidWord σ I) (tendLocalsBidOneBegBid_get_begBid σ I)
  have hbid :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := tendLocalsBidOneBegBid σ I) (name := "bid")
      (value := tendBid I) (tendLocalsBidOneBegBid_get_bid σ I)
  have htabEval := evalExpr_bidTab_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := tendLocalsBidOneBegBid σ I) (id := tendId I)
    (tendLocalsBidOneBegBid_get_id σ I) (tendLocalsBidOneBegBid_get_bids σ I)
  have hleft :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ g A I)
        (.binary .ge (.var "bidOne") (.var "begBid")) = .ok (.bool false) :=
    evalExpr_ge_uint256_false hbidOne hbegBid hlt
  have hright :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ g A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool false) := by
    apply evalExpr_eq_int_false hbid htabEval
    intro hbad
    exact htab (u256_inj (Int.ofNat.inj hbad))
  exact evalExpr_or_false_right hleft hright

set_option maxHeartbeats 1000000 in
theorem flipperTendSourceBodyBidOneOverflow {cA gh bl σ σ₀ A I} {g : UInt256}
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
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hover : UInt256.size ≤ (tendBid I).toNat * flipperONEWord.toNat) :
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
  have hmulRev :
      evalExpr? config { contract := contract, locals := locals } evm0
        (mul256 (.var "bid") (.intLit ONE)) = .revert := by
    dsimp [locals, evm0]
    exact evalExpr_tendBidOneMul_revert (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hover
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hticGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hendGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hlotGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using htabGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hbidGuard)) ?_
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hmulRev)
  simpa [ExecTransitionBody, tendTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem flipperTendSourceBodyBegBidOverflow {cA gh bl σ σ₀ A I} {g : UInt256}
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
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hoverBeg :
      UInt256.size ≤ (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat) :
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
  have hmulBid :
      evalExpr? config { contract := contract, locals := locals } evm0
        (mul256 (.var "bid") (.intLit ONE)) =
          .ok (.int (Int.ofNat (tendBidOneWord I).toNat)) := by
    dsimp [locals, evm0]
    exact evalExpr_tendBidOneMul_ok (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBid
  have hreqBid :
      evalExpr? config { contract := contract, locals := tendLocalsBidOne I } evm0
        (.binary .or
          (.binary .eq (.intLit ONE) (.intLit 0))
          (.binary .eq (.binary .div (.var "bidOne") (.intLit ONE)) (.var "bid"))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_tendBidOneRequire_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBid
  have hmulBegRev :
      evalExpr? config { contract := contract, locals := tendLocalsBidOne I } evm0
        (mul256 (.storage begRef) (.storage (bidsF (.var "id") "bid"))) = .revert := by
    dsimp [evm0]
    exact evalExpr_tendBegBidMul_revert (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hoverBeg
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hticGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hendGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hlotGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using htabGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hbidGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hmulBid) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqBid) ?_
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hmulBegRev)
  simpa [ExecTransitionBody, tendTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0, tendLocalsBidOne] using
    ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem flipperTendSourceBodyInsufficientIncrease {cA gh bl σ σ₀ A I} {g : UInt256}
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
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hlt : (tendBidOneWord I).toNat < (tendBegBidWord σ I).toNat)
    (htab : tendBid I ≠ bidTabWord (tendId I) σ I) :
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
  have hmulBid :
      evalExpr? config { contract := contract, locals := locals } evm0
        (mul256 (.var "bid") (.intLit ONE)) =
          .ok (.int (Int.ofNat (tendBidOneWord I).toNat)) := by
    dsimp [locals, evm0]
    exact evalExpr_tendBidOneMul_ok (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBid
  have hreqBid :
      evalExpr? config { contract := contract, locals := tendLocalsBidOne I } evm0
        (.binary .or
          (.binary .eq (.intLit ONE) (.intLit 0))
          (.binary .eq (.binary .div (.var "bidOne") (.intLit ONE)) (.var "bid"))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_tendBidOneRequire_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBid
  have hmulBeg :
      evalExpr? config { contract := contract, locals := tendLocalsBidOne I } evm0
        (mul256 (.storage begRef) (.storage (bidsF (.var "id") "bid"))) =
          .ok (.int (Int.ofNat (tendBegBidWord σ I).toNat)) := by
    dsimp [evm0]
    exact evalExpr_tendBegBidMul_ok (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBeg
  have hreqBeg :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.binary .or
          (.binary .eq (.storage (bidsF (.var "id") "bid")) (.intLit 0))
          (.binary .eq (.binary .div (.var "begBid")
            (.storage (bidsF (.var "id") "bid"))) (.storage begRef))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_tendBegBidRequire_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBeg
  have hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool false) := by
    simpa [evm0] using
      evalExpr_tendIncreaseRequire_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hlt htab
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hticGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hendGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hlotGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using htabGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hbidGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hmulBid) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqBid) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hmulBeg) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqBeg) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hinc)
  simpa [ExecTransitionBody, tendTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0, tendLocalsBidOne,
    tendLocalsBidOneBegBid] using
    ExecFuncBody.execBlockRevert hblock

theorem flipperTendX_begBidCheckedMulCall {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (h : RD flipperBytecode I g s0 ⟨3330⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨6305⟩
      [bidBidWord (tendId I) σ I, tendBegWord σ I, ⟨3358⟩, tendBid I,
        tendLot I, tendId I, ret, sel]
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3333 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3333, C3333, rd3333raw⟩ := rd3333.sload (by native_decide) (by evm_ov)
  have rd3334 : RD flipperBytecode I g s0 ⟨3334⟩
      [tendBegWord σ I, tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3333 C3333 := by
    simpa [tendBegWord, flipperSlotWord] using rd3333raw
  have rd3348 := evm_run rd3334 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
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
      (by decide) (by evm_ov)]
  obtain ⟨k3348, C3348, rd3348raw⟩ := rd3348.sload (by native_decide) (by evm_ov)
  have rd3349 : RD flipperBytecode I g s0 ⟨3349⟩
      [bidBidWord (tendId I) σ I, tendBegWord σ I, tendBid I,
        tendLot I, tendId I, ret, sel]
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3348 C3348 := by
    simpa [bidBidWord, flipperSlotWord] using rd3348raw
  exact ⟨_, _, evm_run rd3349 with [
    raw push2 ⟨3358⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨6305⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]⟩

theorem flipperTendX_begBidOverflow {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hover :
      UInt256.size ≤ (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨3330⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd6305⟩ := flipperTendX_begBidCheckedMulCall hmemSize h
  exact flipperCheckedMulRevert (ret := ⟨3358⟩) (x := tendBegWord σ I)
    (y := bidBidWord (tendId I) σ I)
    (R := [tendBid I, tendLot I, tendId I, ret, sel])
    (by simp) hover rd6305

theorem flipperTendX_afterBegBidOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hfit :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (h : RD flipperBytecode I g s0 ⟨3330⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3358⟩
      [tendBegBidWord σ I, tendBid I, tendLot I, tendId I, ret, sel]
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd6305⟩ := flipperTendX_begBidCheckedMulCall hmemSize h
  obtain ⟨_, _, rd3358⟩ := flipperCheckedMulOk
    (ret := ⟨3358⟩) (x := tendBegWord σ I)
    (y := bidBidWord (tendId I) σ I)
    (R := [tendBid I, tendLot I, tendId I, ret, sel])
    (by native_decide) (by simp) hfit rd6305
  exact ⟨_, _, by simpa [tendBegBidWord] using rd3358⟩

theorem flipperTendX_bidOneCheckedMulCall {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (h : RD flipperBytecode I g s0 ⟨3358⟩
      [tendBegBidWord σ I, tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨6305⟩
      [flipperONEWord, tendBid I, ⟨3376⟩, tendBegBidWord σ I, tendBid I,
        tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3363 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨3376⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd3372 := rd3363.pushConst flipperONEWord
    (width := 8) (op := .PUSH8) (by native_decide : Operation.POp.PUSH8 ≠ .PUSH0)
    (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd3372 with [
    raw push2 ⟨6305⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]⟩

theorem flipperTendX_bidOneOverflow {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hoverBid : UInt256.size ≤ (tendBid I).toNat * flipperONEWord.toNat)
    (h : RD flipperBytecode I g s0 ⟨3330⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd3358⟩ := flipperTendX_afterBegBidOk hmemSize hfitBeg h
  obtain ⟨_, _, rd6305⟩ := flipperTendX_bidOneCheckedMulCall rd3358
  exact flipperCheckedMulRevert (ret := ⟨3376⟩) (x := tendBid I)
    (y := flipperONEWord)
    (R := [tendBegBidWord σ I, tendBid I, tendLot I, tendId I, ret, sel])
    (by simp) hoverBid rd6305

theorem flipperTendX_checkedMulOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (h : RD flipperBytecode I g s0 ⟨3330⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3376⟩
      [tendBidOneWord I, tendBegBidWord σ I, tendBid I, tendLot I, tendId I, ret, sel]
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd3358⟩ := flipperTendX_afterBegBidOk hmemSize hfitBeg h
  obtain ⟨_, _, rd6305⟩ := flipperTendX_bidOneCheckedMulCall rd3358
  obtain ⟨_, _, rd3376⟩ := flipperCheckedMulOk
    (ret := ⟨3376⟩) (x := tendBid I) (y := flipperONEWord)
    (R := [tendBegBidWord σ I, tendBid I, tendLot I, tendId I, ret, sel])
    (by native_decide) (by simp) hfitBid rd6305
  exact ⟨_, _, by simpa [tendBidOneWord] using rd3376⟩

theorem flipperTendX_increaseOkByGe {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hge : (tendBegBidWord σ I).toNat ≤ (tendBidOneWord I).toNat)
    (h : RD flipperBytecode I g s0 ⟨3376⟩
      [tendBidOneWord I, tendBegBidWord σ I, tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3486⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3380 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hltWord : UInt256.lt (tendBidOneWord I) (tendBegBidWord σ I) = ⟨0⟩ :=
    ult_zero hge
  rw [hltWord, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd3380
  have rd3405 := evm_run rd3380 with [
    raw push2 ⟨3405⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov)]
  exact ⟨_, _, evm_run rd3405 with [
    raw push2 ⟨3486⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]⟩

theorem flipperTendX_increaseOkByTab {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hlt : (tendBidOneWord I).toNat < (tendBegBidWord σ I).toNat)
    (htab : tendBid I = bidTabWord (tendId I) σ I)
    (h : RD flipperBytecode I g s0 ⟨3376⟩
      [tendBidOneWord I, tendBegBidWord σ I, tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3486⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3380 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hltWord : UInt256.lt (tendBidOneWord I) (tendBegBidWord σ I) = ⟨1⟩ :=
    ult_one hlt
  rw [hltWord, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd3380
  have rd3385 := evm_run rd3380 with [
    raw push2 ⟨3405⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  have rd3399 := evm_run rd3385 with [
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
  obtain ⟨k3399, C3399, rd3399raw⟩ := rd3399.sload (by native_decide) (by evm_ov)
  have rd3403 : RD flipperBytecode I g s0 ⟨3403⟩
      [bidTabWord (tendId I) σ I, tendBid I, tendLot I, tendId I, ret, sel]
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3399 C3399 := by
    have hslotAdd :
        (⟨5⟩ : UInt256) + bidBaseOfWord (tendId I) = bidSlotOfWord (tendId I) ⟨5⟩ := by
      simpa [bidSlotOfWord] using
        (u256_add_comm (⟨5⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [bidTabWord, flipperSlotWord, hslotAdd] using rd3399raw
  have rd3405 := evm_run rd3403 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (tendBid I) (bidTabWord (tendId I) σ I) = ⟨1⟩ := by
    rw [htab]
    exact u256_eq_refl _
  rw [heq] at rd3405
  exact ⟨_, _, evm_run rd3405 with [
    raw push2 ⟨3486⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]⟩

theorem flipperTendX_insufficientIncrease {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlt : (tendBidOneWord I).toNat < (tendBegBidWord σ I).toNat)
    (htab : tendBid I ≠ bidTabWord (tendId I) σ I)
    (h : RD flipperBytecode I g s0 ⟨3376⟩
      [tendBidOneWord I, tendBegBidWord σ I, tendBid I, tendLot I, tendId I, ret, sel]
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
  have rd3380 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hltWord : UInt256.lt (tendBidOneWord I) (tendBegBidWord σ I) = ⟨1⟩ :=
    ult_one hlt
  rw [hltWord, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd3380
  have rd3385 := evm_run rd3380 with [
    raw push2 ⟨3405⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  have rd3399 := evm_run rd3385 with [
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
  obtain ⟨k3399, C3399, rd3399raw⟩ := rd3399.sload (by native_decide) (by evm_ov)
  have rd3403 : RD flipperBytecode I g s0 ⟨3403⟩
      [bidTabWord (tendId I) σ I, tendBid I, tendLot I, tendId I, ret, sel]
      memTab (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3399 C3399 := by
    have hslotAdd :
        (⟨5⟩ : UInt256) + bidBaseOfWord (tendId I) = bidSlotOfWord (tendId I) ⟨5⟩ := by
      simpa [bidSlotOfWord] using
        (u256_add_comm (⟨5⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [memTab, bidTabWord, flipperSlotWord, hslotAdd] using rd3399raw
  have rd3405 := evm_run rd3403 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (tendBid I) (bidTabWord (tendId I) σ I) = ⟨0⟩ :=
    u256_eq_of_ne htab
  rw [heq] at rd3405
  have rd3410 := evm_run rd3405 with [
    raw push2 ⟨3486⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)]
  exact RD.solcErrorStringFullWordRevertTail
    (pc := ⟨3410⟩) (len := ⟨29⟩) (word := flipperTendInsufficientIncreaseWord)
    rd3410
    (by
      unfold solcErrorStringFullWordRevertTailWf
      repeat' first | apply And.intro | native_decide)
    hmemTabSize hmemTabRead64 (by simp)

end Benchmarks.Dss.Flipper
