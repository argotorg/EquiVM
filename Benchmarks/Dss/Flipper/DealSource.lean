import Benchmarks.Dss.Flipper.BidDelete
import Benchmarks.Dss.Flipper.ExternalTargets

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Source-side helpers for `deal(uint256)` -/

abbrev dealId (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev dealLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "id" (.int (Int.ofNat (dealId I).toNat))

abbrev dealFinishedGuard : Expr :=
  .binary .and
    (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0))
    (.binary .or
      (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
      (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)))

theorem dealLocals_get_id (I : ExecutionEnv) :
    (dealLocals I).get? "id" =
      some (.int (Int.ofNat (dealId I).toNat)) := by
  rw [dealLocals, store_get_self]

theorem dealLocals_get_bids (I : ExecutionEnv) :
    (dealLocals I).get? "bids" = none := by
  rw [dealLocals, store_get_ne _ _ (by decide)]
  simp

theorem dealLocals_get_cat (I : ExecutionEnv) :
    (dealLocals I).get? "cat" = none := by
  rw [dealLocals, store_get_ne _ _ (by decide)]
  simp

theorem dealLocals_get_vat (I : ExecutionEnv) :
    (dealLocals I).get? "vat" = none := by
  rw [dealLocals, store_get_ne _ _ (by decide)]
  simp

theorem dealLocals_get_ilk (I : ExecutionEnv) :
    (dealLocals I).get? "ilk" = none := by
  rw [dealLocals, store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_dealTicNeZero_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (htic : bidTicWord (dealId I) σ I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dealLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
        .ok (.bool true) := by
  have hticEval :=
    evalExpr_bidTic_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dealLocals I) (id := dealId I) (dealLocals_get_id I)
      (dealLocals_get_bids I)
  have hneNat : ¬ (bidTicWord (dealId I) σ I).toNat = 0 := by
    intro hzero
    exact htic (uint256_toNat_eq_zero hzero)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hticEval]
  simp [evalExpr?, evalBinaryOp?, hneNat]
  all_goals decide

theorem evalExpr_dealTicNeZero_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (htic : bidTicWord (dealId I) σ I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dealLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
        .ok (.bool false) := by
  have hticEval :=
    evalExpr_bidTic_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dealLocals I) (id := dealId I) (dealLocals_get_id I)
      (dealLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hticEval]
  simp [evalExpr?, evalBinaryOp?, htic]
  all_goals decide

theorem evalExpr_dealTicLtTimestamp_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : (bidTicWord (dealId I) σ I).toNat < (UInt256.ofNat I.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := dealLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
        .ok (.bool true) := by
  have hticEval :=
    evalExpr_bidTic_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dealLocals I) (id := dealId I) (dealLocals_get_id I)
      (dealLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hticEval]
  simp [evalExpr?, envValue, initState, evalBinaryOp?, hlt]
  all_goals decide

theorem evalExpr_dealTicLtTimestamp_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hge : (UInt256.ofNat I.header.timestamp).toNat ≤ (bidTicWord (dealId I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := dealLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
        .ok (.bool false) := by
  have hticEval :=
    evalExpr_bidTic_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dealLocals I) (id := dealId I) (dealLocals_get_id I)
      (dealLocals_get_bids I)
  have hnot : ¬ (bidTicWord (dealId I) σ I).toNat <
      (UInt256.ofNat I.header.timestamp).toNat := by
    omega
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hticEval]
  simp [evalExpr?, envValue, initState, evalBinaryOp?, hnot]
  all_goals decide

theorem evalExpr_dealEndLtTimestamp_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : (bidEndWord (dealId I) σ I).toNat < (UInt256.ofNat I.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := dealLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool true) := by
  have hendEval :=
    evalExpr_bidEnd_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dealLocals I) (id := dealId I) (dealLocals_get_id I)
      (dealLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hendEval]
  simp [evalExpr?, envValue, initState, evalBinaryOp?, hlt]
  all_goals decide

theorem evalExpr_dealEndLtTimestamp_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hge : (UInt256.ofNat I.header.timestamp).toNat ≤ (bidEndWord (dealId I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := dealLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool false) := by
  have hendEval :=
    evalExpr_bidEnd_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dealLocals I) (id := dealId I) (dealLocals_get_id I)
      (dealLocals_get_bids I)
  have hnot : ¬ (bidEndWord (dealId I) σ I).toNat <
      (UInt256.ofNat I.header.timestamp).toNat := by
    omega
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hendEval]
  simp [evalExpr?, envValue, initState, evalBinaryOp?, hnot]
  all_goals decide

theorem evalExpr_dealFinishedGuard_true_left {cA gh bl σ σ₀ A I} {g : Sat256}
    (hticNe : bidTicWord (dealId I) σ I ≠ ⟨0⟩)
    (hticLt : (bidTicWord (dealId I) σ I).toNat <
      (UInt256.ofNat I.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := dealLocals I }
      (initState cA gh bl σ σ₀ g A I) dealFinishedGuard = .ok (.bool true) := by
  have hne := evalExpr_dealTicNeZero_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hticNe
  have hlt := evalExpr_dealTicLtTimestamp_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hticLt
  simp [dealFinishedGuard, evalExpr?, EvalResult.bind, bind, pure, hne, hlt]

theorem evalExpr_dealFinishedGuard_true_right {cA gh bl σ σ₀ A I} {g : Sat256}
    (hticNe : bidTicWord (dealId I) σ I ≠ ⟨0⟩)
    (hticGe : (UInt256.ofNat I.header.timestamp).toNat ≤
      (bidTicWord (dealId I) σ I).toNat)
    (hendLt : (bidEndWord (dealId I) σ I).toNat <
      (UInt256.ofNat I.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := dealLocals I }
      (initState cA gh bl σ σ₀ g A I) dealFinishedGuard = .ok (.bool true) := by
  have hne := evalExpr_dealTicNeZero_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hticNe
  have hticFalse := evalExpr_dealTicLtTimestamp_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hticGe
  have hendTrue := evalExpr_dealEndLtTimestamp_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hendLt
  simp [dealFinishedGuard, evalExpr?, EvalResult.bind, bind, pure, hne, hticFalse,
    hendTrue]

theorem evalExpr_dealFinishedGuard_false_tic_zero {cA gh bl σ σ₀ A I} {g : Sat256}
    (htic : bidTicWord (dealId I) σ I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dealLocals I }
      (initState cA gh bl σ σ₀ g A I) dealFinishedGuard = .ok (.bool false) := by
  have hne := evalExpr_dealTicNeZero_false (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) htic
  simp [dealFinishedGuard, evalExpr?, EvalResult.bind, bind, pure, hne]

theorem evalExpr_dealFinishedGuard_false_not_expired {cA gh bl σ σ₀ A I} {g : Sat256}
    (hticNe : bidTicWord (dealId I) σ I ≠ ⟨0⟩)
    (hticGe : (UInt256.ofNat I.header.timestamp).toNat ≤
      (bidTicWord (dealId I) σ I).toNat)
    (hendGe : (UInt256.ofNat I.header.timestamp).toNat ≤
      (bidEndWord (dealId I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := dealLocals I }
      (initState cA gh bl σ σ₀ g A I) dealFinishedGuard = .ok (.bool false) := by
  have hne := evalExpr_dealTicNeZero_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hticNe
  have hticFalse := evalExpr_dealTicLtTimestamp_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hticGe
  have hendFalse := evalExpr_dealEndLtTimestamp_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hendGe
  simp [dealFinishedGuard, evalExpr?, EvalResult.bind, bind, pure, hne, hticFalse,
    hendFalse]

theorem evalExpr_dealCat {evm : EVM.State} :
    evalExpr? config { contract := contract, locals := dealLocals evm.executionEnv } evm
      (.storage catRef) =
        .ok (.address (flipperCatAddress evm.accountMap evm.executionEnv)) := by
  exact evalExpr_flipperStorageCatOfLocals (dealLocals_get_cat evm.executionEnv)

theorem evalExpr_dealVat {evm : EVM.State} :
    evalExpr? config { contract := contract, locals := dealLocals evm.executionEnv } evm
      (.storage vatRef) =
        .ok (.address (flipperVatAddress evm.accountMap evm.executionEnv)) := by
  exact evalExpr_flipperStorageVatOfLocals (dealLocals_get_vat evm.executionEnv)

theorem evalExpr_dealIlk_ofLocals {evm : EVM.State} {locals : Store}
    (hilk : locals.get? "ilk" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage ilkRef) =
        .ok (.fixedBytes bytes32Width
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩))) := by
  rw [evalExpr_storage_scalar
    (t := .bytes bytes32Width)
    (er := ({ base := "ilk", steps := [] } : EvaledStorageRef))
    (loc := bytes32Loc ⟨3⟩)
    (hbase := hilk)
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, ilkRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, bytes32St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, ilkRef])]
  exact congrArg EvalResult.ok (flipperStorageLocLoad_bytes32 evm ⟨3⟩)

theorem evalExpr_dealIlk {evm : EVM.State} :
    evalExpr? config { contract := contract, locals := dealLocals evm.executionEnv } evm
      (.storage ilkRef) =
        .ok (.fixedBytes bytes32Width
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩))) := by
  exact evalExpr_dealIlk_ofLocals (dealLocals_get_ilk evm.executionEnv)

abbrev dealClawArgValsOf (evm : EVM.State) (id : UInt256) : List Value :=
  [.int (Int.ofNat
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (bidSlotOfWord id ⟨5⟩)).toNat)]

abbrev dealClawArgVals (evm : EVM.State) : List Value :=
  dealClawArgValsOf evm (dealId evm.executionEnv)

abbrev dealFluxArgValsOf (evm : EVM.State) (id : UInt256) : List Value :=
  [.fixedBytes bytes32Width
      (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)),
    .address evm.executionEnv.codeOwner,
    .address (AccountAddress.ofNat
      (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (bidPackedSlotOfWord id))
        solcAddrMask).toNat),
    .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidSlotOfWord id ⟨1⟩)).toNat)]

abbrev dealFluxArgVals (evm : EVM.State) : List Value :=
  dealFluxArgValsOf evm (dealId evm.executionEnv)

theorem evalExprs_dealClawArgs_ofLocals {evm : EVM.State} {locals : Store} {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExprs? config { contract := contract, locals := locals } evm
      [.storage (bidsF (.var "id") "tab")] = .ok (dealClawArgValsOf evm id) := by
  have htab := evalExpr_bidTab_of_get_id_evm (evm := evm)
    (locals := locals) (id := id) hid hbids
  unfold evalExprs?
  simp only [EvalResult.bind, bind, pure]
  rw [htab]
  rfl

theorem evalExprs_dealClawArgs {evm : EVM.State} :
    evalExprs? config { contract := contract, locals := dealLocals evm.executionEnv } evm
      [.storage (bidsF (.var "id") "tab")] = .ok (dealClawArgVals evm) := by
  exact evalExprs_dealClawArgs_ofLocals (dealLocals_get_id evm.executionEnv)
    (dealLocals_get_bids evm.executionEnv)

theorem evalExprs_dealFluxArgs_ofLocals {evm : EVM.State} {locals : Store} {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none)
    (hilk : locals.get? "ilk" = none) :
    evalExprs? config { contract := contract, locals := locals } evm
      [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
        .storage (bidsF (.var "id") "lot")] =
        .ok (dealFluxArgValsOf evm id) := by
  have hilkEval := evalExpr_dealIlk_ofLocals (evm := evm) (locals := locals) hilk
  have hguy := evalExpr_bidGuy_of_get_id_evm (evm := evm)
    (locals := locals) (id := id) hid hbids
  have hlot := evalExpr_bidLot_of_get_id_evm (evm := evm)
    (locals := locals) (id := id) hid hbids
  simp only [evalExprs?, evalExpr?, envValue, thisAddr, hilkEval, hguy, hlot,
    dealFluxArgValsOf, EvalResult.bind, bind, pure]

theorem evalExprs_dealFluxArgs {evm : EVM.State} :
    evalExprs? config { contract := contract, locals := dealLocals evm.executionEnv } evm
      [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
        .storage (bidsF (.var "id") "lot")] =
        .ok (dealFluxArgVals evm) := by
  exact evalExprs_dealFluxArgs_ofLocals (dealLocals_get_id evm.executionEnv)
    (dealLocals_get_bids evm.executionEnv) (dealLocals_get_ilk evm.executionEnv)

theorem dealLocalsAfterClaw_get_id (I : ExecutionEnv) :
    ((dealLocals I).insert "_clawRet" (collapseReturns [])).get? "id" =
      some (.int (Int.ofNat (dealId I).toNat)) := by
  rw [store_get_ne _ _ (by decide)]
  exact dealLocals_get_id I

theorem dealLocalsAfterClaw_get_bids (I : ExecutionEnv) :
    ((dealLocals I).insert "_clawRet" (collapseReturns [])).get? "bids" = none := by
  rw [store_get_ne _ _ (by decide)]
  exact dealLocals_get_bids I

theorem dealLocalsAfterClaw_get_vat (I : ExecutionEnv) :
    ((dealLocals I).insert "_clawRet" (collapseReturns [])).get? "vat" = none := by
  rw [store_get_ne _ _ (by decide)]
  exact dealLocals_get_vat I

theorem dealLocalsAfterClaw_get_ilk (I : ExecutionEnv) :
    ((dealLocals I).insert "_clawRet" (collapseReturns [])).get? "ilk" = none := by
  rw [store_get_ne _ _ (by decide)]
  exact dealLocals_get_ilk I

theorem dealLocalsAfterCalls_get_id (I : ExecutionEnv) :
    (((dealLocals I).insert "_clawRet" (collapseReturns [])).insert "_fluxRet"
        (collapseReturns [])).get? "id" =
      some (.int (Int.ofNat (dealId I).toNat)) := by
  rw [store_get_ne _ _ (by decide)]
  exact dealLocalsAfterClaw_get_id I

theorem dealLocalsAfterCalls_get_bids (I : ExecutionEnv) :
    (((dealLocals I).insert "_clawRet" (collapseReturns [])).insert "_fluxRet"
        (collapseReturns [])).get? "bids" = none := by
  rw [store_get_ne _ _ (by decide)]
  exact dealLocalsAfterClaw_get_bids I

theorem flipperDealSourceBodyTicZero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (htic : bidTicWord (dealId I) σ I = ⟨0⟩) :
    let locals := dealLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dealTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0 dealFinishedGuard =
        .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_dealFinishedGuard_false_tic_zero (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) htic
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dealTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody, dealTransition, nonpayable, dealFinishedGuard, checkedExternalCallStmts,
    locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperDealSourceBodyNotFinished {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hticNe : bidTicWord (dealId I) σ I ≠ ⟨0⟩)
    (hticGe : (UInt256.ofNat I.header.timestamp).toNat ≤
      (bidTicWord (dealId I) σ I).toNat)
    (hendGe : (UInt256.ofNat I.header.timestamp).toNat ≤
      (bidEndWord (dealId I) σ I).toNat) :
    let locals := dealLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dealTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0 dealFinishedGuard =
        .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_dealFinishedGuard_false_not_expired (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        hticNe hticGe hendGe
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dealTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody, dealTransition, nonpayable, dealFinishedGuard, checkedExternalCallStmts,
    locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperDealSourceBodyCatNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hfinished :
      evalExpr? config { contract := contract, locals := dealLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) dealFinishedGuard =
          .ok (.bool true))
    (hnoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := dealLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dealTransition.body .reverted := by
  intro locals evm0
  have hcat : evalExpr? config { contract := contract, locals := locals } evm0 (.storage catRef) =
      .ok (.address (flipperCatAddress evm0.accountMap evm0.executionEnv)) := by
    simpa [locals] using evalExpr_dealCat (evm := evm0)
  have hguardCat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) = .ok (.bool false) := by
    simpa [evm0, initState, flipperCatAddress] using
      evalExpr_flipperCatCodeGuard_false_ofLocals (evm := evm0) (locals := locals) hcat
        hnoCode
  have hcallBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode (cfg := config) (C := contract) (evm := evm0)
        (locals := locals) (receiver := .storage catRef) (retVar := "_clawRet")
        (name := "claw") (sendVal := 0)
        (args := [.storage (bidsF (.var "id") "tab")]) hguardCat
  have hcallFull :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet" ++
        (
        checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "lot")] "_fluxRet" ++
        [ .delete (bidRef (.var "id")) ]))
        .reverted := by
    exact execBlock_append_term
      (cfg := config)
      (s2 :=
        checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "lot")] "_fluxRet" ++
        [ .delete (bidRef (.var "id")) ])
      hcallBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dealTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa [locals, evm0] using hfinished
    simpa [dealTransition, checkedExternalCallStmts, List.append_assoc] using hcallFull
  simpa [ExecTransitionBody, dealTransition, nonpayable, dealFinishedGuard, checkedExternalCallStmts,
    locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperDealSourceBodyCatCallFailure {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat : EVM.State} {outCat : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hfinished :
      evalExpr? config { contract := contract, locals := dealLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) dealFinishedGuard =
          .ok (.bool true))
    (hcatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallCat :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperCatAddress σ I)) "claw" 0
        (dealClawArgVals (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
        (false, evmCat, outCat) true) :
    let locals := dealLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dealTransition.body .reverted := by
  intro locals evm0
  have hcat : evalExpr? config { contract := contract, locals := locals } evm0 (.storage catRef) =
      .ok (.address (flipperCatAddress evm0.accountMap evm0.executionEnv)) := by
    simpa [locals] using evalExpr_dealCat (evm := evm0)
  have hguardCat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [evm0, initState, flipperCatAddress] using
      evalExpr_flipperCatCodeGuard_true_ofLocals (evm := evm0) (locals := locals) hcat
        hcatCode
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0
        [.storage (bidsF (.var "id") "tab")] = .ok (dealClawArgVals evm0) := by
    simpa [locals] using evalExprs_dealClawArgs (evm := evm0)
  have hcallCat' :
      typedCallViaEVM config evm0
        (EVM.address (flipperCatAddress evm0.accountMap evm0.executionEnv)) "claw" 0
        (dealClawArgVals evm0) (false, evmCat, outCat) true := by
    simpa [evm0, initState, flipperCatAddress] using hcallCat
  have hcallBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmCat) (locals := locals) (receiver := .storage catRef)
        (retVar := "_clawRet") (name := "claw")
        (target := flipperCatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [.storage (bidsF (.var "id") "tab")])
        (argVals := dealClawArgVals evm0) (out := outCat) (perm := true)
        hguardCat hcat hargs hcallCat'
  have hcallFull :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet" ++
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "lot")] "_fluxRet" ++
        [ .delete (bidRef (.var "id")) ]))
        .reverted := by
    exact execBlock_append_term
      (cfg := config)
      (s2 :=
        checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "lot")] "_fluxRet" ++
        [ .delete (bidRef (.var "id")) ])
      hcallBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dealTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa [locals, evm0] using hfinished
    simpa [dealTransition, checkedExternalCallStmts, List.append_assoc] using hcallFull
  simpa [ExecTransitionBody, dealTransition, nonpayable, dealFinishedGuard, checkedExternalCallStmts,
    locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperDealSourceBodySuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat evmVat : EVM.State} {outCat outVat : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hfinished :
      evalExpr? config { contract := contract, locals := dealLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) dealFinishedGuard =
          .ok (.bool true))
    (hcatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallCat :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperCatAddress σ I)) "claw" 0
        (dealClawArgVals (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
        (true, evmCat, outCat) true)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmCat.lookupAccount (flipperVatAddress evmCat.accountMap evmCat.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM config evmCat
        (EVM.address (flipperVatAddress evmCat.accountMap evmCat.executionEnv)) "flux" 0
        (dealFluxArgValsOf evmCat (dealId I)) (true, evmVat, outVat) true) :
    let locals := dealLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let locals1 := (dealLocals I).insert "_clawRet" (collapseReturns [])
    let locals2 := locals1.insert "_fluxRet" (collapseReturns [])
    let evmDeleted := bidDeletedEVM evmVat (dealId I)
    ExecTransitionBody config contract evm0 locals dealTransition.body
      (.returned { contract := contract, locals := locals2 } evmDeleted none) := by
  intro locals evm0 locals1 locals2 evmDeleted
  have hcat : evalExpr? config { contract := contract, locals := locals } evm0 (.storage catRef) =
      .ok (.address (flipperCatAddress evm0.accountMap evm0.executionEnv)) := by
    simpa [locals] using evalExpr_dealCat (evm := evm0)
  have hguardCat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [evm0, initState, flipperCatAddress] using
      evalExpr_flipperCatCodeGuard_true_ofLocals (evm := evm0) (locals := locals) hcat
        hcatCode
  have hargsCat :
      evalExprs? config { contract := contract, locals := locals } evm0
        [.storage (bidsF (.var "id") "tab")] = .ok (dealClawArgVals evm0) := by
    simpa [locals] using evalExprs_dealClawArgs (evm := evm0)
  have hcallCat' :
      typedCallViaEVM config evm0
        (EVM.address (flipperCatAddress evm0.accountMap evm0.executionEnv)) "claw" 0
        (dealClawArgVals evm0) (true, evmCat, outCat) true := by
    simpa [evm0, initState, flipperCatAddress] using hcallCat
  have hdecCat : config.externalABI.decode? "claw" outCat = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet")
        (.ok { contract := contract, locals := locals1 } evmCat) := by
    simpa [checkedExternalCallStmts, locals1, locals] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmCat) (locals := locals) (receiver := .storage catRef)
        (retVar := "_clawRet") (name := "claw")
        (target := flipperCatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [.storage (bidsF (.var "id") "tab")])
        (argVals := dealClawArgVals evm0) (out := outCat) (perm := true) (value := [])
        hguardCat hcat hargsCat hcallCat' hdecCat
  have hvat : evalExpr? config { contract := contract, locals := locals1 } evmCat
      (.storage vatRef) =
        .ok (.address (flipperVatAddress evmCat.accountMap evmCat.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals
      (by simpa [locals1] using dealLocalsAfterClaw_get_vat I)
  have hguardVat :
      evalExpr? config { contract := contract, locals := locals1 } evmCat
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_flipperVatCodeGuard_true_ofLocals hvat hvatCode
  have hargsVat :
      evalExprs? config { contract := contract, locals := locals1 } evmCat
        [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "lot")] =
        .ok (dealFluxArgValsOf evmCat (dealId I)) := by
    exact evalExprs_dealFluxArgs_ofLocals
      (by simpa [locals1] using dealLocalsAfterClaw_get_id I)
      (by simpa [locals1] using dealLocalsAfterClaw_get_bids I)
      (by simpa [locals1] using dealLocalsAfterClaw_get_ilk I)
  have hdecVat : config.externalABI.decode? "flux" outVat = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hvatBlock :
      ExecBlock config { contract := contract, locals := locals1 } evmCat
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "lot")] "_fluxRet")
        (.ok { contract := contract, locals := locals2 } evmVat) := by
    simpa [checkedExternalCallStmts, locals2, locals1] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evmCat)
        (evm' := evmVat) (locals := locals1) (receiver := .storage vatRef)
        (retVar := "_fluxRet") (name := "flux")
        (target := flipperVatAddress evmCat.accountMap evmCat.executionEnv) (sendVal := 0)
        (args := [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "lot")])
        (argVals := dealFluxArgValsOf evmCat (dealId I)) (out := outVat) (perm := true)
        (value := []) hguardVat hvat hargsVat hcallVat hdecVat
  have hdelete :
      ExecBlock config { contract := contract, locals := locals2 } evmVat
        [ .delete (bidRef (.var "id")) ]
        (.ok { contract := contract, locals := locals2 } evmDeleted) := by
    exact ExecBlock.consNormal
      (ExecStmt.delete (by
        simpa [evmDeleted, locals2] using
          deleteStorage_bidRef_of_get_id (evm := evmVat) (id := dealId I)
            (dealLocalsAfterCalls_get_id I) (dealLocalsAfterCalls_get_bids I)))
      ExecBlock.nil
  have htail :
      ExecBlock config { contract := contract, locals := locals1 } evmCat
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "lot")] "_fluxRet" ++
        [ .delete (bidRef (.var "id")) ])
        (.ok { contract := contract, locals := locals2 } evmDeleted) := by
    exact execBlock_append hvatBlock hdelete
  have hcalls :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet" ++
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "lot")] "_fluxRet" ++
        [ .delete (bidRef (.var "id")) ]))
        (.ok { contract := contract, locals := locals2 } evmDeleted) := by
    exact execBlock_append hcatBlock htail
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dealTransition.body
        (.ok { contract := contract, locals := locals2 } evmDeleted) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa [locals, evm0] using hfinished
    simpa [dealTransition, checkedExternalCallStmts, List.append_assoc] using hcalls
  simpa [ExecTransitionBody, dealTransition, nonpayable, dealFinishedGuard, checkedExternalCallStmts,
    locals, evm0, locals1, locals2, evmDeleted] using ExecFuncBody.execBlockOK hblock

theorem flipperDealSourceBodyVatNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat : EVM.State} {outCat : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hfinished :
      evalExpr? config { contract := contract, locals := dealLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) dealFinishedGuard =
          .ok (.bool true))
    (hcatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallCat :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperCatAddress σ I)) "claw" 0
        (dealClawArgVals (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
        (true, evmCat, outCat) true)
    (hvatNoCode :
      (UInt256.ofNat
        ((evmCat.lookupAccount (flipperVatAddress evmCat.accountMap evmCat.executionEnv)).option
          0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := dealLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let locals1 := (dealLocals I).insert "_clawRet" (collapseReturns [])
    ExecTransitionBody config contract evm0 locals dealTransition.body .reverted := by
  intro locals evm0 locals1
  have hcat : evalExpr? config { contract := contract, locals := locals } evm0 (.storage catRef) =
      .ok (.address (flipperCatAddress evm0.accountMap evm0.executionEnv)) := by
    simpa [locals] using evalExpr_dealCat (evm := evm0)
  have hguardCat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [evm0, initState, flipperCatAddress] using
      evalExpr_flipperCatCodeGuard_true_ofLocals (evm := evm0) (locals := locals) hcat
        hcatCode
  have hargsCat :
      evalExprs? config { contract := contract, locals := locals } evm0
        [.storage (bidsF (.var "id") "tab")] = .ok (dealClawArgVals evm0) := by
    simpa [locals] using evalExprs_dealClawArgs (evm := evm0)
  have hcallCat' :
      typedCallViaEVM config evm0
        (EVM.address (flipperCatAddress evm0.accountMap evm0.executionEnv)) "claw" 0
        (dealClawArgVals evm0) (true, evmCat, outCat) true := by
    simpa [evm0, initState, flipperCatAddress] using hcallCat
  have hdecCat : config.externalABI.decode? "claw" outCat = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet")
        (.ok { contract := contract, locals := locals1 } evmCat) := by
    simpa [checkedExternalCallStmts, locals1, locals] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmCat) (locals := locals) (receiver := .storage catRef)
        (retVar := "_clawRet") (name := "claw")
        (target := flipperCatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [.storage (bidsF (.var "id") "tab")])
        (argVals := dealClawArgVals evm0) (out := outCat) (perm := true) (value := [])
        hguardCat hcat hargsCat hcallCat' hdecCat
  have hvat : evalExpr? config { contract := contract, locals := locals1 } evmCat
      (.storage vatRef) =
        .ok (.address (flipperVatAddress evmCat.accountMap evmCat.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals
      (by simpa [locals1] using dealLocalsAfterClaw_get_vat I)
  have hguardVat :
      evalExpr? config { contract := contract, locals := locals1 } evmCat
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_flipperVatCodeGuard_false_ofLocals hvat hvatNoCode
  have hvatBlock :
      ExecBlock config { contract := contract, locals := locals1 } evmCat
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "lot")] "_fluxRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode (cfg := config) (C := contract) (evm := evmCat)
        (locals := locals1) (receiver := .storage vatRef) (retVar := "_fluxRet")
        (name := "flux") (sendVal := 0)
        (args := [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "lot")]) hguardVat
  have htail :
      ExecBlock config { contract := contract, locals := locals1 } evmCat
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "lot")] "_fluxRet" ++
        [ .delete (bidRef (.var "id")) ])
        .reverted := by
    exact execBlock_append_term (s2 := [ .delete (bidRef (.var "id")) ])
      hvatBlock (by intro f' e' h; cases h)
  have hcalls :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet" ++
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "lot")] "_fluxRet" ++
        [ .delete (bidRef (.var "id")) ]))
        .reverted := by
    exact execBlock_append hcatBlock htail
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dealTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa [locals, evm0] using hfinished
    simpa [dealTransition, checkedExternalCallStmts, List.append_assoc] using hcalls
  simpa [ExecTransitionBody, dealTransition, nonpayable, dealFinishedGuard, checkedExternalCallStmts,
    locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperDealSourceBodyVatCallFailure {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat evmVat : EVM.State} {outCat outVat : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hfinished :
      evalExpr? config { contract := contract, locals := dealLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) dealFinishedGuard =
          .ok (.bool true))
    (hcatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallCat :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperCatAddress σ I)) "claw" 0
        (dealClawArgVals (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
        (true, evmCat, outCat) true)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmCat.lookupAccount (flipperVatAddress evmCat.accountMap evmCat.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM config evmCat
        (EVM.address (flipperVatAddress evmCat.accountMap evmCat.executionEnv)) "flux" 0
        (dealFluxArgValsOf evmCat (dealId I)) (false, evmVat, outVat) true) :
    let locals := dealLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let locals1 := (dealLocals I).insert "_clawRet" (collapseReturns [])
    ExecTransitionBody config contract evm0 locals dealTransition.body .reverted := by
  intro locals evm0 locals1
  have hcat : evalExpr? config { contract := contract, locals := locals } evm0 (.storage catRef) =
      .ok (.address (flipperCatAddress evm0.accountMap evm0.executionEnv)) := by
    simpa [locals] using evalExpr_dealCat (evm := evm0)
  have hguardCat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [evm0, initState, flipperCatAddress] using
      evalExpr_flipperCatCodeGuard_true_ofLocals (evm := evm0) (locals := locals) hcat
        hcatCode
  have hargsCat :
      evalExprs? config { contract := contract, locals := locals } evm0
        [.storage (bidsF (.var "id") "tab")] = .ok (dealClawArgVals evm0) := by
    simpa [locals] using evalExprs_dealClawArgs (evm := evm0)
  have hcallCat' :
      typedCallViaEVM config evm0
        (EVM.address (flipperCatAddress evm0.accountMap evm0.executionEnv)) "claw" 0
        (dealClawArgVals evm0) (true, evmCat, outCat) true := by
    simpa [evm0, initState, flipperCatAddress] using hcallCat
  have hdecCat : config.externalABI.decode? "claw" outCat = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet")
        (.ok { contract := contract, locals := locals1 } evmCat) := by
    simpa [checkedExternalCallStmts, locals1, locals] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmCat) (locals := locals) (receiver := .storage catRef)
        (retVar := "_clawRet") (name := "claw")
        (target := flipperCatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [.storage (bidsF (.var "id") "tab")])
        (argVals := dealClawArgVals evm0) (out := outCat) (perm := true) (value := [])
        hguardCat hcat hargsCat hcallCat' hdecCat
  have hvat : evalExpr? config { contract := contract, locals := locals1 } evmCat
      (.storage vatRef) =
        .ok (.address (flipperVatAddress evmCat.accountMap evmCat.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals
      (by simpa [locals1] using dealLocalsAfterClaw_get_vat I)
  have hguardVat :
      evalExpr? config { contract := contract, locals := locals1 } evmCat
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_flipperVatCodeGuard_true_ofLocals hvat hvatCode
  have hargsVat :
      evalExprs? config { contract := contract, locals := locals1 } evmCat
        [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "lot")] =
        .ok (dealFluxArgValsOf evmCat (dealId I)) := by
    exact evalExprs_dealFluxArgs_ofLocals
      (by simpa [locals1] using dealLocalsAfterClaw_get_id I)
      (by simpa [locals1] using dealLocalsAfterClaw_get_bids I)
      (by simpa [locals1] using dealLocalsAfterClaw_get_ilk I)
  have hvatBlock :
      ExecBlock config { contract := contract, locals := locals1 } evmCat
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "lot")] "_fluxRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure (cfg := config) (C := contract) (evm := evmCat)
        (evm' := evmVat) (locals := locals1) (receiver := .storage vatRef)
        (retVar := "_fluxRet") (name := "flux")
        (target := flipperVatAddress evmCat.accountMap evmCat.executionEnv) (sendVal := 0)
        (args := [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "lot")])
        (argVals := dealFluxArgValsOf evmCat (dealId I)) (out := outVat) (perm := true)
        hguardVat hvat hargsVat hcallVat
  have htail :
      ExecBlock config { contract := contract, locals := locals1 } evmCat
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "lot")] "_fluxRet" ++
        [ .delete (bidRef (.var "id")) ])
        .reverted := by
    exact execBlock_append_term (s2 := [ .delete (bidRef (.var "id")) ])
      hvatBlock (by intro f' e' h; cases h)
  have hcalls :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet" ++
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "lot")] "_fluxRet" ++
        [ .delete (bidRef (.var "id")) ]))
        .reverted := by
    exact execBlock_append hcatBlock htail
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dealTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa [locals, evm0] using hfinished
    simpa [dealTransition, checkedExternalCallStmts, List.append_assoc] using hcalls
  simpa [ExecTransitionBody, dealTransition, nonpayable, dealFinishedGuard, checkedExternalCallStmts,
    locals, evm0] using ExecFuncBody.execBlockRevert hblock

end Benchmarks.Dss.Flipper
